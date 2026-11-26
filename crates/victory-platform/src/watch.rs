//! A write watch for diagnostics (`VICTORY_TRACE_DESCRIPTORS=sites`, #43): which title
//! instructions store into a set of watched ranges, and how often.
//!
//! [`watch`] publishes the ranges and makes their pages read-only. The loader's signal handler
//! hands every write fault to [`on_write_fault`] first, whoever wrote: a fault in a watched page
//! makes that page writable again, and the store runs again when the handler returns. It is
//! counted as a site only when the writing instruction lies in the title image ([`set_image`]) and
//! the address in a watched range itself, so host writes (the device's view calls) and title
//! stores that only share the page go on unseen. The next [`watch`] closes the pages again, so
//! what is counted is the first write to each page per interval, not every store.
//!
//! Signal safety: the fault path reads atomics, calls `mprotect` and adds to a fixed table
//! ([`Sites`], open addressing, no allocation or lock); a full table counts the sites it could not
//! hold.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

unsafe extern "C" {
    fn mprotect(addr: *mut std::ffi::c_void, len: usize, prot: i32) -> i32;
}
const READ: i32 = 1;
const READ_WRITE: i32 = 3;

/// `mprotect`, which only returns a status (nothing to allocate in a signal handler).
///
/// # Safety
/// The pages are the caller's.
unsafe fn set(at: usize, len: usize, prot: i32) -> bool {
    // SAFETY: forwarded from the caller.
    unsafe { mprotect(at as *mut _, len, prot) == 0 }
}

/// The most ranges watched at once (more are left out).
pub const RANGES: usize = 64;
/// The sites the table holds.
pub const SITES: usize = 4096;

/// Store sites (image offsets, never 0 here: offset 0 is the image header) and their counts.
pub struct Sites<const N: usize> {
    keys: [AtomicU64; N],
    counts: [AtomicU64; N],
    overflow: AtomicU64,
}

impl<const N: usize> Default for Sites<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Sites<N> {
    pub const fn new() -> Self {
        Sites {
            keys: [const { AtomicU64::new(0) }; N],
            counts: [const { AtomicU64::new(0) }; N],
            overflow: AtomicU64::new(0),
        }
    }

    /// One store from `site`. Signal safe.
    pub fn add(&self, site: u64) {
        let start = (site.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize % N;
        for i in 0..N {
            let k = (start + i) % N;
            let key = &self.keys[k];
            let found = match key.compare_exchange(0, site, Ordering::AcqRel, Ordering::Acquire) {
                Ok(_) => true,
                Err(other) => other == site,
            };
            if found {
                self.counts[k].fetch_add(1, Ordering::Relaxed);
                return;
            }
        }
        self.overflow.fetch_add(1, Ordering::Relaxed);
    }

    /// Every site and its count, most first (then by site).
    pub fn sorted(&self) -> Vec<(u64, u64)> {
        let mut out: Vec<(u64, u64)> = (0..N)
            .filter_map(|k| {
                let site = self.keys[k].load(Ordering::Acquire);
                (site != 0).then(|| (site, self.counts[k].load(Ordering::Relaxed)))
            })
            .collect();
        out.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        out
    }

    /// Stores from sites the full table could not hold.
    pub fn overflow(&self) -> u64 {
        self.overflow.load(Ordering::Relaxed)
    }
}

/// What a write fault at `addr` from the instruction at `rip` is to the watch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fault {
    /// Not in a watched page: someone else's fault.
    NotOurs,
    /// In a watched page: open the page (its first byte given) and run the store again.
    Open { page: usize },
    /// The same, and a title store into a watched range: count `site` (an image offset).
    Count { page: usize, site: u64 },
}

/// The rule, for ranges `[start, end)`, the title image `[base, end)` and pages of `page` bytes.
pub fn classify(
    addr: usize,
    rip: usize,
    ranges: impl IntoIterator<Item = (usize, usize)>,
    (image, image_end): (usize, usize),
    page: usize,
) -> Fault {
    let first = addr & !(page - 1);
    let mut open = false;
    for (start, end) in ranges {
        let pages = (start & !(page - 1))..(end.saturating_add(page - 1) & !(page - 1));
        if !pages.contains(&addr) {
            continue;
        }
        if (start..end).contains(&addr) && (image..image_end).contains(&rip) {
            return Fault::Count {
                page: first,
                site: (rip - image) as u64,
            };
        }
        open = true;
    }
    if open {
        Fault::Open { page: first }
    } else {
        Fault::NotOurs
    }
}

struct Ranges {
    starts: [AtomicUsize; RANGES],
    ends: [AtomicUsize; RANGES],
    len: AtomicUsize,
}

static WATCHED: Ranges = Ranges {
    starts: [const { AtomicUsize::new(0) }; RANGES],
    ends: [const { AtomicUsize::new(0) }; RANGES],
    len: AtomicUsize::new(0),
};
static IMAGE: [AtomicUsize; 2] = [AtomicUsize::new(0), AtomicUsize::new(0)];
static PAGE: AtomicUsize = AtomicUsize::new(0);
static SITES_SEEN: Sites<SITES> = Sites::new();

fn published() -> impl Iterator<Item = (usize, usize)> {
    let n = WATCHED.len.load(Ordering::Acquire);
    (0..n).map(|i| {
        (
            WATCHED.starts[i].load(Ordering::Relaxed),
            WATCHED.ends[i].load(Ordering::Relaxed),
        )
    })
}

/// The title image, whose instructions count as store sites (from the loader, at the start).
pub fn set_image(base: usize, len: usize) {
    IMAGE[0].store(base, Ordering::Relaxed);
    IMAGE[1].store(base.saturating_add(len), Ordering::Release);
}

/// Whether anything is watched: the signal handler's one check when the watch is off.
pub fn active() -> bool {
    WATCHED.len.load(Ordering::Relaxed) != 0
}

/// A write fault at `addr` from the instruction at `rip`, from the signal handler: true when it
/// was the watch's (the page is writable again and the store is to run again). Signal safe.
pub fn on_write_fault(addr: usize, rip: usize) -> bool {
    let page = PAGE.load(Ordering::Relaxed);
    if page == 0 || !active() {
        return false;
    }
    let image = (
        IMAGE[0].load(Ordering::Relaxed),
        IMAGE[1].load(Ordering::Acquire),
    );
    let at = match classify(addr, rip, published(), image, page) {
        Fault::NotOurs => return false,
        Fault::Open { page } => page,
        Fault::Count { page, site } => {
            SITES_SEEN.add(site);
            page
        }
    };
    // SAFETY: a page of a range the caller of `watch` owns; it only becomes writable again.
    unsafe { set(at, page, READ_WRITE) }
}

/// Watches `ranges` (each `[start, end)`, read-write memory of the caller's) until the next call:
/// publishes them, then makes their pages read-only. Pages of ranges no longer given are made
/// writable again; an empty list ends the watch.
pub fn watch(ranges: &[(usize, usize)]) {
    let page = crate::mem::page_size();
    PAGE.store(page, Ordering::Relaxed);
    let ranges = &ranges[..ranges.len().min(RANGES)];
    let pages = |(s, e): (usize, usize)| {
        let first = s & !(page - 1);
        (first, (e.saturating_add(page - 1) & !(page - 1)) - first)
    };
    let old: Vec<(usize, usize)> = published().collect();
    for &r in old.iter().filter(|r| !ranges.contains(r)) {
        let (at, len) = pages(r);
        // SAFETY: pages this watch made read-only; they only become writable again.
        unsafe { set(at, len, READ_WRITE) };
    }
    WATCHED.len.store(0, Ordering::Release);
    for (i, &(s, e)) in ranges.iter().enumerate() {
        WATCHED.starts[i].store(s, Ordering::Relaxed);
        WATCHED.ends[i].store(e, Ordering::Relaxed);
    }
    WATCHED.len.store(ranges.len(), Ordering::Release);
    for &r in ranges {
        let (at, len) = pages(r);
        // SAFETY: the caller's read-write memory; a write to it faults and reopens its page.
        unsafe { set(at, len, READ) };
    }
}

/// Every store site counted so far (image offsets), most first, and the stores the full table
/// could not hold.
pub fn sites() -> (Vec<(u64, u64)>, u64) {
    (SITES_SEEN.sorted(), SITES_SEEN.overflow())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sites_count_and_overflow() {
        let s = Sites::<4>::new();
        for site in [0x10, 0x20, 0x10, 0x30, 0x10, 0x20, 0x40] {
            s.add(site);
        }
        assert_eq!(s.sorted(), [(0x10, 3), (0x20, 2), (0x30, 1), (0x40, 1)]);
        assert_eq!(s.overflow(), 0);
        // Full: a fifth site is counted as overflow, the four keep counting.
        s.add(0x50);
        s.add(0x50);
        s.add(0x30);
        assert_eq!(s.overflow(), 2);
        assert_eq!(s.sorted()[2], (0x30, 2));
    }

    #[test]
    fn only_title_stores_into_a_range_count() {
        let page = 0x1000;
        let image = (0x1_4000_0000, 0x1_5000_0000);
        let ranges = [(0x10_0100, 0x10_0200), (0x20_0000, 0x20_2000)];
        let title = 0x1_4000_1234;
        // In a range, from the title: counted, its page opened.
        assert_eq!(
            classify(0x10_0180, title, ranges, image, page),
            Fault::Count {
                page: 0x10_0000,
                site: 0x1234
            }
        );
        // The same page outside the range, or a host instruction: opened only.
        assert_eq!(
            classify(0x10_0080, title, ranges, image, page),
            Fault::Open { page: 0x10_0000 }
        );
        assert_eq!(
            classify(0x10_0180, 0x7000_0000, ranges, image, page),
            Fault::Open { page: 0x10_0000 }
        );
        // A range's last page, and pages no range touches.
        assert_eq!(
            classify(0x20_1ff8, title, ranges, image, page),
            Fault::Count {
                page: 0x20_1000,
                site: 0x1234
            }
        );
        assert_eq!(
            classify(0x20_2000, title, ranges, image, page),
            Fault::NotOurs
        );
        assert_eq!(
            classify(0x10_1000, title, ranges, image, page),
            Fault::NotOurs
        );
        assert_eq!(classify(0x10_0180, title, [], image, page), Fault::NotOurs);
    }
}
