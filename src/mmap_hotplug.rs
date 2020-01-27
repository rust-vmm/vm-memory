// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! A wrapper over the `GuestMemoryMmap` struct to support memory hotplug.
//!
//! With the `backend-mmap-hotplug` feature enabled, simply replacing GuestMemoryMmap
//! with GuestMemoryMmapAtomic will enable support of memory hotplug. To support memory
//! hotplug, guest memory clients also need to use GuestMemory::snapshot() to get a stable
//! snapshot of guest memory.

extern crate arc_swap;

use arc_swap::{ArcSwap, Guard};
use std::borrow::Borrow;
use std::ops::Deref;
use std::result;
use std::sync::{Arc, Mutex};

use crate::{
    Error, FileOffset, GuestAddress, GuestMemory, GuestMemoryGuard, GuestMemoryMmap,
    GuestRegionMmap,
};

#[derive(Debug)]
enum State {
    Outer((Arc<ArcSwap<GuestMemoryMmap>>, Mutex<()>)),
    Guard(Guard<'static, Arc<GuestMemoryMmap>>),
    Inner(Arc<GuestMemoryMmap>),
}

/// Tracks memory regions allocated/mapped for the guest in the current process.
///
/// This implementation uses ArcSwap to provide RCU-like lock strategy to support memory hotplug.
/// The implementation is really a little over complex, hope that it deserves the complexity in
/// case of performance.
#[derive(Debug)]
pub struct GuestMemoryMmapAtomic {
    inner: State,
}

impl GuestMemoryMmapAtomic {
    /// Creates a container and allocates anonymous memory for guest memory regions.
    /// Valid memory regions are specified as a slice of (Address, Size) tuples sorted by Address.
    pub fn new(ranges: &[(GuestAddress, usize)]) -> result::Result<Self, Error> {
        let mmap = GuestMemoryMmap::with_files(ranges.iter().map(|r| (r.0, r.1, None)))?;
        Self::from_mmap(mmap)
    }

    /// Creates a container and allocates anonymous memory for guest memory regions.
    /// Valid memory regions are specified as a sequence of (Address, Size, Option<FileOffset>)
    /// tuples sorted by Address.
    pub fn with_files<A, T>(ranges: T) -> result::Result<Self, Error>
    where
        A: Borrow<(GuestAddress, usize, Option<FileOffset>)>,
        T: IntoIterator<Item = A>,
    {
        let mmap = GuestMemoryMmap::with_files(ranges)?;
        Self::from_mmap(mmap)
    }

    /// Creates a new `GuestMemoryMmap` from a vector of regions.
    ///
    /// # Arguments
    ///
    /// * `regions` - The vector of regions.
    ///               The regions shouldn't overlap and they should be sorted
    ///               by the starting address.
    pub fn from_regions(mut regions: Vec<GuestRegionMmap>) -> result::Result<Self, Error> {
        Self::from_arc_regions(regions.drain(..).map(Arc::new).collect())
    }

    /// Creates a new `GuestMemoryMmap` from a vector of Arc regions.
    ///
    /// Similar to the constructor from_regions() as it returns a
    /// GuestMemoryMmap. The need for this constructor is to provide a way for
    /// consumer of this API to create a new GuestMemoryMmap based on existing
    /// regions coming from an existing GuestMemoryMmap instance.
    ///
    /// # Arguments
    ///
    /// * `regions` - The vector of Arc regions.
    ///               The regions shouldn't overlap and they should be sorted
    ///               by the starting address.
    pub fn from_arc_regions(regions: Vec<Arc<GuestRegionMmap>>) -> result::Result<Self, Error> {
        let mmap = GuestMemoryMmap::from_arc_regions(regions)?;
        Self::from_mmap(mmap)
    }

    /// Insert an region into the `GuestMemoryMmap` object.
    ///
    /// Note: this method is not multi-thread safe. If called at runtime to support memory hot-add,
    /// the caller needs to protect it from concurrent access from both reader and writer side.
    ///
    /// # Arguments
    /// * `region`: the memory region to insert into the guest memory object.
    pub fn insert_region(&mut self, region: Arc<GuestRegionMmap>) -> result::Result<(), Error> {
        let inner = match self.inner {
            State::Outer(ref obj) => obj,
            _ => panic!("GuestRegionMmapAtomic::insert_region must be called from object itself"),
        };
        let _lock = inner
            .1
            .lock()
            .expect("memory hotplug lock has been poisoned");

        let curr = inner.0.load().regions.clone();
        let mut mmap = GuestMemoryMmap::from_arc_regions(curr)?;
        mmap.insert_region(region)?;
        let _old = inner.0.swap(Arc::new(mmap));

        Ok(())
    }

    fn from_mmap(mmap: GuestMemoryMmap) -> result::Result<Self, Error> {
        Ok(GuestMemoryMmapAtomic {
            inner: State::Outer((Arc::new(ArcSwap::new(Arc::new(mmap))), Mutex::new(()))),
        })
    }
}

impl GuestMemory for GuestMemoryMmapAtomic {
    type R = GuestRegionMmap;

    fn snapshot(&self) -> GuestMemoryGuard<'_, Self>
    where
        Self: std::marker::Sized,
    {
        let inner = match self.inner {
            State::Outer(ref obj) => State::Guard(obj.0.load()),
            State::Guard(ref guard) => State::Inner(guard.deref().clone()),
            State::Inner(ref obj) => State::Inner(obj.clone()),
        };
        GuestMemoryGuard::Valued(GuestMemoryMmapAtomic { inner })
    }

    fn num_regions(&self) -> usize {
        match self.inner {
            State::Outer(ref _obj) => {
                panic!("please use GuestMemoryMmapAtomic::snapshot().num_regions()")
            }
            State::Guard(ref guard) => guard.num_regions(),
            State::Inner(ref obj) => obj.num_regions(),
        }
    }

    fn find_region(&self, addr: GuestAddress) -> Option<&Self::R> {
        match self.inner {
            State::Outer(ref _obj) => {
                panic!("please use GuestMemoryMmapAtomic::snapshot().find_region(addr)")
            }
            State::Guard(ref guard) => guard.find_region(addr),
            State::Inner(ref obj) => obj.find_region(addr),
        }
    }

    fn with_regions<F, E>(&self, cb: F) -> result::Result<(), E>
    where
        F: Fn(usize, &Self::R) -> result::Result<(), E>,
    {
        match self.inner {
            State::Outer(ref o) => o.0.load().with_regions(cb),
            State::Guard(ref g) => g.with_regions(cb),
            State::Inner(ref i) => i.with_regions(cb),
        }
    }

    fn with_regions_mut<F, E>(&self, cb: F) -> result::Result<(), E>
    where
        F: FnMut(usize, &Self::R) -> result::Result<(), E>,
    {
        match self.inner {
            State::Outer(ref o) => o.0.load().with_regions_mut(cb),
            State::Guard(ref g) => g.with_regions_mut(cb),
            State::Inner(ref i) => i.with_regions_mut(cb),
        }
    }

    fn map_and_fold<F, G, T>(&self, init: T, mapf: F, foldf: G) -> T
    where
        F: Fn((usize, &Self::R)) -> T,
        G: Fn(T, T) -> T,
    {
        match self.inner {
            State::Outer(ref o) => o.0.load().map_and_fold(init, mapf, foldf),
            State::Guard(ref g) => g.map_and_fold(init, mapf, foldf),
            State::Inner(ref i) => i.map_and_fold(init, mapf, foldf),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{guest_memory, GuestMemoryRegion, GuestUsize, MmapRegion};

    #[test]
    fn test_hotplug_basic() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let mut iterated_regions = Vec::new();
        let gm = GuestMemoryMmapAtomic::new(&regions).unwrap();

        let res: guest_memory::Result<()> = gm.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestUsize);
            Ok(())
        });
        assert!(res.is_ok());
        let res: guest_memory::Result<()> = gm.with_regions_mut(|_, region| {
            iterated_regions.push((region.start_addr(), region.len() as usize));
            Ok(())
        });
        assert!(res.is_ok());
        assert_eq!(regions, iterated_regions);

        assert!(regions
            .iter()
            .map(|x| (x.0, x.1))
            .eq(iterated_regions.iter().map(|x| *x)));
    }

    #[test]
    fn test_hotplug_snapshot() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let mut iterated_regions = Vec::new();
        let gm = GuestMemoryMmapAtomic::new(&regions).unwrap();
        let snapshot = gm.snapshot();

        let res: guest_memory::Result<()> = snapshot.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestUsize);
            Ok(())
        });
        assert!(res.is_ok());
        let res: guest_memory::Result<()> = snapshot.with_regions_mut(|_, region| {
            iterated_regions.push((region.start_addr(), region.len() as usize));
            Ok(())
        });
        assert!(res.is_ok());
        assert_eq!(regions, iterated_regions);
        assert_eq!(snapshot.num_regions(), 2);
        assert!(snapshot.find_region(GuestAddress(0x1000)).is_some());
        assert!(snapshot.find_region(GuestAddress(0x10000)).is_none());

        assert!(regions
            .iter()
            .map(|x| (x.0, x.1))
            .eq(iterated_regions.iter().map(|x| *x)));

        let snapshot2 = snapshot.snapshot();
        let res: guest_memory::Result<()> = snapshot2.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestUsize);
            Ok(())
        });
        assert!(res.is_ok());
        let res: guest_memory::Result<()> = snapshot2.with_regions_mut(|_, _| Ok(()));
        assert!(res.is_ok());
        assert_eq!(snapshot2.num_regions(), 2);
        assert!(snapshot2.find_region(GuestAddress(0x1000)).is_some());
        assert!(snapshot2.find_region(GuestAddress(0x10000)).is_none());

        assert!(regions
            .iter()
            .map(|x| (x.0, x.1))
            .eq(iterated_regions.iter().map(|x| *x)));

        let snapshot3 = snapshot2.snapshot();
        let res: guest_memory::Result<()> = snapshot3.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestUsize);
            Ok(())
        });
        assert!(res.is_ok());
        let res: guest_memory::Result<()> = snapshot3.with_regions_mut(|_, _| Ok(()));
        assert!(res.is_ok());
        assert_eq!(snapshot3.num_regions(), 2);
        assert!(snapshot3.find_region(GuestAddress(0x1000)).is_some());
        assert!(snapshot3.find_region(GuestAddress(0x10000)).is_none());
    }

    #[should_panic]
    #[test]
    fn test_num_regions_panic() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let gm = GuestMemoryMmapAtomic::new(&regions).unwrap();
        let _ = gm.num_regions();
    }

    #[should_panic]
    #[test]
    fn test_find_region_panic() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let gm = GuestMemoryMmapAtomic::new(&regions).unwrap();
        let _ = gm.find_region(GuestAddress(0x1001));
    }

    #[test]
    fn test_mmap_memory_hotplug() {
        let region_size = 0x1000;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x10_0000), region_size),
        ];
        let mut gm = GuestMemoryMmapAtomic::new(&regions).unwrap();
        let snapshot_orig = gm.snapshot();
        assert_eq!(snapshot_orig.num_regions(), 2);

        let mmap =
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0x8000)).unwrap();
        gm.insert_region(Arc::new(mmap)).unwrap();
        let mmap =
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0x4000)).unwrap();
        gm.insert_region(Arc::new(mmap)).unwrap();
        let mmap =
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0xc000)).unwrap();
        gm.insert_region(Arc::new(mmap)).unwrap();
        let mmap =
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0xc000)).unwrap();
        gm.insert_region(Arc::new(mmap)).unwrap_err();

        let snapshot = gm.snapshot();
        //assert_eq!(snapshot_orig.num_regions(), 2);
        assert_eq!(snapshot.num_regions(), 5);

        let inner = match snapshot.inner {
            State::Guard(ref g) => g,
            _ => panic!("invalid snapshot state"),
        };
        assert_eq!(inner.regions[0].start_addr(), GuestAddress(0x0000));
        assert_eq!(inner.regions[1].start_addr(), GuestAddress(0x4000));
        assert_eq!(inner.regions[2].start_addr(), GuestAddress(0x8000));
        assert_eq!(inner.regions[3].start_addr(), GuestAddress(0xc000));
        assert_eq!(inner.regions[4].start_addr(), GuestAddress(0x10_0000));
    }
}
