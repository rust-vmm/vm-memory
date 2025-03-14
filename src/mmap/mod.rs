// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! The default implementation for the [`GuestMemory`](trait.GuestMemory.html) trait.
//!
//! This implementation is mmap-ing the memory of the guest into the current process.

// re-export for backward compat, as the trait used to be defined in mmap.rs
pub use crate::bitmap::NewBitmap;

#[cfg(target_family = "unix")]
pub(super) mod unix;

#[cfg(all(feature = "xen", target_family = "unix"))]
pub(super) mod xen;

#[cfg(target_family = "windows")]
pub(super) mod windows;

#[cfg(all(not(feature = "xen"), target_family = "unix"))]
pub use unix::{Error as MmapRegionError, MmapRegion, MmapRegionBuilder};

#[cfg(all(feature = "xen", target_family = "unix"))]
pub use xen::{Error as MmapRegionError, MmapRange, MmapRegion, MmapXenFlags};

#[cfg(target_family = "windows")]
pub use std::io::Error as MmapRegionError;
#[cfg(target_family = "windows")]
pub use windows::MmapRegion;

#[cfg(test)]
pub(crate) mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]
    extern crate vmm_sys_util;

    use crate::bitmap::BS;
    use crate::{
        guest_memory, Address, Bytes, FileOffset, GuestAddress, GuestMemory, GuestMemoryError,
        GuestMemoryRegion, GuestMemoryRegionBytes, GuestUsize, MemoryRegionAddress, VolatileMemory,
        VolatileSlice,
    };

    use std::io::Write;
    use std::sync::Arc;
    #[cfg(feature = "rawfd")]
    use std::{fs::File, path::Path};
    use vmm_sys_util::tempfile::TempFile;

    use matches::assert_matches;

    macro_rules! any_backend {
        ($($(#[$attr:meta])* $backend: ident[$region: path]), *) => {
            #[derive(Debug)]
            pub enum AnyRegion {
                $(
                    $(#[$attr])* $backend($region)
                ),*
            }

            pub type AnyBackend = $crate::GuestRegionCollection<AnyRegion>;

            impl $crate::GuestMemoryRegion for AnyRegion {
                type B = ();

                fn len(&self) -> GuestUsize {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => $crate::GuestMemoryRegion::len(inner)),*
                    }
                }

                fn start_addr(&self) -> GuestAddress {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => inner.start_addr()),*
                    }
                }

                fn bitmap(&self) {}

                fn get_host_address(&self, addr: MemoryRegionAddress) -> guest_memory::Result<*mut u8> {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => inner.get_host_address(addr)),*
                    }
                }

                fn file_offset(&self) -> Option<&FileOffset> {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => inner.file_offset()),*
                    }
                }

                fn get_slice(&self, offset: MemoryRegionAddress, count: usize) -> guest_memory::Result<VolatileSlice<BS<Self::B>>> {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => $crate::GuestMemoryRegion::get_slice(inner, offset, count)),*
                    }
                }
            }

            impl GuestMemoryRegionBytes for AnyRegion {}
        };
    }

    any_backend! {
        #[cfg(all(windows, feature = "backend-mmap"))]
        Windows[crate::mmap::windows::GuestRegionWindows<()>],
        #[cfg(all(unix, feature = "backend-mmap"))]
        Mmap[crate::mmap::unix::GuestRegionMmap<()>],
        #[cfg(all(unix, feature = "backend-mmap", feature = "xen"))]
        Xen[crate::mmap::xen::MmapRegion]
    }

    // The cfgs make using vec![...] instead more unreadable, so suppress the lint here.
    #[allow(clippy::vec_init_then_push)]
    impl AnyRegion {
        fn all_with_file(addr: GuestAddress, size: usize, f_off: &FileOffset) -> Vec<AnyRegion> {
            let mut regions = Vec::new();
            #[cfg(all(windows, feature = "backend-mmap"))]
            regions.push(AnyRegion::Windows(
                crate::mmap::windows::GuestRegionWindows::new(
                    crate::mmap::windows::MmapRegion::from_file(f_off.clone(), size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap"))]
            regions.push(AnyRegion::Mmap(
                crate::mmap::unix::GuestRegionMmap::new(
                    crate::MmapRegion::from_file(f_off.clone(), size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap", feature = "xen"))]
            regions.push(AnyRegion::Xen(
                crate::MmapRegionXen::from_range(crate::MmapRange::new_unix(
                    size,
                    Some(f_off.clone()),
                    addr,
                ))
                .unwrap(),
            ));
            regions
        }

        fn all(addr: GuestAddress, size: usize, file: &Option<FileOffset>) -> Vec<AnyRegion> {
            let mut regions = if let Some(file) = file {
                Self::all_with_file(addr, size, file)
            } else {
                Vec::new()
            };
            #[cfg(all(windows, feature = "backend-mmap"))]
            regions.push(AnyRegion::Windows(
                crate::mmap::windows::GuestRegionWindows::new(
                    crate::mmap::windows::MmapRegion::new(size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap"))]
            regions.push(AnyRegion::Mmap(
                crate::mmap::unix::GuestRegionMmap::new(
                    crate::MmapRegion::new(size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap", feature = "xen"))]
            regions.push(AnyRegion::Xen(
                crate::MmapRegionXen::from_range(crate::MmapRange::new_unix(size, None, addr))
                    .unwrap(),
            ));
            regions
        }

        fn as_ptr(&self) -> *mut u8 {
            self.get_host_address(MemoryRegionAddress(0)).unwrap()
        }
    }

    fn transpose(striped: Vec<Vec<AnyRegion>>) -> Vec<AnyBackend> {
        assert!(!striped.is_empty(), "No test cases found!");

        let mut backends = (0..striped[0].len())
            .map(|_| AnyBackend::default())
            .collect::<Vec<_>>();
        for stripe in striped {
            backends
                .iter_mut()
                .zip(stripe)
                .for_each(|(backend, region)| {
                    *backend = backend.insert_region(Arc::new(region)).unwrap();
                });
        }
        backends
    }

    impl AnyBackend {
        fn all_with_file(regions: &[(GuestAddress, usize, FileOffset)]) -> Vec<AnyBackend> {
            let striped = regions
                .iter()
                .map(|(addr, size, file)| AnyRegion::all_with_file(*addr, *size, file))
                .collect::<Vec<_>>();

            transpose(striped)
        }

        pub(crate) fn all(
            regions: &[(GuestAddress, usize, Option<FileOffset>)],
        ) -> Vec<AnyBackend> {
            let striped = regions
                .iter()
                .map(|(addr, size, file)| AnyRegion::all(*addr, *size, file))
                .collect::<Vec<_>>();

            transpose(striped)
        }
    }

    #[test]
    fn basic_map() {
        for m in AnyRegion::all(GuestAddress(0), 1024, &None) {
            assert_eq!(1024, m.len());
        }
    }

    #[test]
    fn slice_addr() {
        for m in AnyRegion::all(GuestAddress(0), 5, &None) {
            let s = m.get_slice(MemoryRegionAddress(2), 3).unwrap();
            let guard = s.ptr_guard();
            assert_eq!(guard.as_ptr(), unsafe { m.as_ptr().offset(2) });
        }
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn mapped_file_read() {
        let mut f = TempFile::new().unwrap().into_file();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert!(f.write_all(sample_buf).is_ok());

        let file = FileOffset::new(f, 0);
        for mem_map in AnyRegion::all_with_file(GuestAddress(0), sample_buf.len(), &file) {
            let buf = &mut [0u8; 16];
            assert_eq!(
                mem_map.as_volatile_slice().unwrap().read(buf, 0).unwrap(),
                sample_buf.len()
            );
            assert_eq!(buf[0..sample_buf.len()], sample_buf[..]);
        }
    }

    #[test]
    fn test_to_region_addr() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x400).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x400).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        for guest_mem in AnyBackend::all(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ]) {
            assert!(guest_mem.to_region_addr(GuestAddress(0x600)).is_none());
            let (r0, addr0) = guest_mem.to_region_addr(GuestAddress(0x800)).unwrap();
            let (r1, addr1) = guest_mem.to_region_addr(GuestAddress(0xa00)).unwrap();
            assert_eq!(r0.as_ptr(), r1.as_ptr());
            assert_eq!(addr0, MemoryRegionAddress(0));
            assert_eq!(addr1, MemoryRegionAddress(0x200));
        }
    }

    #[test]
    fn test_get_host_address() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x400).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x400).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        for guest_mem in AnyBackend::all(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ]) {
            assert!(guest_mem.get_host_address(GuestAddress(0x600)).is_err());
            let ptr0 = guest_mem.get_host_address(GuestAddress(0x800)).unwrap();
            let ptr1 = guest_mem.get_host_address(GuestAddress(0xa00)).unwrap();
            assert_eq!(
                ptr0,
                guest_mem.find_region(GuestAddress(0x800)).unwrap().as_ptr()
            );
            assert_eq!(unsafe { ptr0.offset(0x200) }, ptr1);
        }
    }

    #[test]
    fn test_check_range() {
        let start_addr1 = GuestAddress(0);
        let start_addr2 = GuestAddress(0x800);
        let start_addr3 = GuestAddress(0xc00);
        for guest_mem in AnyBackend::all(&[
            (start_addr1, 0x400, None),
            (start_addr2, 0x400, None),
            (start_addr3, 0x400, None),
        ]) {
            assert!(guest_mem.check_range(start_addr1, 0x0));
            assert!(guest_mem.check_range(start_addr1, 0x200));
            assert!(guest_mem.check_range(start_addr1, 0x400));
            assert!(!guest_mem.check_range(start_addr1, 0xa00));
            assert!(guest_mem.check_range(start_addr2, 0x7ff));
            assert!(guest_mem.check_range(start_addr2, 0x800));
            assert!(!guest_mem.check_range(start_addr2, 0x801));
            assert!(!guest_mem.check_range(start_addr2, 0xc00));
            assert!(!guest_mem.check_range(start_addr1, usize::MAX));
        }
    }

    #[test]
    fn test_deref() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let start_addr = GuestAddress(0x0);
        for guest_mem in AnyBackend::all(&[(start_addr, 0x400, Some(FileOffset::new(f, 0)))]) {
            let sample_buf = &[1, 2, 3, 4, 5];

            assert_eq!(guest_mem.write(sample_buf, start_addr).unwrap(), 5);
            let slice = guest_mem
                .find_region(GuestAddress(0))
                .unwrap()
                .as_volatile_slice()
                .unwrap();

            let buf = &mut [0, 0, 0, 0, 0];
            assert_eq!(slice.read(buf, 0).unwrap(), 5);
            assert_eq!(buf, sample_buf);
        }
    }

    #[test]
    fn test_read_u64() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x1000).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x1000).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        let bad_addr = GuestAddress(0x2001);
        let bad_addr2 = GuestAddress(0x1ffc);
        let max_addr = GuestAddress(0x2000);

        for gm in AnyBackend::all(&[
            (start_addr1, 0x1000, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x1000, Some(FileOffset::new(f2, 0))),
        ]) {
            let val1: u64 = 0xaa55_aa55_aa55_aa55;
            let val2: u64 = 0x55aa_55aa_55aa_55aa;
            assert_matches!(
                gm.write_obj(val1, bad_addr).unwrap_err(),
                GuestMemoryError::InvalidGuestAddress(addr) if addr == bad_addr
            );
            assert_matches!(
                gm.write_obj(val1, bad_addr2).unwrap_err(),
                GuestMemoryError::PartialBuffer { expected, completed } if expected == size_of::<u64>() && completed == max_addr.checked_offset_from(bad_addr2).unwrap() as usize);

            gm.write_obj(val1, GuestAddress(0x500)).unwrap();
            gm.write_obj(val2, GuestAddress(0x1000 + 32)).unwrap();
            let num1: u64 = gm.read_obj(GuestAddress(0x500)).unwrap();
            let num2: u64 = gm.read_obj(GuestAddress(0x1000 + 32)).unwrap();
            assert_eq!(val1, num1);
            assert_eq!(val2, num2);
        }
    }

    #[test]
    fn write_and_read() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let mut start_addr = GuestAddress(0x1000);
        for gm in AnyBackend::all(&[(start_addr, 0x400, Some(FileOffset::new(f, 0)))]) {
            let sample_buf = &[1, 2, 3, 4, 5];

            assert_eq!(gm.write(sample_buf, start_addr).unwrap(), 5);

            let buf = &mut [0u8; 5];
            assert_eq!(gm.read(buf, start_addr).unwrap(), 5);
            assert_eq!(buf, sample_buf);

            start_addr = GuestAddress(0x13ff);
            assert_eq!(gm.write(sample_buf, start_addr).unwrap(), 1);
            assert_eq!(gm.read(buf, start_addr).unwrap(), 1);
            assert_eq!(buf[0], sample_buf[0]);
            start_addr = GuestAddress(0x1000);
        }
    }

    #[test]
    #[cfg(feature = "rawfd")]
    #[cfg(not(miri))]
    fn read_to_and_write_from_mem() {
        use std::mem;

        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        for gm in AnyBackend::all(&[(GuestAddress(0x1000), 0x400, Some(FileOffset::new(f, 0)))]) {
            let addr = GuestAddress(0x1010);
            let mut file = File::open(Path::new("/dev/zero")).unwrap();
            gm.write_obj(!0u32, addr).unwrap();
            gm.read_exact_volatile_from(addr, &mut file, mem::size_of::<u32>())
                .unwrap();
            let value: u32 = gm.read_obj(addr).unwrap();
            if cfg!(target_family = "unix") {
                assert_eq!(value, 0);
            } else {
                assert_eq!(value, 0x0090_5a4d);
            }

            let mut sink = vec![0; mem::size_of::<u32>()];
            gm.write_all_volatile_to(addr, &mut sink.as_mut_slice(), mem::size_of::<u32>())
                .unwrap();
            assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
        }
    }

    #[test]
    fn test_access_cross_boundary() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x1000).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x1000).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        for gm in AnyBackend::all(&[
            (start_addr1, 0x1000, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x1000, Some(FileOffset::new(f2, 0))),
        ]) {
            let sample_buf = &[1, 2, 3, 4, 5];
            assert_eq!(gm.write(sample_buf, GuestAddress(0xffc)).unwrap(), 5);
            let buf = &mut [0u8; 5];
            assert_eq!(gm.read(buf, GuestAddress(0xffc)).unwrap(), 5);
            assert_eq!(buf, sample_buf);
        }
    }

    #[test]
    fn test_retrieve_fd_backing_memory_region() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let start_addr = GuestAddress(0x0);
        for gm in AnyBackend::all_with_file(&[(start_addr, 0x400, FileOffset::new(f, 0))]) {
            assert!(gm.find_region(start_addr).is_some());
            let region = gm.find_region(start_addr).unwrap();
            assert!(region.file_offset().is_some());
        }
    }

    // Windows needs a dedicated test where it will retrieve the allocation
    // granularity to determine a proper offset (other than 0) that can be
    // used for the backing file. Refer to Microsoft docs here:
    // https://docs.microsoft.com/en-us/windows/desktop/api/memoryapi/nf-memoryapi-mapviewoffile
    #[test]
    #[cfg(target_family = "unix")]
    fn test_retrieve_offset_from_fd_backing_memory_region() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x1400).unwrap();
        // Needs to be aligned on 4k, otherwise mmap will fail.
        let offset = 0x1000;

        let start_addr = GuestAddress(0x0);

        for gm in AnyBackend::all_with_file(&[(start_addr, 0x400, FileOffset::new(f, offset))]) {
            assert!(gm.find_region(start_addr).is_some());
            let region = gm.find_region(start_addr).unwrap();
            assert!(region.file_offset().is_some());
            assert_eq!(region.file_offset().unwrap().start(), offset);
        }
    }

    #[test]
    fn test_guest_memory_mmap_get_slice() {
        for region in AnyRegion::all(GuestAddress(0), 0x400, &None) {
            // Normal case.
            let slice_addr = MemoryRegionAddress(0x100);
            let slice_size = 0x200;
            let slice = region.get_slice(slice_addr, slice_size).unwrap();
            assert_eq!(slice.len(), slice_size);

            // Empty slice.
            let slice_addr = MemoryRegionAddress(0x200);
            let slice_size = 0x0;
            let slice = region.get_slice(slice_addr, slice_size).unwrap();
            assert!(slice.is_empty());

            // Error case when slice_size is beyond the boundary.
            let slice_addr = MemoryRegionAddress(0x300);
            let slice_size = 0x200;
            assert!(region.get_slice(slice_addr, slice_size).is_err());
        }
    }

    #[test]
    fn test_guest_memory_mmap_as_volatile_slice() {
        let region_size = 0x400;

        for region in AnyRegion::all(GuestAddress(0), region_size, &None) {
            // Test slice length.
            let slice = region.as_volatile_slice().unwrap();
            assert_eq!(slice.len(), region_size);

            // Test slice data.
            let v = 0x1234_5678u32;
            let r = slice.get_ref::<u32>(0x200).unwrap();
            r.store(v);
            assert_eq!(r.load(), v);
        }
    }

    #[test]
    fn test_guest_memory_get_slice() {
        let start_addr1 = GuestAddress(0);
        let start_addr2 = GuestAddress(0x800);
        for guest_mem in AnyBackend::all(&[(start_addr1, 0x400, None), (start_addr2, 0x400, None)])
        {
            // Normal cases.
            let slice_size = 0x200;
            let slice = guest_mem
                .get_slice(GuestAddress(0x100), slice_size)
                .unwrap();
            assert_eq!(slice.len(), slice_size);

            let slice_size = 0x400;
            let slice = guest_mem
                .get_slice(GuestAddress(0x800), slice_size)
                .unwrap();
            assert_eq!(slice.len(), slice_size);

            // Empty slice.
            assert!(guest_mem
                .get_slice(GuestAddress(0x900), 0)
                .unwrap()
                .is_empty());

            // Error cases, wrong size or base address.
            assert!(guest_mem.get_slice(GuestAddress(0), 0x500).is_err());
            assert!(guest_mem.get_slice(GuestAddress(0x600), 0x100).is_err());
            assert!(guest_mem.get_slice(GuestAddress(0xc00), 0x100).is_err());
        }
    }

    #[test]
    fn test_guest_memory_get_slices() {
        let start_addr1 = GuestAddress(0);
        let start_addr2 = GuestAddress(0x800);
        let start_addr3 = GuestAddress(0xc00);
        for guest_mem in AnyBackend::all(&[
            (start_addr1, 0x400, None),
            (start_addr2, 0x400, None),
            (start_addr3, 0x400, None),
        ]) {
            // Same cases as `test_guest_memory_get_slice()`, just with `get_slices()`.
            let slice_size = 0x200;
            let mut slices = guest_mem.get_slices(GuestAddress(0x100), slice_size);
            let slice = slices.next().unwrap().unwrap();
            assert!(slices.next().is_none());
            assert_eq!(slice.len(), slice_size);

            let slice_size = 0x400;
            let mut slices = guest_mem.get_slices(GuestAddress(0x800), slice_size);
            let slice = slices.next().unwrap().unwrap();
            assert!(slices.next().is_none());
            assert_eq!(slice.len(), slice_size);

            // Empty iterator.
            assert!(guest_mem
                .get_slices(GuestAddress(0x900), 0)
                .next()
                .is_none());

            // Error cases, wrong size or base address.
            let mut slices = guest_mem.get_slices(GuestAddress(0), 0x500);
            assert_eq!(slices.next().unwrap().unwrap().len(), 0x400);
            assert!(slices.next().unwrap().is_err());
            assert!(slices.next().is_none());
            let mut slices = guest_mem.get_slices(GuestAddress(0x600), 0x100);
            assert!(slices.next().unwrap().is_err());
            assert!(slices.next().is_none());
            let mut slices = guest_mem.get_slices(GuestAddress(0x1000), 0x100);
            assert!(slices.next().unwrap().is_err());
            assert!(slices.next().is_none());

            // Test fragmented case
            let mut slices = guest_mem.get_slices(GuestAddress(0xa00), 0x400);
            assert_eq!(slices.next().unwrap().unwrap().len(), 0x200);
            assert_eq!(slices.next().unwrap().unwrap().len(), 0x200);
            assert!(slices.next().is_none());
        }
    }

    #[test]
    fn test_atomic_accesses() {
        for region in AnyRegion::all(GuestAddress(0), 0x1000, &None) {
            crate::bytes::tests::check_atomic_accesses(
                region,
                MemoryRegionAddress(0),
                MemoryRegionAddress(0x1000),
            );
        }
    }
}
