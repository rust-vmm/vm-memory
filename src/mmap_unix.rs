// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Helper structure for working with mmaped memory regions in Unix.

use std::io;
use std::os::unix::io::AsRawFd;
use std::ptr::null_mut;
use std::result;

use crate::bitmap::{Bitmap, BS};
use crate::guest_memory::FileOffset;
use crate::mmap::{check_file_offset, GuestMmapRange, NewBitmap};
use crate::volatile_memory::{self, VolatileMemory, VolatileSlice};
use crate::MmapInfo;

#[cfg(feature = "xen")]
use crate::guest_memory::GuestAddress;

/// Error conditions that may arise when creating a new `MmapRegion` object.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// The specified file offset and length cause overflow when added.
    #[error("The specified file offset and length cause overflow when added")]
    InvalidOffsetLength,
    /// The specified pointer to the mapping is not page-aligned.
    #[error("The specified pointer to the mapping is not page-aligned")]
    InvalidPointer,
    /// The forbidden `MAP_FIXED` flag was specified.
    #[error("The forbidden `MAP_FIXED` flag was specified")]
    MapFixed,
    /// Mappings using the same fd overlap in terms of file offset and length.
    #[error("Mappings using the same fd overlap in terms of file offset and length")]
    MappingOverlap,
    /// A mapping with offset + length > EOF was attempted.
    #[error("The specified file offset and length is greater then file length")]
    MappingPastEof,
    /// The `mmap` call returned an error.
    #[error("{0}")]
    Mmap(io::Error),
    /// Seeking the end of the file returned an error.
    #[error("Error seeking the end of the file: {0}")]
    SeekEnd(io::Error),
    /// Seeking the start of the file returned an error.
    #[error("Error seeking the start of the file: {0}")]
    SeekStart(io::Error),
    /// Missing prot.
    #[error("Missing prot")]
    MissingProt,
    /// Missing flags.
    #[error("Missing flags")]
    MissingFlags,
    /// Invalid file offset.
    #[error("Invalid file offset")]
    InvalidFileOffset,
    /// Xen specific error wrapper.
    #[cfg(feature = "xen")]
    #[error("Xen specific errors: {0}")]
    Xen(crate::mmap_xen::XenError),
}

pub type Result<T> = result::Result<T, Error>;

/// `MmapRange` represents a range of arguments required to create Mmap regions.
#[derive(Clone, Debug)]
pub struct MmapRange {
    size: usize,
    file: Option<FileOffset>,
    prot: Option<i32>,
    flags: Option<i32>,

    // Region's address
    #[cfg(feature = "xen")]
    addr: GuestAddress,
    // Xen mmap flags
    #[cfg(feature = "xen")]
    mmap_flags: u32,
    // Xen mmap data
    #[cfg(feature = "xen")]
    mmap_data: u32,
}

impl MmapRange {
    /// Creates instance of the range with `size`.
    pub fn new(size: usize) -> Self {
        Self::with_file(size, None, None, None)
    }

    /// Creates instance of the range with multiple arguments.
    pub fn with_file(
        size: usize,
        file: Option<FileOffset>,
        prot: Option<i32>,
        flags: Option<i32>,
    ) -> Self {
        Self {
            size,
            file,
            prot,
            flags,

            // Defaults to standard UNIX mapping. Use `with_xen()` for Xen specific mappings.
            #[cfg(feature = "xen")]
            addr: GuestAddress(0),
            #[cfg(feature = "xen")]
            mmap_flags: super::MmapXenFlags::UNIX.bits(),
            #[cfg(feature = "xen")]
            mmap_data: 0,
        }
    }

    #[cfg(all(feature = "xen", unix))]
    /// Creates instance of the range with multiple arguments.
    pub fn with_xen(
        size: usize,
        file: Option<FileOffset>,
        prot: Option<i32>,
        flags: Option<i32>,
        addr: GuestAddress,
        mmap_flags: u32,
        mmap_data: u32,
    ) -> Self {
        Self {
            size,
            file,
            prot,
            flags,
            addr,
            mmap_flags,
            mmap_data,
        }
    }
}

impl From<GuestMmapRange> for MmapRange {
    fn from(r: GuestMmapRange) -> Self {
        Self {
            size: r.size,
            file: r.file,
            prot: None,
            flags: None,

            #[cfg(feature = "xen")]
            addr: r.addr,
            #[cfg(feature = "xen")]
            mmap_flags: r.mmap_flags,
            #[cfg(feature = "xen")]
            mmap_data: r.mmap_data,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Mmap {
    addr: *mut u8,
    size: usize,
    owned: bool,
}

impl Mmap {
    pub(crate) fn new(size: usize, prot: i32, flags: i32, fd: i32, f_offset: u64) -> Result<Self> {
        #[cfg(not(miri))]
        let addr =
        // SAFETY: This is safe because we're not allowing MAP_FIXED, and invalid parameters
        // cannot break Rust safety guarantees (things may change if we're mapping /dev/mem or
        // some wacky file).
            unsafe { libc::mmap(null_mut(), size, prot, flags, fd, f_offset as libc::off_t) };

        #[cfg(not(miri))]
        if addr == libc::MAP_FAILED {
            return Err(Error::Mmap(io::Error::last_os_error()));
        }

        #[cfg(miri)]
        if size == 0 {
            return Err(Error::Mmap(io::Error::from_raw_os_error(libc::EINVAL)));
        }

        // Miri does not support the mmap syscall, so we use rust's allocator for miri tests
        #[cfg(miri)]
        let addr = unsafe {
            std::alloc::alloc_zeroed(std::alloc::Layout::from_size_align(size, 8).unwrap())
        };

        Ok(Self {
            addr: addr as *mut u8,
            size,
            owned: true,
        })
    }

    pub(crate) fn with_checks(
        size: usize,
        prot: i32,
        flags: i32,
        file_offset: &Option<FileOffset>,
    ) -> Result<Self> {
        let (fd, f_offset) = if let Some(ref f_offset) = file_offset {
            check_file_offset(f_offset, size)?;
            (f_offset.file().as_raw_fd(), f_offset.start())
        } else {
            (-1, 0)
        };

        Self::new(size, prot, flags, fd, f_offset)
    }

    pub(crate) fn addr(&self) -> *mut u8 {
        self.addr
    }

    pub(crate) fn raw(addr: *mut u8) -> Self {
        Self {
            addr,
            size: 0,
            owned: false,
        }
    }

    pub(crate) fn mmap_in_advance(&self) -> bool {
        true
    }
}

impl Drop for Mmap {
    fn drop(&mut self) {
        if self.owned {
            // SAFETY: This is safe because we mmap the area at addr ourselves, and nobody
            // else is holding a reference to it.
            unsafe {
                #[cfg(not(miri))]
                libc::munmap(self.addr as *mut libc::c_void, self.size);

                #[cfg(miri)]
                std::alloc::dealloc(
                    self.addr,
                    std::alloc::Layout::from_size_align(self.size, 8).unwrap(),
                );
            }
        }
    }
}

/// A factory struct to build `MmapRegion` objects.
pub struct MmapRegionBuilder<B = ()> {
    size: usize,
    prot: i32,
    flags: i32,
    file_offset: Option<FileOffset>,
    raw_ptr: Option<*mut u8>,
    hugetlbfs: Option<bool>,
    bitmap: B,
    mmap: Option<MmapInfo>,
}

impl<B: Bitmap + Default> MmapRegionBuilder<B> {
    /// Create a new `MmapRegionBuilder` using the default value for
    /// the inner `Bitmap` object.
    pub fn new(size: usize) -> Self {
        Self::new_with_bitmap(size, B::default())
    }
}

impl<B: Bitmap> MmapRegionBuilder<B> {
    /// Create a new `MmapRegionBuilder` using the provided `Bitmap` object.
    ///
    /// When instantiating the builder for a region that does not require dirty bitmap
    /// bitmap tracking functionality, we can specify a trivial `Bitmap` implementation
    /// such as `()`.
    pub fn new_with_bitmap(size: usize, bitmap: B) -> Self {
        MmapRegionBuilder {
            size,
            prot: 0,
            flags: libc::MAP_ANONYMOUS | libc::MAP_PRIVATE,
            file_offset: None,
            raw_ptr: None,
            hugetlbfs: None,
            bitmap,
            mmap: None,
        }
    }

    /// Create the `MmapRegion` object with the specified mmap memory protection flag `prot`.
    pub fn with_mmap_prot(mut self, prot: i32) -> Self {
        self.prot = prot;
        self
    }

    /// Create the `MmapRegion` object with the specified mmap `flags`.
    pub fn with_mmap_flags(mut self, flags: i32) -> Self {
        self.flags = flags;
        self
    }

    /// Create the `MmapRegion` object with the specified `file_offset`.
    pub fn with_file_offset(mut self, file_offset: FileOffset) -> Self {
        self.file_offset = Some(file_offset);
        self
    }

    /// Create the `MmapRegion` object with the specified `hugetlbfs` flag.
    pub fn with_hugetlbfs(mut self, hugetlbfs: bool) -> Self {
        self.hugetlbfs = Some(hugetlbfs);
        self
    }

    /// Create the `MmapRegion` object with pre-mmapped raw pointer.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that `raw_addr` and `self.size` define a
    /// region within a valid mapping that is already present in the process.
    pub unsafe fn with_raw_mmap_pointer(mut self, raw_ptr: *mut u8) -> Self {
        self.raw_ptr = Some(raw_ptr);
        self
    }

    /// Build the `MmapRegion` object.
    pub fn build(mut self) -> Result<MmapRegion<B>> {
        if self.raw_ptr.is_some() {
            return self.build_raw();
        }

        // Forbid MAP_FIXED, as it doesn't make sense in this context, and is pretty dangerous
        // in general.
        if self.flags & libc::MAP_FIXED != 0 {
            return Err(Error::MapFixed);
        }

        self.mmap()?;
        self.build_region()
    }

    fn build_raw(mut self) -> Result<MmapRegion<B>> {
        // SAFETY: Safe because this call just returns the page size and doesn't have any side
        // effects.
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
        let addr = self.raw_ptr.unwrap();

        // Check that the pointer to the mapping is page-aligned.
        if (addr as usize) & (page_size - 1) != 0 {
            return Err(Error::InvalidPointer);
        }

        self.raw_mmap(addr);
        self.build_region()
    }

    fn build_region(self) -> Result<MmapRegion<B>> {
        Ok(MmapRegion {
            size: self.size,
            bitmap: self.bitmap,
            file_offset: self.file_offset,
            prot: self.prot,
            flags: self.flags,
            hugetlbfs: self.hugetlbfs,
            mmap: self.mmap.unwrap(),
        })
    }
}

impl<B: NewBitmap> MmapRegionBuilder<B> {
    fn from_range(range: MmapRange) -> Result<Self> {
        let prot = range.prot.ok_or(Error::MissingProt)?;
        let flags = range.flags.ok_or(Error::MissingFlags)?;

        let mut builder = Self::new_with_bitmap(range.size, B::with_len(range.size))
            .with_mmap_prot(prot)
            .with_mmap_flags(flags);

        if let Some(f_off) = range.file {
            builder = builder.with_file_offset(f_off);
        }

        #[cfg(feature = "xen")]
        let builder = builder.with_mmap_info(range.addr, range.mmap_flags, range.mmap_data)?;

        Ok(builder)
    }
}

#[cfg(not(feature = "xen"))]
impl<B: Bitmap> MmapRegionBuilder<B> {
    fn mmap(&mut self) -> Result<()> {
        self.mmap = Some(MmapInfo::with_checks(
            self.size,
            self.prot,
            self.flags,
            &self.file_offset,
        )?);

        Ok(())
    }

    fn raw_mmap(&mut self, addr: *mut u8) {
        self.mmap = Some(MmapInfo::raw(addr));
    }
}

#[cfg(feature = "xen")]
impl<B: Bitmap> MmapRegionBuilder<B> {
    fn mmap(&mut self) -> Result<()> {
        self.mmap
            .as_mut()
            .unwrap()
            .mmap(self.size, self.prot, self.flags, &self.file_offset)
    }

    fn raw_mmap(&mut self, addr: *mut u8) {
        self.mmap.as_mut().unwrap().raw_mmap(addr)
    }

    /// Create the `MmapRegion` object with the specified Xen mmap `flags` and data.
    pub fn with_mmap_info(
        mut self,
        addr: GuestAddress,
        mmap_flags: u32,
        mmap_data: u32,
    ) -> Result<Self> {
        self.mmap = Some(MmapInfo::new(addr, mmap_flags, mmap_data)?);
        Ok(self)
    }
}

/// Helper structure for working with mmaped memory regions in Unix.
///
/// The structure is used for accessing the guest's physical memory by mmapping it into
/// the current process.
///
/// # Limitations
/// When running a 64-bit virtual machine on a 32-bit hypervisor, only part of the guest's
/// physical memory may be mapped into the current process due to the limited virtual address
/// space size of the process.
#[derive(Debug)]
pub struct MmapRegion<B = ()> {
    size: usize,
    bitmap: B,
    file_offset: Option<FileOffset>,
    prot: i32,
    flags: i32,
    hugetlbfs: Option<bool>,
    mmap: MmapInfo,
}

// SAFETY: Send and Sync aren't automatically inherited for the raw address pointer.
// Accessing that pointer is only done through the stateless interface which
// allows the object to be shared by multiple threads without a decrease in
// safety.
unsafe impl<B: Send> Send for MmapRegion<B> {}
// SAFETY: See comment above.
unsafe impl<B: Sync> Sync for MmapRegion<B> {}

impl<B: NewBitmap> MmapRegion<B> {
    /// Creates a shared anonymous mapping of `size` bytes.
    ///
    /// # Arguments
    /// * `range` - An instance of type `MmapRange`.
    pub fn new(mut range: MmapRange) -> Result<Self> {
        if range.prot.is_none() {
            range.prot = Some(libc::PROT_READ | libc::PROT_WRITE);
        }

        if range.flags.is_none() {
            range.flags = Some(if range.file.is_some() {
                libc::MAP_NORESERVE | libc::MAP_SHARED
            } else {
                libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_PRIVATE
            });
        }

        MmapRegionBuilder::from_range(range)?.build()
    }

    /// Creates a `MmapRegion` instance for an externally managed mapping.
    ///
    /// This method is intended to be used exclusively in situations in which the mapping backing
    /// the region is provided by an entity outside the control of the caller (e.g. the dynamic
    /// linker).
    ///
    /// # Arguments
    /// * `addr` - Pointer to the start of the mapping. Must be page-aligned.
    /// * `size` - The size of the memory region in bytes.
    /// * `prot` - Must correspond to the memory protection attributes of the existing mapping.
    /// * `flags` - Must correspond to the flags that were passed to `mmap` for the creation of
    ///             the existing mapping.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that `addr` and `size` define a region within
    /// a valid mapping that is already present in the process.
    pub unsafe fn build_raw(addr: *mut u8, range: MmapRange) -> Result<Self> {
        if range.file.is_some() {
            return Err(Error::InvalidFileOffset);
        }

        MmapRegionBuilder::from_range(range)?
            .with_raw_mmap_pointer(addr)
            .build()
    }
}

impl<B: Bitmap> MmapRegion<B> {
    /// Returns a pointer to the beginning of the memory region. Mutable accesses performed
    /// using the resulting pointer are not automatically accounted for by the dirty bitmap
    /// tracking functionality.
    ///
    /// Should only be used for passing this region to ioctls for setting guest memory.
    pub fn as_ptr(&self) -> *mut u8 {
        self.mmap.addr()
    }

    /// Returns the size of this region.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns information regarding the offset into the file backing this region (if any).
    pub fn file_offset(&self) -> Option<&FileOffset> {
        self.file_offset.as_ref()
    }

    /// Returns the value of the `prot` parameter passed to `mmap` when mapping this region.
    pub fn prot(&self) -> i32 {
        self.prot
    }

    /// Returns the value of the `flags` parameter passed to `mmap` when mapping this region.
    pub fn flags(&self) -> i32 {
        self.flags
    }

    /// Checks whether this region and `other` are backed by overlapping
    /// [`FileOffset`](struct.FileOffset.html) objects.
    ///
    /// This is mostly a sanity check available for convenience, as different file descriptors
    /// can alias the same file.
    pub fn fds_overlap<T: Bitmap>(&self, other: &MmapRegion<T>) -> bool {
        if let Some(f_off1) = self.file_offset() {
            if let Some(f_off2) = other.file_offset() {
                if f_off1.file().as_raw_fd() == f_off2.file().as_raw_fd() {
                    let s1 = f_off1.start();
                    let s2 = f_off2.start();
                    let l1 = self.len() as u64;
                    let l2 = other.len() as u64;

                    if s1 < s2 {
                        return s1 + l1 > s2;
                    } else {
                        return s2 + l2 > s1;
                    }
                }
            }
        }
        false
    }

    /// Set the hugetlbfs of the region
    pub fn set_hugetlbfs(&mut self, hugetlbfs: bool) {
        self.hugetlbfs = Some(hugetlbfs)
    }

    /// Returns `true` if the region is hugetlbfs
    pub fn is_hugetlbfs(&self) -> Option<bool> {
        self.hugetlbfs
    }

    /// Returns a reference to the inner bitmap object.
    pub fn bitmap(&self) -> &B {
        &self.bitmap
    }

    fn region_ref(&self) -> Option<&MmapInfo> {
        if self.mmap.mmap_in_advance() {
            None
        } else {
            Some(&self.mmap)
        }
    }
}

#[cfg(feature = "xen")]
impl<B> MmapRegion<B> {
    /// Returns xen mmap flags.
    pub fn xen_mmap_flags(&self) -> u32 {
        self.mmap.flags()
    }

    /// Returns xen mmap data.
    pub fn xen_mmap_data(&self) -> u32 {
        self.mmap.data()
    }
}

impl<B: Bitmap> VolatileMemory for MmapRegion<B> {
    type B = B;

    fn len(&self) -> usize {
        self.size
    }

    fn get_slice(
        &self,
        offset: usize,
        count: usize,
    ) -> volatile_memory::Result<VolatileSlice<BS<B>>> {
        let _ = self.compute_end_offset(offset, count)?;

        Ok(
            // SAFETY: Safe because we checked that offset + count was within our range and we only
            // ever hand out volatile accessors.
            unsafe {
                VolatileSlice::with_bitmap(
                    self.as_ptr().add(offset),
                    count,
                    self.bitmap.slice_at(offset),
                    self.region_ref(),
                )
            },
        )
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]
    use super::*;

    use std::io::Write;
    use std::slice;
    use std::sync::Arc;
    use vmm_sys_util::tempfile::TempFile;

    use crate::bitmap::AtomicBitmap;

    type MmapRegion = super::MmapRegion<()>;

    impl Mmap {
        pub fn owned(&self) -> bool {
            self.owned
        }
    }

    // Adding a helper method to extract the errno within an Error::Mmap(e), or return a
    // distinctive value when the error is represented by another variant.
    impl Error {
        pub fn raw_os_error(&self) -> i32 {
            match self {
                Error::Mmap(e) => e.raw_os_error().unwrap(),
                _ => std::i32::MIN,
            }
        }
    }

    impl<B: Bitmap> MmapRegionBuilder<B> {
        pub fn with_mmap_info_def(self) -> Self {
            #[cfg(not(feature = "xen"))]
            return self;

            #[cfg(feature = "xen")]
            self.with_mmap_info(
                GuestAddress(0),
                crate::mmap_xen::MmapXenFlags::UNIX.bits(),
                0,
            )
            .unwrap()
        }
    }

    #[test]
    fn test_mmap_region_new() {
        assert!(MmapRegion::new(MmapRange::new(0)).is_err());

        let size = 4096;

        let r = MmapRegion::new(MmapRange::new(4096)).unwrap();
        assert_eq!(r.size(), size);
        assert!(r.file_offset().is_none());
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(
            r.flags(),
            libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_PRIVATE
        );
    }

    #[test]
    fn test_mmap_region_set_hugetlbfs() {
        assert!(MmapRegion::new(MmapRange::new(0)).is_err());

        let size = 4096;
        let range = MmapRange::new(size);

        let r = MmapRegion::new(range.clone()).unwrap();
        assert_eq!(r.size(), size);
        assert!(r.file_offset().is_none());
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(
            r.flags(),
            libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_PRIVATE
        );
        assert_eq!(r.is_hugetlbfs(), None);

        let mut r = MmapRegion::new(range.clone()).unwrap();
        r.set_hugetlbfs(false);
        assert_eq!(r.size(), size);
        assert!(r.file_offset().is_none());
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(
            r.flags(),
            libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_PRIVATE
        );
        assert_eq!(r.is_hugetlbfs(), Some(false));

        let mut r = MmapRegion::new(range).unwrap();
        r.set_hugetlbfs(true);
        assert_eq!(r.size(), size);
        assert!(r.file_offset().is_none());
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(
            r.flags(),
            libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_PRIVATE
        );
        assert_eq!(r.is_hugetlbfs(), Some(true));
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_mmap_region_from_file() {
        let mut f = TempFile::new().unwrap().into_file();
        let offset: usize = 0;
        let buf1 = [1u8, 2, 3, 4, 5];

        f.write_all(buf1.as_ref()).unwrap();
        let range = MmapRange::with_file(
            buf1.len(),
            Some(FileOffset::new(f, offset as u64)),
            None,
            None,
        );
        let r = MmapRegion::new(range).unwrap();

        assert_eq!(r.size(), buf1.len() - offset);
        assert_eq!(r.file_offset().unwrap().start(), offset as u64);
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(r.flags(), libc::MAP_NORESERVE | libc::MAP_SHARED);

        let buf2 = unsafe { slice::from_raw_parts(r.as_ptr(), buf1.len() - offset) };
        assert_eq!(&buf1[offset..], buf2);
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_mmap_region_build() {
        let a = Arc::new(TempFile::new().unwrap().into_file());

        let prot = libc::PROT_READ | libc::PROT_WRITE;
        let flags = libc::MAP_NORESERVE | libc::MAP_PRIVATE;
        let offset = 4096;
        let size = 1000;

        // Offset + size will overflow.
        let r = MmapRegion::new(MmapRange::with_file(
            size,
            Some(FileOffset::from_arc(a.clone(), std::u64::MAX)),
            Some(prot),
            Some(flags),
        ));
        assert_eq!(format!("{:?}", r.unwrap_err()), "InvalidOffsetLength");

        // Offset + size is greater than the size of the file (which is 0 at this point).
        let r = MmapRegion::new(MmapRange::with_file(
            size,
            Some(FileOffset::from_arc(a.clone(), offset)),
            Some(prot),
            Some(flags),
        ));
        assert_eq!(format!("{:?}", r.unwrap_err()), "MappingPastEof");

        // MAP_FIXED was specified among the flags.
        let r = MmapRegion::new(MmapRange::with_file(
            size,
            Some(FileOffset::from_arc(a.clone(), offset)),
            Some(prot),
            Some(flags | libc::MAP_FIXED),
        ));
        assert_eq!(format!("{:?}", r.unwrap_err()), "MapFixed");

        // Let's resize the file.
        assert_eq!(unsafe { libc::ftruncate(a.as_raw_fd(), 1024 * 10) }, 0);

        // The offset is not properly aligned.
        let r = MmapRegion::new(MmapRange::with_file(
            size,
            Some(FileOffset::from_arc(a.clone(), offset - 1)),
            Some(prot),
            Some(flags),
        ));
        assert_eq!(r.unwrap_err().raw_os_error(), libc::EINVAL);

        // The build should be successful now.
        let r = MmapRegion::new(MmapRange::with_file(
            size,
            Some(FileOffset::from_arc(a, offset)),
            Some(prot),
            Some(flags),
        ))
        .unwrap();

        assert_eq!(r.size(), size);
        assert_eq!(r.file_offset().unwrap().start(), offset);
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(r.flags(), libc::MAP_NORESERVE | libc::MAP_PRIVATE);
        assert!(r.mmap.owned());

        let region_size = 0x10_0000;
        let bitmap = AtomicBitmap::new(region_size, 0x1000);
        let builder = MmapRegionBuilder::new_with_bitmap(region_size, bitmap)
            .with_hugetlbfs(true)
            .with_mmap_prot(libc::PROT_READ | libc::PROT_WRITE)
            .with_mmap_info_def();
        assert_eq!(builder.size, region_size);
        assert_eq!(builder.hugetlbfs, Some(true));
        assert_eq!(builder.prot, libc::PROT_READ | libc::PROT_WRITE);

        crate::bitmap::tests::test_volatile_memory(&(builder.build().unwrap()));
    }

    #[test]
    #[cfg(not(miri))] // Causes warnings due to the pointer casts
    fn test_mmap_region_build_raw() {
        let addr = 0;
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
        let prot = libc::PROT_READ | libc::PROT_WRITE;
        let flags = libc::MAP_NORESERVE | libc::MAP_PRIVATE;

        let range = MmapRange::with_file(size, None, Some(prot), Some(flags));
        let r = unsafe { MmapRegion::build_raw((addr + 1) as *mut u8, range.clone()) };
        assert_eq!(format!("{:?}", r.unwrap_err()), "InvalidPointer");

        let r = unsafe { MmapRegion::build_raw(addr as *mut u8, range).unwrap() };

        assert_eq!(r.size(), size);
        assert_eq!(r.prot(), libc::PROT_READ | libc::PROT_WRITE);
        assert_eq!(r.flags(), libc::MAP_NORESERVE | libc::MAP_PRIVATE);
        assert!(!r.mmap.owned());
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_mmap_region_fds_overlap() {
        let a = Arc::new(TempFile::new().unwrap().into_file());
        assert_eq!(unsafe { libc::ftruncate(a.as_raw_fd(), 1024 * 10) }, 0);

        let range =
            MmapRange::with_file(4096, Some(FileOffset::from_arc(a.clone(), 0)), None, None);
        let r1 = MmapRegion::new(range).unwrap();

        let range = MmapRange::with_file(
            4096,
            Some(FileOffset::from_arc(a.clone(), 4096)),
            None,
            None,
        );
        let r2 = MmapRegion::new(range).unwrap();
        assert!(!r1.fds_overlap(&r2));

        let range =
            MmapRange::with_file(5000, Some(FileOffset::from_arc(a.clone(), 0)), None, None);
        let r1 = MmapRegion::new(range).unwrap();
        assert!(r1.fds_overlap(&r2));

        let range = MmapRange::with_file(1000, Some(FileOffset::from_arc(a, 0)), None, None);
        let r2 = MmapRegion::new(range).unwrap();
        assert!(r1.fds_overlap(&r2));

        // Different files, so there's not overlap.
        let new_file = TempFile::new().unwrap().into_file();
        // Resize before mapping.
        assert_eq!(
            unsafe { libc::ftruncate(new_file.as_raw_fd(), 1024 * 10) },
            0
        );
        let range = MmapRange::with_file(5000, Some(FileOffset::new(new_file, 0)), None, None);
        let r2 = MmapRegion::new(range).unwrap();
        assert!(!r1.fds_overlap(&r2));

        // R2 is not file backed, so no overlap.
        let r2 = MmapRegion::new(MmapRange::new(5000)).unwrap();
        assert!(!r1.fds_overlap(&r2));
    }

    #[test]
    fn test_dirty_tracking() {
        // Using the `crate` prefix because we aliased `MmapRegion` to `MmapRegion<()>` for
        // the rest of the unit tests above.
        let m = crate::MmapRegion::<AtomicBitmap>::new(MmapRange::new(0x1_0000)).unwrap();
        crate::bitmap::tests::test_volatile_memory(&m);
    }
}
