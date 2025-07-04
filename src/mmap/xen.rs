// Copyright 2023 Linaro Ltd. All Rights Reserved.
//          Viresh Kumar <viresh.kumar@linaro.org>
//
// Xen specific memory mapping implementations
//
// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

//! Helper structure for working with mmap'ed memory regions on Xen.

use bitflags::bitflags;
use libc::{c_int, c_void, MAP_SHARED, _SC_PAGESIZE};
use std::sync::Arc;
use std::{io, mem::size_of, os::raw::c_ulong, os::unix::io::AsRawFd, ptr::null_mut, result};
use vmm_sys_util::{
    fam::{Error as FamError, FamStruct, FamStructWrapper},
    generate_fam_struct_impl,
    ioctl::{ioctl_expr, _IOC_NONE},
};

// Use a dummy ioctl implementation for tests instead.
#[cfg(not(test))]
use vmm_sys_util::ioctl::ioctl_with_ref;

#[cfg(test)]
use tests::ioctl_with_ref;

use crate::bitmap::{Bitmap, NewBitmap, BS};
use crate::guest_memory::{FileOffset, GuestAddress};
use crate::mmap::unix::MmapRegion as MmapUnix;
use crate::volatile_memory::{self, VolatileMemory, VolatileSlice};
use crate::{
    guest_memory, Address, GuestMemoryRegion, GuestMemoryRegionBytes, GuestRegionCollection,
    GuestUsize, MemoryRegionAddress, MmapRegionBuilder,
};

/// Error conditions that may arise when creating a new `MmapRegion` object.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// The forbidden `MAP_FIXED` flag was specified.
    #[error("The forbidden `MAP_FIXED` flag was specified")]
    MapFixed,
    /// The `mmap` call returned an error.
    #[error("{0}")]
    Mmap(io::Error),
    /// Invalid file offset (non-zero of missing altogether).
    #[error("Invalid file offset")]
    InvalidFileOffset,
    /// Memory mapped in advance.
    #[error("Memory mapped in advance")]
    MappedInAdvance,
    /// Invalid Xen mmap flags.
    #[error("Invalid Xen Mmap flags: {0:x}")]
    MmapFlags(u32),
    /// Fam error.
    #[error("Fam error: {0}")]
    Fam(FamError),
    /// Unexpected error.
    #[error("Unexpected error")]
    Unexpected,
    /// Error establishing normal unix mapping
    #[error["{0}"]]
    Unix(#[from] crate::mmap::unix::Error),
}

type Result<T> = result::Result<T, Error>;

/// `MmapRange` represents a range of arguments required to create Mmap regions.
#[derive(Clone, Debug)]
pub struct MmapRange {
    size: usize,
    file_offset: Option<FileOffset>,
    prot: Option<i32>,
    flags: Option<i32>,
    hugetlbfs: Option<bool>,
    addr: GuestAddress,
    mmap_flags: u32,
    mmap_data: u32,
}

impl MmapRange {
    /// Creates instance of the range with multiple arguments.
    pub fn new(
        size: usize,
        file_offset: Option<FileOffset>,
        addr: GuestAddress,
        mmap_flags: u32,
        mmap_data: u32,
    ) -> Self {
        Self {
            size,
            file_offset,
            prot: None,
            flags: None,
            hugetlbfs: None,
            addr,
            mmap_flags,
            mmap_data,
        }
    }

    /// Creates instance of the range for `MmapXenFlags::UNIX` type mapping.
    pub fn new_unix(size: usize, file_offset: Option<FileOffset>, addr: GuestAddress) -> Self {
        let flags = Some(match file_offset {
            Some(_) => libc::MAP_NORESERVE | libc::MAP_SHARED,
            None => libc::MAP_ANONYMOUS | libc::MAP_PRIVATE,
        });

        Self {
            size,
            file_offset,
            prot: None,
            flags,
            hugetlbfs: None,
            addr,
            mmap_flags: MmapXenFlags::UNIX.bits(),
            mmap_data: 0,
        }
    }

    /// Set the prot of the range.
    pub fn set_prot(&mut self, prot: i32) {
        self.prot = Some(prot)
    }

    /// Set the flags of the range.
    pub fn set_flags(&mut self, flags: i32) {
        self.flags = Some(flags)
    }

    /// Set the hugetlbfs of the range.
    pub fn set_hugetlbfs(&mut self, hugetlbfs: bool) {
        self.hugetlbfs = Some(hugetlbfs)
    }
}

/// Helper structure for working with mmaped memory regions with Xen.
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
    bitmap: B,
    size: usize,
    prot: i32,
    flags: i32,
    file_offset: Option<FileOffset>,
    hugetlbfs: Option<bool>,
    mmap: MmapXen,
}

impl<B: Bitmap> GuestMemoryRegion for MmapRegion<B> {
    type B = B;

    fn len(&self) -> GuestUsize {
        self.size as GuestUsize
    }

    fn start_addr(&self) -> GuestAddress {
        self.mmap.mmap.guest_base()
    }

    fn bitmap(&self) -> BS<'_, Self::B> {
        self.bitmap.slice_at(0)
    }

    // TODO: MmapRegion::as_ptr states that it should only be used for passing pointers to ioctls. Should this function then just remain the default implementation of returning Err(InvalidHostAddress)?
    fn get_host_address(&self, addr: MemoryRegionAddress) -> crate::guest_memory::Result<*mut u8> {
        self.check_address(addr)
            .ok_or(guest_memory::Error::InvalidBackendAddress)
            .map(|addr| self.as_ptr().wrapping_offset(addr.raw_value() as isize))
    }

    fn file_offset(&self) -> Option<&FileOffset> {
        self.file_offset.as_ref()
    }

    fn get_slice(
        &self,
        offset: MemoryRegionAddress,
        count: usize,
    ) -> crate::guest_memory::Result<VolatileSlice<BS<Self::B>>> {
        VolatileMemory::get_slice(self, offset.raw_value() as usize, count).map_err(Into::into)
    }

    // TODO: does this make sense in the context of Xen, or should it just return None, as the default implementation does?
    // (and if running on Xen, will target_os="linux" even be true?)
    #[cfg(target_os = "linux")]
    fn is_hugetlbfs(&self) -> Option<bool> {
        self.hugetlbfs
    }
}

impl<B: Bitmap> GuestMemoryRegionBytes for MmapRegion<B> {}

/// A collection of Xen guest memory regions.
///
/// Represents the entire physical memory of the guest by tracking all its memory regions.
/// Each region is an instance of [`MmapRegionXen`].
pub type GuestMemoryXen<B> = GuestRegionCollection<MmapRegion<B>>;

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
    ///
    /// # Examples
    /// * Write a slice at guest address 0x1200 with Xen's Grant mapping.
    ///
    /// ```
    /// use std::fs::File;
    /// use std::path::Path;
    /// use vm_memory::{
    ///     Bytes, FileOffset, GuestAddress, GuestMemoryXen, MmapRange, MmapRegionXen, MmapXenFlags,
    /// };
    /// # use vmm_sys_util::tempfile::TempFile;
    ///
    /// let addr = GuestAddress(0x1000);
    /// # if false {
    /// let file = Some(FileOffset::new(
    ///     File::open(Path::new("/dev/xen/gntdev")).expect("Could not open file"),
    ///     0,
    /// ));
    ///
    /// let range = MmapRange::new(0x400, file, addr, MmapXenFlags::GRANT.bits(), 0);
    /// # }
    /// # // We need a UNIX mapping for tests to succeed.
    /// # let range = MmapRange::new_unix(0x400, None, addr);
    ///
    /// let r = MmapRegionXen::<()>::from_range(range).expect("Could not create mmap region");
    ///
    /// let mut gm = GuestMemoryXen::from_regions(vec![r]).expect("Could not create guest memory");
    /// let res = gm
    ///     .write(&[1, 2, 3, 4, 5], GuestAddress(0x1200))
    ///     .expect("Could not write to guest memory");
    /// assert_eq!(5, res);
    /// ```
    ///
    /// * Write a slice at guest address 0x1200 with Xen's Foreign mapping.
    ///
    /// ```
    /// use std::fs::File;
    /// use std::path::Path;
    /// use vm_memory::{
    ///     Bytes, FileOffset, GuestAddress, GuestMemoryXen, MmapRange, MmapRegionXen, MmapXenFlags,
    /// };
    /// # use vmm_sys_util::tempfile::TempFile;
    ///
    /// let addr = GuestAddress(0x1000);
    /// # if false {
    /// let file = Some(FileOffset::new(
    ///     File::open(Path::new("/dev/xen/privcmd")).expect("Could not open file"),
    ///     0,
    /// ));
    ///
    /// let range = MmapRange::new(0x400, file, addr, MmapXenFlags::FOREIGN.bits(), 0);
    /// # }
    /// # // We need a UNIX mapping for tests to succeed.
    /// # let range = MmapRange::new_unix(0x400, None, addr);
    ///
    /// let r = MmapRegionXen::<()>::from_range(range).expect("Could not create mmap region");
    ///
    /// let mut gm = GuestMemoryXen::from_regions(vec![r]).expect("Could not create guest memory");
    /// let res = gm
    ///     .write(&[1, 2, 3, 4, 5], GuestAddress(0x1200))
    ///     .expect("Could not write to guest memory");
    /// assert_eq!(5, res);
    /// ```
    pub fn from_range(mut range: MmapRange) -> Result<Self> {
        if range.prot.is_none() {
            range.prot = Some(libc::PROT_READ | libc::PROT_WRITE);
        }

        match range.flags {
            Some(flags) => {
                if flags & libc::MAP_FIXED != 0 {
                    // Forbid MAP_FIXED, as it doesn't make sense in this context, and is pretty dangerous
                    // in general.
                    return Err(Error::MapFixed);
                }
            }
            None => range.flags = Some(libc::MAP_NORESERVE | libc::MAP_SHARED),
        }

        let mmap = MmapXen::new(&range)?;

        Ok(MmapRegion {
            bitmap: B::with_len(range.size),
            size: range.size,
            prot: range.prot.ok_or(Error::Unexpected)?,
            flags: range.flags.ok_or(Error::Unexpected)?,
            file_offset: range.file_offset,
            hugetlbfs: range.hugetlbfs,
            mmap,
        })
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
                    let l1 = self.size as u64;
                    let l2 = other.size as u64;

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

        let mmap_info = if self.mmap.mmap_in_advance() {
            None
        } else {
            Some(&self.mmap)
        };

        Ok(
            // SAFETY: Safe because we checked that offset + count was within our range and we only
            // ever hand out volatile accessors.
            unsafe {
                VolatileSlice::with_bitmap(
                    self.as_ptr().add(offset),
                    count,
                    self.bitmap.slice_at(offset),
                    mmap_info,
                )
            },
        )
    }
}

// Bit mask for the vhost-user xen mmap message.
bitflags! {
    /// Flags for the Xen mmap message.
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct MmapXenFlags: u32 {
        /// Standard Unix memory mapping.
        const UNIX = 0x0;
        /// Xen foreign memory (accessed via /dev/privcmd).
        const FOREIGN = 0x1;
        /// Xen grant memory (accessed via /dev/gntdev).
        const GRANT = 0x2;
        /// Xen no advance mapping.
        const NO_ADVANCE_MAP = 0x8;
        /// All valid mappings.
        const ALL = Self::FOREIGN.bits() | Self::GRANT.bits();
    }
}

impl MmapXenFlags {
    /// Mmap flags are valid.
    pub fn is_valid(&self) -> bool {
        // only one of unix, foreign or grant should be set and mmap_in_advance() should be true
        // with foreign and unix.
        if self.is_grant() {
            !self.is_foreign()
        } else if self.is_foreign() || self.is_unix() {
            self.mmap_in_advance()
        } else {
            false
        }
    }

    /// Is standard Unix memory.
    pub fn is_unix(&self) -> bool {
        self.bits() == Self::UNIX.bits()
    }

    /// Is xen foreign memory.
    pub fn is_foreign(&self) -> bool {
        self.contains(Self::FOREIGN)
    }

    /// Is xen grant memory.
    pub fn is_grant(&self) -> bool {
        self.contains(Self::GRANT)
    }

    /// Can mmap entire region in advance.
    pub fn mmap_in_advance(&self) -> bool {
        !self.contains(Self::NO_ADVANCE_MAP)
    }
}

fn page_size() -> u64 {
    // SAFETY: Safe because this call just returns the page size and doesn't have any side effects.
    unsafe { libc::sysconf(_SC_PAGESIZE) as u64 }
}

fn pages(size: usize) -> (usize, usize) {
    let page_size = page_size() as usize;
    let num = size.div_ceil(page_size);

    (num, page_size * num)
}

fn validate_file(file_offset: Option<FileOffset>) -> Result<FileOffset> {
    let file_offset = match file_offset {
        Some(f) => f,
        None => return Err(Error::InvalidFileOffset),
    };

    // We don't allow file offsets with Xen foreign mappings.
    if file_offset.start() != 0 {
        return Err(Error::InvalidFileOffset);
    }

    Ok(file_offset)
}

// Xen Foreign memory mapping interface.
trait MmapXenTrait: std::fmt::Debug {
    fn mmap_slice(&self, addr: *const u8, prot: i32, len: usize) -> Result<MmapXenSlice>;
    fn addr(&self) -> *mut u8;
    fn guest_base(&self) -> GuestAddress;
}

// Standard Unix memory mapping for testing other crates.
#[derive(Clone, Debug)]
struct MmapXenUnix(MmapUnix, GuestAddress);

impl MmapXenUnix {
    fn new(range: &MmapRange) -> Result<Self> {
        let mut builder = MmapRegionBuilder::new(range.size)
            .with_mmap_prot(range.prot.ok_or(Error::Unexpected)?)
            .with_mmap_flags(range.flags.ok_or(Error::Unexpected)?);

        if let Some(ref file_offset) = range.file_offset {
            builder = builder.with_file_offset(file_offset.clone());
        }

        let mmap_unix = builder.build()?;

        Ok(MmapXenUnix(mmap_unix, range.addr))
    }
}

impl MmapXenTrait for MmapXenUnix {
    #[allow(unused_variables)]
    fn mmap_slice(&self, addr: *const u8, prot: i32, len: usize) -> Result<MmapXenSlice> {
        Err(Error::MappedInAdvance)
    }

    fn addr(&self) -> *mut u8 {
        self.0.as_ptr()
    }

    fn guest_base(&self) -> GuestAddress {
        self.1
    }
}

// Privcmd mmap batch v2 command
//
// include/uapi/xen/privcmd.h: `privcmd_mmapbatch_v2`
#[repr(C)]
#[derive(Debug, Copy, Clone)]
struct PrivCmdMmapBatchV2 {
    // number of pages to populate
    num: u32,
    // target domain
    domid: u16,
    // virtual address
    addr: *mut c_void,
    // array of mfns
    arr: *const u64,
    // array of error codes
    err: *mut c_int,
}

const XEN_PRIVCMD_TYPE: u32 = 'P' as u32;

// #define IOCTL_PRIVCMD_MMAPBATCH_V2 _IOC(_IOC_NONE, 'P', 4, sizeof(privcmd_mmapbatch_v2_t))
fn ioctl_privcmd_mmapbatch_v2() -> c_ulong {
    ioctl_expr(
        _IOC_NONE,
        XEN_PRIVCMD_TYPE,
        4,
        size_of::<PrivCmdMmapBatchV2>() as u32,
    )
}

// Xen foreign memory specific implementation.
#[derive(Clone, Debug)]
struct MmapXenForeign {
    domid: u32,
    guest_base: GuestAddress,
    unix_mmap: MmapUnix,
    fd: i32,
}

impl AsRawFd for MmapXenForeign {
    fn as_raw_fd(&self) -> i32 {
        self.fd
    }
}

impl MmapXenForeign {
    fn new(range: &MmapRange) -> Result<Self> {
        let (count, size) = pages(range.size);
        let file_offset = validate_file(range.file_offset.clone())?;
        let fd = file_offset.file().as_raw_fd();

        let unix_mmap = MmapRegionBuilder::new(size)
            .with_mmap_prot(range.prot.ok_or(Error::Unexpected)?)
            .with_mmap_flags(range.flags.ok_or(Error::Unexpected)? | MAP_SHARED)
            .with_file_offset(file_offset)
            .build()?;

        let foreign = Self {
            domid: range.mmap_data,
            guest_base: range.addr,
            unix_mmap,
            fd,
        };

        foreign.mmap_ioctl(count)?;
        Ok(foreign)
    }

    // Ioctl to pass additional information to mmap infrastructure of privcmd driver.
    fn mmap_ioctl(&self, count: usize) -> Result<()> {
        let base = self.guest_base.0 / page_size();

        let mut pfn = Vec::with_capacity(count);
        for i in 0..count {
            pfn.push(base + i as u64);
        }

        let mut err: Vec<c_int> = vec![0; count];

        let map = PrivCmdMmapBatchV2 {
            num: count as u32,
            domid: self.domid as u16,
            addr: self.addr() as *mut c_void,
            arr: pfn.as_ptr(),
            err: err.as_mut_ptr(),
        };

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond `map`.
        let ret = unsafe { ioctl_with_ref(self, ioctl_privcmd_mmapbatch_v2(), &map) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }
}

impl MmapXenTrait for MmapXenForeign {
    #[allow(unused_variables)]
    fn mmap_slice(&self, addr: *const u8, prot: i32, len: usize) -> Result<MmapXenSlice> {
        Err(Error::MappedInAdvance)
    }

    fn addr(&self) -> *mut u8 {
        self.unix_mmap.as_ptr()
    }

    fn guest_base(&self) -> GuestAddress {
        self.guest_base
    }
}

// Xen Grant memory mapping interface.

const XEN_GRANT_ADDR_OFF: u64 = 1 << 63;

// Grant reference
//
// include/uapi/xen/gntdev.h: `ioctl_gntdev_grant_ref`
#[repr(C)]
#[derive(Copy, Clone, Debug, Default, PartialEq)]
struct GntDevGrantRef {
    // The domain ID of the grant to be mapped.
    domid: u32,
    // The grant reference of the grant to be mapped.
    reference: u32,
}

#[repr(C)]
#[derive(Debug, Default, PartialEq, Eq)]
struct __IncompleteArrayField<T>(::std::marker::PhantomData<T>, [T; 0]);
impl<T> __IncompleteArrayField<T> {
    #[inline]
    unsafe fn as_ptr(&self) -> *const T {
        self as *const __IncompleteArrayField<T> as *const T
    }
    #[inline]
    unsafe fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut __IncompleteArrayField<T> as *mut T
    }
    #[inline]
    unsafe fn as_slice(&self, len: usize) -> &[T] {
        ::std::slice::from_raw_parts(self.as_ptr(), len)
    }
    #[inline]
    unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [T] {
        ::std::slice::from_raw_parts_mut(self.as_mut_ptr(), len)
    }
}

// Grant dev mapping reference
//
// include/uapi/xen/gntdev.h: `ioctl_gntdev_map_grant_ref`
#[repr(C)]
#[derive(Debug, Default)]
struct GntDevMapGrantRef {
    // The number of grants to be mapped.
    count: u32,
    // Unused padding
    pad: u32,
    // The offset to be used on a subsequent call to mmap().
    index: u64,
    // Array of grant references, of size @count.
    refs: __IncompleteArrayField<GntDevGrantRef>,
}

generate_fam_struct_impl!(
    GntDevMapGrantRef,
    GntDevGrantRef,
    refs,
    u32,
    count,
    usize::MAX
);

type GntDevMapGrantRefWrapper = FamStructWrapper<GntDevMapGrantRef>;

impl GntDevMapGrantRef {
    fn new(domid: u32, base: u32, count: usize) -> Result<GntDevMapGrantRefWrapper> {
        let mut wrapper = GntDevMapGrantRefWrapper::new(count).map_err(Error::Fam)?;
        let refs = wrapper.as_mut_slice();

        // GntDevMapGrantRef's pad and index are initialized to 0 by Fam layer.
        for (i, r) in refs.iter_mut().enumerate().take(count) {
            r.domid = domid;
            r.reference = base + i as u32;
        }

        Ok(wrapper)
    }
}

// Grant dev un-mapping reference
//
// include/uapi/xen/gntdev.h: `ioctl_gntdev_unmap_grant_ref`
#[repr(C)]
#[derive(Debug, Copy, Clone)]
struct GntDevUnmapGrantRef {
    // The offset returned by the map operation.
    index: u64,
    // The number of grants to be unmapped.
    count: u32,
    // Unused padding
    pad: u32,
}

impl GntDevUnmapGrantRef {
    fn new(index: u64, count: u32) -> Self {
        Self {
            index,
            count,
            pad: 0,
        }
    }
}

const XEN_GNTDEV_TYPE: u32 = 'G' as u32;

// #define IOCTL_GNTDEV_MAP_GRANT_REF _IOC(_IOC_NONE, 'G', 0, sizeof(ioctl_gntdev_map_grant_ref))
fn ioctl_gntdev_map_grant_ref() -> c_ulong {
    ioctl_expr(
        _IOC_NONE,
        XEN_GNTDEV_TYPE,
        0,
        (size_of::<GntDevMapGrantRef>() + size_of::<GntDevGrantRef>()) as u32,
    )
}

// #define IOCTL_GNTDEV_UNMAP_GRANT_REF _IOC(_IOC_NONE, 'G', 1, sizeof(struct ioctl_gntdev_unmap_grant_ref))
fn ioctl_gntdev_unmap_grant_ref() -> c_ulong {
    ioctl_expr(
        _IOC_NONE,
        XEN_GNTDEV_TYPE,
        1,
        size_of::<GntDevUnmapGrantRef>() as u32,
    )
}

// Xen grant memory specific implementation.
#[derive(Clone, Debug)]
struct MmapXenGrant {
    guest_base: GuestAddress,
    unix_mmap: Option<MmapUnix>,
    file_offset: FileOffset,
    flags: i32,
    size: usize,
    index: u64,
    domid: u32,
}

impl AsRawFd for MmapXenGrant {
    fn as_raw_fd(&self) -> i32 {
        self.file_offset.file().as_raw_fd()
    }
}

impl MmapXenGrant {
    fn new(range: &MmapRange, mmap_flags: MmapXenFlags) -> Result<Self> {
        let file_offset = validate_file(range.file_offset.clone())?;

        let mut grant = Self {
            guest_base: range.addr,
            unix_mmap: None,
            file_offset,
            flags: range.flags.ok_or(Error::Unexpected)?,
            size: 0,
            index: 0,
            domid: range.mmap_data,
        };

        // Region can't be mapped in advance, partial mapping will be done later via
        // `MmapXenSlice`.
        if mmap_flags.mmap_in_advance() {
            let (unix_mmap, index) =
                grant.mmap_range(range.addr, range.size, range.prot.ok_or(Error::Unexpected)?)?;

            grant.unix_mmap = Some(unix_mmap);
            grant.index = index;
            grant.size = range.size;
        }

        Ok(grant)
    }

    fn mmap_range(&self, addr: GuestAddress, size: usize, prot: i32) -> Result<(MmapUnix, u64)> {
        let (count, size) = pages(size);
        let index = self.mmap_ioctl(addr, count)?;

        let unix_mmap = MmapRegionBuilder::new(size)
            .with_mmap_prot(prot)
            .with_mmap_flags(self.flags)
            .with_file_offset(FileOffset::from_arc(
                Arc::clone(self.file_offset.arc()),
                index,
            ))
            .build()?;

        Ok((unix_mmap, index))
    }

    fn unmap_range(&self, unix_mmap: MmapUnix, size: usize, index: u64) {
        let (count, _) = pages(size);

        // Unmap the address first.
        drop(unix_mmap);
        self.unmap_ioctl(count as u32, index).unwrap();
    }

    fn mmap_ioctl(&self, addr: GuestAddress, count: usize) -> Result<u64> {
        let base = ((addr.0 & !XEN_GRANT_ADDR_OFF) / page_size()) as u32;
        let wrapper = GntDevMapGrantRef::new(self.domid, base, count)?;
        let reference = wrapper.as_fam_struct_ref();

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond reference.
        let ret = unsafe { ioctl_with_ref(self, ioctl_gntdev_map_grant_ref(), reference) };

        if ret == 0 {
            Ok(reference.index)
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }

    fn unmap_ioctl(&self, count: u32, index: u64) -> Result<()> {
        let unmap = GntDevUnmapGrantRef::new(index, count);

        // SAFETY: This is safe because the ioctl guarantees to not access memory beyond unmap.
        let ret = unsafe { ioctl_with_ref(self, ioctl_gntdev_unmap_grant_ref(), &unmap) };

        if ret == 0 {
            Ok(())
        } else {
            Err(Error::Mmap(io::Error::last_os_error()))
        }
    }
}

impl MmapXenTrait for MmapXenGrant {
    // Maps a slice out of the entire region.
    fn mmap_slice(&self, addr: *const u8, prot: i32, len: usize) -> Result<MmapXenSlice> {
        MmapXenSlice::new_with(self.clone(), addr as usize, prot, len)
    }

    fn addr(&self) -> *mut u8 {
        if let Some(ref unix_mmap) = self.unix_mmap {
            unix_mmap.as_ptr()
        } else {
            null_mut()
        }
    }

    fn guest_base(&self) -> GuestAddress {
        self.guest_base
    }
}

impl Drop for MmapXenGrant {
    fn drop(&mut self) {
        if let Some(unix_mmap) = self.unix_mmap.take() {
            self.unmap_range(unix_mmap, self.size, self.index);
        }
    }
}

#[derive(Debug)]
pub(crate) struct MmapXenSlice {
    grant: Option<MmapXenGrant>,
    unix_mmap: Option<MmapUnix>,
    addr: *mut u8,
    size: usize,
    index: u64,
}

impl MmapXenSlice {
    fn raw(addr: *mut u8) -> Self {
        Self {
            grant: None,
            unix_mmap: None,
            addr,
            size: 0,
            index: 0,
        }
    }

    fn new_with(grant: MmapXenGrant, offset: usize, prot: i32, size: usize) -> Result<Self> {
        let page_size = page_size() as usize;
        let page_base: usize = (offset / page_size) * page_size;
        let offset = offset - page_base;
        let size = offset + size;

        let addr = grant.guest_base.0 + page_base as u64;
        let (unix_mmap, index) = grant.mmap_range(GuestAddress(addr), size, prot)?;

        // SAFETY: We have already mapped the range including offset.
        let addr = unsafe { unix_mmap.as_ptr().add(offset) };

        Ok(Self {
            grant: Some(grant),
            unix_mmap: Some(unix_mmap),
            addr,
            size,
            index,
        })
    }

    // Mapped address for the region.
    pub(crate) fn addr(&self) -> *mut u8 {
        self.addr
    }
}

impl Drop for MmapXenSlice {
    fn drop(&mut self) {
        // Unmaps memory automatically once this instance goes out of scope.
        if let Some(unix_mmap) = self.unix_mmap.take() {
            self.grant
                .as_ref()
                .unwrap()
                .unmap_range(unix_mmap, self.size, self.index);
        }
    }
}

#[derive(Debug)]
pub struct MmapXen {
    xen_flags: MmapXenFlags,
    domid: u32,
    mmap: Box<dyn MmapXenTrait>,
}

impl MmapXen {
    fn new(range: &MmapRange) -> Result<Self> {
        let xen_flags = match MmapXenFlags::from_bits(range.mmap_flags) {
            Some(flags) => flags,
            None => return Err(Error::MmapFlags(range.mmap_flags)),
        };

        if !xen_flags.is_valid() {
            return Err(Error::MmapFlags(xen_flags.bits()));
        }

        Ok(Self {
            xen_flags,
            domid: range.mmap_data,
            mmap: if xen_flags.is_foreign() {
                Box::new(MmapXenForeign::new(range)?)
            } else if xen_flags.is_grant() {
                Box::new(MmapXenGrant::new(range, xen_flags)?)
            } else {
                Box::new(MmapXenUnix::new(range)?)
            },
        })
    }

    fn addr(&self) -> *mut u8 {
        self.mmap.addr()
    }

    fn flags(&self) -> u32 {
        self.xen_flags.bits()
    }

    fn data(&self) -> u32 {
        self.domid
    }

    fn mmap_in_advance(&self) -> bool {
        self.xen_flags.mmap_in_advance()
    }

    pub(crate) fn mmap(
        mmap_xen: Option<&Self>,
        addr: *mut u8,
        prot: i32,
        len: usize,
    ) -> MmapXenSlice {
        match mmap_xen {
            Some(mmap_xen) => mmap_xen.mmap.mmap_slice(addr, prot, len).unwrap(),
            None => MmapXenSlice::raw(addr),
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]

    use super::*;
    use matches::assert_matches;
    use vmm_sys_util::tempfile::TempFile;

    // Adding a helper method to extract the errno within an Error::Mmap(e), or return a
    // distinctive value when the error is represented by another variant.
    impl Error {
        fn raw_os_error(&self) -> i32 {
            match self {
                Error::Mmap(e) => e.raw_os_error().unwrap(),
                Error::Unix(crate::mmap::unix::Error::Mmap(e)) => e.raw_os_error().unwrap(),
                _ => i32::MIN,
            }
        }
    }

    #[allow(unused_variables)]
    pub unsafe fn ioctl_with_ref<F: AsRawFd, T>(fd: &F, req: c_ulong, arg: &T) -> c_int {
        0
    }

    impl MmapRange {
        fn initialized(is_file: bool) -> Self {
            let file_offset = if is_file {
                Some(FileOffset::new(TempFile::new().unwrap().into_file(), 0))
            } else {
                None
            };

            let mut range = MmapRange::new_unix(0x1000, file_offset, GuestAddress(0x1000));
            range.prot = Some(libc::PROT_READ | libc::PROT_WRITE);
            range.mmap_data = 1;

            range
        }
    }

    impl MmapRegion {
        /// Create an `MmapRegion` with specified `size` at GuestAdress(0)
        pub fn new(size: usize) -> Result<Self> {
            let range = MmapRange::new_unix(size, None, GuestAddress(0));
            Self::from_range(range)
        }
    }

    #[test]
    fn test_mmap_xen_failures() {
        let mut range = MmapRange::initialized(true);
        // Invalid flags
        range.mmap_flags = 16;

        let r = MmapXen::new(&range);
        assert_matches!(r.unwrap_err(), Error::MmapFlags(flags) if flags == range.mmap_flags);

        range.mmap_flags = MmapXenFlags::FOREIGN.bits() | MmapXenFlags::GRANT.bits();
        let r = MmapXen::new(&range);
        assert_matches!(r.unwrap_err(), Error::MmapFlags(flags) if flags == MmapXenFlags::ALL.bits());

        range.mmap_flags = MmapXenFlags::FOREIGN.bits() | MmapXenFlags::NO_ADVANCE_MAP.bits();
        let r = MmapXen::new(&range);
        assert_matches!(r.unwrap_err(), Error::MmapFlags(flags) if flags ==  MmapXenFlags::NO_ADVANCE_MAP.bits() | MmapXenFlags::FOREIGN.bits());
    }

    #[test]
    fn test_mmap_xen_success() {
        let mut range = MmapRange::initialized(true);
        range.mmap_flags = MmapXenFlags::FOREIGN.bits();

        let r = MmapXen::new(&range).unwrap();
        assert_eq!(r.flags(), range.mmap_flags);
        assert_eq!(r.data(), range.mmap_data);
        assert_ne!(r.addr(), null_mut());
        assert!(r.mmap_in_advance());

        range.mmap_flags = MmapXenFlags::GRANT.bits();
        let r = MmapXen::new(&range).unwrap();
        assert_eq!(r.flags(), range.mmap_flags);
        assert_eq!(r.data(), range.mmap_data);
        assert_ne!(r.addr(), null_mut());
        assert!(r.mmap_in_advance());

        range.mmap_flags = MmapXenFlags::GRANT.bits() | MmapXenFlags::NO_ADVANCE_MAP.bits();
        let r = MmapXen::new(&range).unwrap();
        assert_eq!(r.flags(), range.mmap_flags);
        assert_eq!(r.data(), range.mmap_data);
        assert_eq!(r.addr(), null_mut());
        assert!(!r.mmap_in_advance());
    }

    #[test]
    fn test_foreign_map_failure() {
        let mut range = MmapRange::initialized(true);
        range.file_offset = Some(FileOffset::new(TempFile::new().unwrap().into_file(), 0));
        range.prot = None;
        let r = MmapXenForeign::new(&range);
        assert_matches!(r.unwrap_err(), Error::Unexpected);

        let mut range = MmapRange::initialized(true);
        range.flags = None;
        let r = MmapXenForeign::new(&range);
        assert_matches!(r.unwrap_err(), Error::Unexpected);

        let mut range = MmapRange::initialized(true);
        range.file_offset = Some(FileOffset::new(TempFile::new().unwrap().into_file(), 1));
        let r = MmapXenForeign::new(&range);
        assert_matches!(r.unwrap_err(), Error::InvalidFileOffset);

        let mut range = MmapRange::initialized(true);
        range.size = 0;
        let r = MmapXenForeign::new(&range);
        assert_eq!(r.unwrap_err().raw_os_error(), libc::EINVAL);
    }

    #[test]
    fn test_foreign_map_success() {
        let range = MmapRange::initialized(true);
        let r = MmapXenForeign::new(&range).unwrap();
        assert_ne!(r.addr(), null_mut());
        assert_eq!(r.domid, range.mmap_data);
        assert_eq!(r.guest_base, range.addr);
    }

    #[test]
    fn test_grant_map_failure() {
        let mut range = MmapRange::initialized(true);
        range.prot = None;
        let r = MmapXenGrant::new(&range, MmapXenFlags::empty());
        assert_matches!(r.unwrap_err(), Error::Unexpected);

        let mut range = MmapRange::initialized(true);
        range.prot = None;
        // Protection isn't used for no-advance mappings
        MmapXenGrant::new(&range, MmapXenFlags::NO_ADVANCE_MAP).unwrap();

        let mut range = MmapRange::initialized(true);
        range.flags = None;
        let r = MmapXenGrant::new(&range, MmapXenFlags::NO_ADVANCE_MAP);
        assert_matches!(r.unwrap_err(), Error::Unexpected);

        let mut range = MmapRange::initialized(true);
        range.file_offset = Some(FileOffset::new(TempFile::new().unwrap().into_file(), 1));
        let r = MmapXenGrant::new(&range, MmapXenFlags::NO_ADVANCE_MAP);
        assert_matches!(r.unwrap_err(), Error::InvalidFileOffset);

        let mut range = MmapRange::initialized(true);
        range.size = 0;
        let r = MmapXenGrant::new(&range, MmapXenFlags::empty());
        assert_eq!(r.unwrap_err().raw_os_error(), libc::EINVAL);
    }

    #[test]
    fn test_grant_map_success() {
        let range = MmapRange::initialized(true);
        let r = MmapXenGrant::new(&range, MmapXenFlags::NO_ADVANCE_MAP).unwrap();
        assert_eq!(r.addr(), null_mut());
        assert_eq!(r.domid, range.mmap_data);
        assert_eq!(r.guest_base, range.addr);

        let mut range = MmapRange::initialized(true);
        // Size isn't used with no-advance mapping.
        range.size = 0;
        MmapXenGrant::new(&range, MmapXenFlags::NO_ADVANCE_MAP).unwrap();

        let range = MmapRange::initialized(true);
        let r = MmapXenGrant::new(&range, MmapXenFlags::empty()).unwrap();
        assert_ne!(r.addr(), null_mut());
        assert_eq!(r.domid, range.mmap_data);
        assert_eq!(r.guest_base, range.addr);
    }

    #[test]
    fn test_grant_ref_alloc() {
        let wrapper = GntDevMapGrantRef::new(0, 0x1000, 0x100).unwrap();
        let r = wrapper.as_fam_struct_ref();
        assert_eq!(r.count, 0x100);
        assert_eq!(r.pad, 0);
        assert_eq!(r.index, 0);
    }
}
