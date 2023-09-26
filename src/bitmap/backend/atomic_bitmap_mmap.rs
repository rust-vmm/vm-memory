// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

use crate::bitmap::{Bitmap, BitmapSlice, WithBitmapSlice};
use crate::mmap::{BitmapMmap, BitmapReplace, NewBitmap};
use crate::{Address, GuestAddress, GuestUsize};
use std::ops::Index;
use std::os::fd::{AsRawFd, BorrowedFd};
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, RwLock};
use std::{io, ptr};

// Size in bytes of the `VHOST_LOG_PAGE`
const LOG_PAGE_SIZE: usize = 0x1000;
// Number of bits in an AtomicU8
const LOG_BLOCK_SIZE: usize = 8;

/// `RegionBitmap` implements a bitmap tha can be replaced at runtime.
/// The main use case is to support live migration on vhost-user backends
/// (see `VHOST_USER_PROTOCOL_F_LOG_SHMFD` and `VHOST_USER_SET_LOG_BASE` in the vhost-user protocol
/// specification). It uses a fixed memory page size of `VHOST_LOG_PAGE` bytes (i.e., `4096` bytes),
/// so it converts addresses to page numbers before setting or clearing the bits.
///
/// Note:
/// This implementation uses `std::sync::RwLock`, the priority policy of the lock is dependent on
/// the underlying operating system's implementation and does not guarantee any particular policy,
/// in systems other than linux a thread trying to acquire the lock may starve.
#[derive(Default, Debug, Clone)]
pub struct BitmapRegion {
    // To avoid both reader and writer starvation we can replace the `std::sync::RwLock` with
    // `parking_lot::RwLock`.
    inner: Arc<RwLock<Option<AtomicBitmapMmap>>>,
    base_address: usize, // The slice's base address
}

impl Bitmap for BitmapRegion {
    fn mark_dirty(&self, offset: usize, len: usize) {
        let inner = self.inner.read().unwrap();
        if let Some(bitmap) = inner.as_ref() {
            bitmap.mark_dirty(self.base_address.wrapping_add(offset), len);
        }
    }

    fn dirty_at(&self, offset: usize) -> bool {
        let inner = self.inner.read().unwrap();
        let Some(bitmap) = inner.as_ref() else {
            return false;
        };

        bitmap.dirty_at(self.base_address.wrapping_add(offset))
    }

    fn slice_at(&self, offset: usize) -> <Self as WithBitmapSlice>::S {
        Self {
            inner: self.inner.clone(),
            base_address: self.base_address.wrapping_add(offset),
        }
    }
}

impl BitmapReplace for BitmapRegion {
    type InnerBitmap = AtomicBitmapMmap;

    fn replace(&self, bitmap: AtomicBitmapMmap) {
        let mut inner = self.inner.write().unwrap();
        inner.replace(bitmap);
    }
}

impl BitmapSlice for BitmapRegion {}

impl<'a> WithBitmapSlice<'a> for BitmapRegion {
    type S = Self;
}

impl NewBitmap for BitmapRegion {
    fn with_len(_len: usize) -> Self {
        Self::default()
    }
}

/// `AtomicBitmapMmap` implements a simple memory-mapped bitmap on the page level with test
/// and set operations. The main use case is to support live migration on vhost-user backends
/// (see `VHOST_USER_PROTOCOL_F_LOG_SHMFD` and `VHOST_USER_SET_LOG_BASE` in the vhost-user protocol
/// specification). It uses a fixed memory page size of `LOG_PAGE_SIZE` bytes, so it converts
/// addresses to page numbers before setting or clearing the bits.
#[derive(Debug)]
pub struct AtomicBitmapMmap {
    logmem: MmapLogReg,
    pages_before_region: usize, // Number of pages to ignore from the start of the bitmap
    number_of_pages: usize,     // Number of total pages indexed in the bitmap for this region
}

// `AtomicBitmapMmap` implements a simple bitmap, it is page-size aware and relative
// to a memory region. It  handling the `log` memory mapped area. Each page is indexed
// inside a block of `LOG_BLOCK_SIZE` bits, so even if the bitmap starts at the beginning of
// the mapped area, the memory region does not necessarily have to start at the beginning of
// that block.
// Note: we don't implement `Bitmap` because we cannot implement `slice_at()`
impl AtomicBitmapMmap {
    // Sets the memory range as dirty. The `offset` is relative to the memory region,
    // so an offset of `0` references the start of the memory region. Any attempt to
    // access beyond the end of the bitmap are simply ignored.
    fn mark_dirty(&self, offset: usize, len: usize) {
        if len == 0 {
            return;
        }

        let first_page = page_number(offset);
        let last_page = page_number(offset.saturating_add(len - 1));
        for page in first_page..=last_page {
            if page >= self.number_of_pages {
                break; // ignore out of bound access
            }

            // get the absolute page number
            let page = self.pages_before_region + page;
            self.logmem[page_block(page)].fetch_or(1 << page_bit(page), Ordering::SeqCst);
        }
    }

    // Check whether the specified offset is marked as dirty. The `offset` is relative
    // to the mery region so and offset of `0` references the start of the memory region.
    // Any attempt to access beyond the end of the bitmap are simply ignored.
    fn dirty_at(&self, offset: usize) -> bool {
        let page = page_number(offset);
        if page >= self.number_of_pages {
            return false; // ignore out of bound access
        }

        // get the absolute page number
        let page = self.pages_before_region + page;
        let page_bit = self.logmem[page_block(page)].load(Ordering::SeqCst) & (1 << page_bit(page));
        page_bit != 0
    }
}

impl BitmapMmap for AtomicBitmapMmap {
    /// Creates a new memory-mapped bitmap for the region of size `region_len` starting at
    /// the `region_start_addr` memory address. This bitmap must fit within the mapped
    /// memory of size `size` bytes starting at offset `offset` in the file referred to by
    /// the file descriptor `fd`.
    fn from_file(
        region_start_addr: GuestAddress,
        region_len: GuestUsize,
        fd: BorrowedFd,
        offset: u64,
        len: u64,
    ) -> io::Result<Self> {
        let region_start_addr: usize = try_into(region_start_addr.raw_value())?;
        let region_len: usize = try_into(region_len)?;
        let offset: isize = try_into(offset)?;
        let len: usize = try_into(len)?;

        // The size of the log should be large enough to cover all known guest addresses.
        let region_end_addr = region_start_addr
            .checked_add(region_len - 1)
            .ok_or(io::Error::from(io::ErrorKind::InvalidData))?;
        let region_end_log_block = addr_block(region_end_addr);
        if region_end_log_block >= len {
            return Err(io::Error::from(io::ErrorKind::InvalidData));
        }

        // Note: We could try to adjust the mapping area to only cover the memory region, but
        // the region's starting address is not guarantee to be LOG_BLOCK_SIZE-page aligned
        // which makes the implementation needlessly cumbersome.
        // Note: The specification does not define whether the offset must be page-aligned or not.
        // But, since we are receiving the offset from the frontend to be used to call mmap,
        // we assume it is properly aligned (currently, qemu always send a 0 offset).
        let logmem = MmapLogReg::from_file(fd, offset, len)?;

        // We need to check that `log.as_ptr().offset(len)` doesn't wrap around and is
        // contained within the mapped memory region.
        check_pointer_offset(logmem.base_ptr(), len)?;

        // The frontend sends a single bitmap (i.e., the log memory to be mapped using `fd`,
        // `mmap_offset` and `mmap_size`) that covers the entire guest memory.
        // However, since each memory region requires a bitmap relative to them, we have to
        // adjust the offset and size, in number of pages, of this region.
        let offset_pages = page_number(region_start_addr);
        let size_page = page_number(region_len);

        Ok(Self {
            logmem,
            pages_before_region: offset_pages,
            number_of_pages: size_page,
        })
    }
}

// Just a handy object to manage the RAII of the mmap region.
#[derive(Debug)]
struct MmapLogReg {
    addr: *const AtomicU8,
    len: usize,
}

// SAFETY: Send is not automatically implemented because the raw pointer.
// No one besides `MmapLogReg` has the raw pointer, so we can safely transfer it to another thread.
unsafe impl Send for MmapLogReg {}

// SAFETY: Sync is not automatically implemented because the raw pointer.
// `MmapLogReg` doesn't have any interior mutability and all access to `&AtomicU8`
// are done through atomic operations.
unsafe impl Sync for MmapLogReg {}

impl MmapLogReg {
    fn from_file(fd: BorrowedFd, offset: isize, len: usize) -> io::Result<Self> {
        #[cfg(not(miri))]
        // SAFETY: `fd` is a valid file descriptor and we are not using `libc::MAP_FIXED`.
        let addr = unsafe {
            libc::mmap(
                ptr::null_mut(),
                len as libc::size_t,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                fd.as_raw_fd(),
                offset as libc::off_t,
            )
        };

        #[cfg(not(miri))]
        if addr == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }

        #[cfg(miri)]
        if len == 0 {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }

        // Miri does not support the mmap syscall, so we use rust's allocator for miri tests
        #[cfg(miri)]
        let addr = unsafe {
            std::alloc::alloc_zeroed(std::alloc::Layout::from_size_align(len, 1).unwrap())
        };

        Ok(Self {
            addr: addr as *const AtomicU8,
            len,
        })
    }

    fn base_ptr(&self) -> *const AtomicU8 {
        self.addr
    }
}

impl Index<usize> for MmapLogReg {
    type Output = AtomicU8;

    // It's ok to get a reference to an atomic value.
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.len);
        // Note: Instaed of `&*` we can use `AtomicU8::from_ptr()` as soon it gets stabilized.
        // SAFETY: `self.addr` + `index` doesn't wrap around and is contained within the mapped
        // memory region.
        unsafe { &*self.addr.add(index) }
    }
}

impl Drop for MmapLogReg {
    fn drop(&mut self) {
        // SAFETY: `addr` is non-null and properly aligned, also we are sure that this
        // is the last reference alive and/or we have an exclusive access to this object.
        unsafe {
            #[cfg(not(miri))]
            libc::munmap(self.addr as *mut libc::c_void, self.len as libc::size_t);

            #[cfg(miri)]
            std::alloc::dealloc(
                self.addr as *mut u8,
                std::alloc::Layout::from_size_align(self.len, 1).unwrap(),
            );
        }
    }
}

#[inline]
fn try_into<TI: TryInto<TO>, TO>(val: TI) -> io::Result<TO> {
    val.try_into()
        .map_err(|_| io::Error::from(io::ErrorKind::InvalidData))
}

#[inline]
fn check_pointer_offset(ptr: *const AtomicU8, offset: usize) -> io::Result<()> {
    let offset: isize = try_into(offset)?;
    if ptr as usize > (isize::MAX - offset) as usize {
        return Err(io::Error::from(io::ErrorKind::InvalidData));
    }
    Ok(())
}

#[inline]
// Get the page number corresponding to the address `addr`
fn page_number(addr: usize) -> usize {
    addr / LOG_PAGE_SIZE
}
#[inline]
// Get the block within the bitmap of the page.
// Each page is indexed inside a block of `LOG_BLOCK_SIZE` bits.
fn page_block(page: usize) -> usize {
    page / LOG_BLOCK_SIZE
}

#[inline]
// Get the bit index inside a block of `LOG_BLOCK_SIZE` bits
fn page_bit(page: usize) -> usize {
    page % LOG_BLOCK_SIZE
}
#[inline]
// Get the block within the bitmap of the `addr` memory address
fn addr_block(addr: usize) -> usize {
    page_block(page_number(addr))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use std::os::fd::AsFd;

    use crate::bitmap::tests::{range_is_clean, range_is_dirty};
    use vmm_sys_util::tempfile::TempFile;

    fn tmp_file(len: usize) -> File {
        let mut f = TempFile::new().unwrap().into_file();
        let buf = vec![0; len];
        f.write_all(buf.as_ref()).unwrap();
        f
    }

    fn test_all(b: &BitmapRegion, len: usize) {
        assert!(range_is_clean(b, 0, len), "The bitmap should be clean");

        b.mark_dirty(0, len);
        assert!(range_is_dirty(b, 0, len), "The bitmap should be dirty");
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_region_bigger_than_log() {
        let mmap_offset: u64 = 0;
        let mmap_size = 1; // 8 pages
        let f = tmp_file(mmap_size);

        let region_start_addr = GuestAddress::new(mmap_offset);
        let region_len = LOG_PAGE_SIZE * LOG_BLOCK_SIZE * mmap_size * 2; // 16 pages

        let log = AtomicBitmapMmap::from_file(
            region_start_addr,
            region_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log.is_err());
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_log_and_region_same_size() {
        let mmap_offset: u64 = 0;
        let mmap_size = 4;
        let f = tmp_file(mmap_size);

        let region_start_addr = GuestAddress::new(mmap_offset);
        let region_len = LOG_PAGE_SIZE * LOG_BLOCK_SIZE * mmap_size; // 32 pages

        let bitmap = BitmapRegion::default();
        let log = AtomicBitmapMmap::from_file(
            region_start_addr,
            region_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log.is_ok());
        let log = log.unwrap();

        bitmap.replace(log);

        test_all(&bitmap, region_len);
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_region_smaller_than_log() {
        let mmap_offset: u64 = 0;
        let mmap_size = 4;
        let f = tmp_file(mmap_size);

        let region_start_addr = GuestAddress::new(mmap_offset);
        let region_len = LOG_PAGE_SIZE * LOG_BLOCK_SIZE * mmap_size / 2; // 16 pages

        let bitmap = BitmapRegion::default();
        let log = AtomicBitmapMmap::from_file(
            region_start_addr,
            region_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log.is_ok());
        let log = log.unwrap();

        bitmap.replace(log);

        test_all(&bitmap, region_len);
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_region_smaller_than_one_block() {
        let mmap_offset: u64 = 0;
        let mmap_size = 4;
        let f = tmp_file(mmap_size);

        let region_start_addr = GuestAddress::new(mmap_offset);
        let region_len = LOG_PAGE_SIZE * (LOG_BLOCK_SIZE - 2); // 6 pages

        let bitmap = BitmapRegion::default();
        let log = AtomicBitmapMmap::from_file(
            region_start_addr,
            region_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log.is_ok());
        let log = log.unwrap();

        bitmap.replace(log);

        test_all(&bitmap, region_len);
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_two_regions_overlapping_block_first_dirty() {
        let mmap_offset: u64 = 0;
        let mmap_size = 4;
        let f = tmp_file(mmap_size);

        let region0_start_addr = GuestAddress::new(mmap_offset);
        let region0_len = LOG_PAGE_SIZE * 11;
        let bitmap0 = BitmapRegion::default();
        let log0 = AtomicBitmapMmap::from_file(
            region0_start_addr,
            region0_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log0.is_ok());
        let log0 = log0.unwrap();

        bitmap0.replace(log0);

        let region1_start_addr = GuestAddress::new(mmap_offset + LOG_PAGE_SIZE as u64 * 14);
        let region1_len = LOG_PAGE_SIZE;
        let bitmap1 = BitmapRegion::default();
        let log1 = AtomicBitmapMmap::from_file(
            region1_start_addr,
            region1_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log1.is_ok());
        let log1 = log1.unwrap();

        bitmap1.replace(log1);

        // Both regions should be clean
        assert!(
            range_is_clean(&bitmap0, 0, region0_len),
            "The bitmap0 should be clean"
        );
        assert!(
            range_is_clean(&bitmap1, 0, region1_len),
            "The bitmap1 should be clean"
        );

        // Marking region 0, region 1 should continue be clean
        bitmap0.mark_dirty(0, region0_len);

        assert!(
            range_is_dirty(&bitmap0, 0, region0_len),
            "The bitmap0 should be dirty"
        );
        assert!(
            range_is_clean(&bitmap1, 0, region1_len),
            "The bitmap1 should be clean"
        );
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_two_regions_overlapping_block_second_dirty() {
        let mmap_offset: u64 = 0;
        let mmap_size = 4;
        let f = tmp_file(mmap_size);

        let region0_start_addr = GuestAddress::new(mmap_offset);
        let region0_len = LOG_PAGE_SIZE * 11;
        let bitmap0 = BitmapRegion::default();
        let log0 = AtomicBitmapMmap::from_file(
            region0_start_addr,
            region0_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log0.is_ok());
        let log0 = log0.unwrap();

        bitmap0.replace(log0);

        let region1_start_addr = GuestAddress::new(mmap_offset + LOG_PAGE_SIZE as u64 * 14);
        let region1_len = LOG_PAGE_SIZE;
        let bitmap1 = BitmapRegion::default();
        let log1 = AtomicBitmapMmap::from_file(
            region1_start_addr,
            region1_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log1.is_ok());
        let log1 = log1.unwrap();

        bitmap1.replace(log1);

        // Both regions should be clean
        assert!(
            range_is_clean(&bitmap0, 0, region0_len),
            "The bitmap0 should be clean"
        );
        assert!(
            range_is_clean(&bitmap1, 0, region1_len),
            "The bitmap1 should be clean"
        );

        // Marking region 1, region 0 should continue be clean
        bitmap1.mark_dirty(0, region1_len);

        assert!(
            range_is_dirty(&bitmap1, 0, region1_len),
            "The bitmap0 should be dirty"
        );
        assert!(
            range_is_clean(&bitmap0, 0, region0_len),
            "The bitmap1 should be clean"
        );
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn test_bitmap_region_slice() {
        let mmap_offset: u64 = 0;
        let mmap_size = 4;
        let f = tmp_file(mmap_size);

        let region_start_addr = GuestAddress::new(mmap_offset);
        let region_len = LOG_PAGE_SIZE * LOG_BLOCK_SIZE * mmap_size; // 32 pages

        let bitmap = BitmapRegion::default();
        let log = AtomicBitmapMmap::from_file(
            region_start_addr,
            region_len as u64,
            f.as_fd(),
            mmap_offset,
            mmap_size as u64,
        );
        assert!(log.is_ok());
        let log = log.unwrap();

        bitmap.replace(log);

        assert!(
            range_is_clean(&bitmap, 0, region_len),
            "The bitmap should be clean"
        );

        // Let's get a slice of half the bitmap
        let slice_len = region_len / 2;
        let slice = bitmap.slice_at(slice_len);
        assert!(
            range_is_clean(&slice, 0, slice_len),
            "The slice should be clean"
        );

        slice.mark_dirty(0, slice_len);
        assert!(
            range_is_dirty(&slice, 0, slice_len),
            "The slice should be dirty"
        );
        assert!(
            range_is_clean(&bitmap, 0, slice_len),
            "The first half of the bitmap should be clean"
        );
        assert!(
            range_is_dirty(&bitmap, slice_len, region_len - slice_len),
            "The last half of the bitmap should be dirty"
        );
    }
}
