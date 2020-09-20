use std::cmp;
use std::io::{Read, Write};
use std::mem::size_of;
use std::ptr;
use std::result;

use crate::{copy_bytes, ByteValued, Bytes, GuestMemoryError};

// This module contains internal (they don't need to be explicitly brought into scope or otherwise
// acknowledged by consumers of `vm-memory`) helper abstractions which provide a single
// implementation for all related functionality in `vm-memory` right now (for example, all
// types implementing `Bytes` leverage the logic in this file instead of defining their own).
// Moreover, they also offer a simple manner to automatically implement functionality for
// all relevant objects.
//
// Most methods/objects here have `pub` visibility, but the module itself is not public.

pub type Result<T> = result::Result<T, GuestMemoryError>;

// Stands for a contiguous region of host virtual memory.
pub trait HostRegion {
    // The starting address of the region.
    fn as_ptr(&self) -> *mut u8;
    // The legnth of the region.
    fn len(&self) -> usize;

    // Computes the resulting address without checking the addition operation for overflow.
    fn offset_unchecked(&self, offset: usize) -> *mut u8 {
        ((self.as_ptr() as usize) + offset) as *mut u8
    }
}

// Stands for an address space that can be queried whether an access at a given address and
// with a specified length is valid. For example, we can ask a `GuestMemory` object if we can
// read/write a number of bytes starting with some address. The input address depends on the
// implementor, but the output addresses are always host virtual. We leverage the assumption
// that cross region accesses no longer require special handling.
pub trait CheckAccess<A> {
    // Check whether an access starting at `addr` for exactly `len` bytes is valid, and return
    // the starting HVA if successful.
    fn check_access(&self, addr: A, len: usize) -> Result<*mut u8>;

    // Check whether an access starting at `addr` for at most `max_len` bytes is valid, and
    // return the starting HVA and allowed length if successful.
    fn check_partial_access(&self, addr: A, max_len: usize) -> Result<(*mut u8, usize)>;
}

// A type implementing `HostRegion` can be seen as an array of bytes in host virtual memory, so
// we can implement `CheckAccess<usize>` automatically from that perspective (the address is
// basically an offset in this case).
impl<T: HostRegion> CheckAccess<usize> for T {
    fn check_access(&self, offset: usize, len: usize) -> Result<*mut u8> {
        if let Some(end) = offset.checked_add(len) {
            if end <= self.len() {
                // It's ok to use `offset_unchecked` because we previously verified there's
                // no overflow.
                return Ok(self.offset_unchecked(offset));
            }
        }
        Err(GuestMemoryError::InvalidAccess)
    }

    fn check_partial_access(&self, offset: usize, max_len: usize) -> Result<(*mut u8, usize)> {
        if offset <= self.len() {
            if let Some(end) = offset.checked_add(max_len) {
                let min = cmp::min(self.len(), end);
                let access_len = min - offset;
                // It's ok to use `offset_unchecked` because we previously verified there's
                // no overflow.
                return Ok((self.offset_unchecked(offset), access_len));
            }
        }
        Err(GuestMemoryError::InvalidAccess)
    }
}

// Implementing this trait for a type `T` will automatically add a `Bytes` implementation for `T`,
// based on the logic below.
pub trait AutoBytes<A>: CheckAccess<A> {}

// This is an internal helper struct (like the one already existing in `vm-memory`) which can
// be used to do volatile object accesses for addresses which might not be aligned. Working
// with packed objects has quite a number of caveats in Rust, so we don't expose this to the
// outside.
#[repr(packed)]
struct Packed<T>(T);

// Helper function for reading bytes from a `Read` source into a memory location.//
//
// # Safety
//
// The function is safe to call only if (`ptr`, `len`) is valid for writes.
unsafe fn help_read_from<R: Read>(mut src: R, ptr: *mut u8, len: usize) -> Result<usize> {
    // Safe because `ptr` and `len` are valid for writes.
    let dst = std::slice::from_raw_parts_mut(ptr, len);
    let mut total = 0;
    while total < len {
        match src.read(&mut dst[total..len]) {
            Ok(n) => match n {
                0 => return Ok(total),
                _ => total += n,
            },
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(GuestMemoryError::IOError(e)),
        }
    }
    Ok(total)
}

// Helper function for reading bytes from a memory location into a `Write` destination.
//
// # Safety
//
// The function is safe to call only if (`ptr`, `len`) is valid for reads.
unsafe fn help_write_to<W: Write>(ptr: *const u8, mut dst: W, len: usize) -> Result<usize> {
    // Safe because `ptr` and `len` are valid for reads.
    let src = std::slice::from_raw_parts(ptr, len);
    let mut total = 0;
    while total < len {
        match dst.write(&src[total..len]) {
            Ok(n) => match n {
                0 => return Ok(total),
                _ => total += n,
            },
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(GuestMemoryError::IOError(e)),
        }
    }
    Ok(total)
}

// Provides an automatic `Bytes` implementation for `C`, based on `C: CheckAccess<A>` (which
// is implied by `C: AutoBytes<A>`. The reason we define and use `AutoBytes` instead of having
// a `CheckAccess` bound here directly is to avoid generating the implementation unless
// explicitly requested to. The logic defined here will be used by all `Bytes` implementors
// within `vm-memory`.
impl<A, C: AutoBytes<A>> Bytes<A> for C {
    type E = GuestMemoryError;

    // All methods here make extensive use of `CheckAccess`.
    fn write(&self, buf: &[u8], addr: A) -> Result<usize> {
        // A `write` can be partial so we query the validity and allowed length first.
        self.check_partial_access(addr, buf.len())
            .map(|(ptr, len)| {
                // If we get here, `ptr` and `len` have been checked to be valid, so it's
                // safe to proceed with copying the bytes.
                unsafe {
                    copy_bytes(buf.as_ptr(), ptr, len);
                    len
                }
            })
    }

    fn read(&self, buf: &mut [u8], addr: A) -> Result<usize> {
        self.check_partial_access(addr, buf.len())
            .map(|(ptr, len)| {
                // Safe because (`ptr`, `len`) is guaranteed to be valid for access.
                unsafe {
                    copy_bytes(ptr, buf.as_mut_ptr(), len);
                    len
                }
            })
    }

    fn write_slice(&self, buf: &[u8], addr: A) -> Result<()> {
        // The caller wants to write the full contents of the slice, so we use `check_access`
        // with the desired `len`.
        self.check_access(addr, buf.len()).map(|ptr| {
            // Safe because ...
            unsafe { copy_bytes(buf.as_ptr(), ptr, buf.len()) };
        })
    }

    fn read_slice(&self, buf: &mut [u8], addr: A) -> Result<()> {
        self.check_access(addr, buf.len()).map(|ptr| {
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access.
            unsafe { copy_bytes(ptr, buf.as_mut_ptr(), buf.len()) };
        })
    }

    fn write_obj<T: ByteValued>(&self, val: T, addr: A) -> Result<()> {
        // We check for an access equal to the size of the object.
        self.check_access(addr, size_of::<T>()).map(|ptr| {
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access, and
            // passing a `Packed<T>` ensures alignment doesn't matter.
            unsafe { ptr::write_volatile(ptr as *mut Packed<T>, Packed(val)) }
        })
    }

    fn read_obj<T: ByteValued>(&self, addr: A) -> Result<T> {
        self.check_access(addr, size_of::<T>()).map(|ptr| {
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access, and
            // using the `Packed<T>` type ensures alignment doesn't matter.
            unsafe { ptr::read_volatile(ptr as *const Packed<T>).0 }
        })
    }

    fn read_from<R: Read>(&self, addr: A, src: &mut R, count: usize) -> Result<usize> {
        self.check_partial_access(addr, count)
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access.
            .and_then(|(ptr, len)| unsafe { help_read_from(src, ptr, len) })
    }

    fn read_exact_from<R: Read>(&self, addr: A, src: &mut R, count: usize) -> Result<()> {
        self.check_access(addr, count)
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access.
            .and_then(|ptr| unsafe { help_read_from(src, ptr, count) })
            .and_then(|actual_count| {
                if actual_count != count {
                    Err(GuestMemoryError::PartialBuffer {
                        expected: count,
                        completed: actual_count,
                    })
                } else {
                    Ok(())
                }
            })
    }

    fn write_to<W: Write>(&self, addr: A, dst: &mut W, count: usize) -> Result<usize> {
        self.check_partial_access(addr, count)
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access.
            .and_then(|(ptr, len)| unsafe { help_write_to(ptr, dst, len) })
    }

    fn write_all_to<W: Write>(&self, addr: A, dst: &mut W, count: usize) -> Result<()> {
        self.check_access(addr, count)
            // Safe because (`ptr`, `len`) is guaranteed to be valid for access.
            .and_then(|ptr| unsafe { help_write_to(ptr, dst, count) })
            .and_then(|actual_count| {
                if actual_count != count {
                    Err(GuestMemoryError::PartialBuffer {
                        expected: count,
                        completed: actual_count,
                    })
                } else {
                    Ok(())
                }
            })
    }
}
