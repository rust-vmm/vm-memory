// Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Module containing versions of the standard library's [`Read`] and [`Write`] traits compatible
//! with volatile memory accesses.

use crate::bitmap::BitmapSlice;
use crate::volatile_memory::copy_slice_impl::{copy_from_volatile_slice, copy_to_volatile_slice};
use crate::{VolatileMemoryError, VolatileSlice};
use std::io::ErrorKind;
use std::os::fd::AsRawFd;

/// A version of the standard library's [`Read`] trait that operates on volatile memory instead of
/// slices
///
/// This trait is needed as rust slices (`&[u8]` and `&mut [u8]`) cannot be used when operating on
/// guest memory [1].
///
/// [1]: https://github.com/rust-vmm/vm-memory/pull/217
pub trait ReadVolatile {
    /// Tries to read some bytes into the given [`VolatileSlice`] buffer, returning how many bytes
    /// were read.
    ///
    /// The behavior of implementations should be identical to [`Read::read`]
    fn read_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<usize, VolatileMemoryError>;

    /// Tries to fill the given [`VolatileSlice`] buffer by reading from `self` returning an error
    /// if insufficient bytes could be read.
    ///
    /// The default implementation is identical to that of [`Read::read_exact`]
    fn read_exact_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<(), VolatileMemoryError> {
        // Implementation based on https://github.com/rust-lang/rust/blob/7e7483d26e3cec7a44ef00cf7ae6c9c8c918bec6/library/std/src/io/mod.rs#L465

        let mut partial_buf = buf.offset(0)?;

        while !partial_buf.is_empty() {
            match self.read_volatile(&mut partial_buf) {
                Err(VolatileMemoryError::IOError(err)) if err.kind() == ErrorKind::Interrupted => {
                    continue
                }
                Ok(0) => {
                    return Err(VolatileMemoryError::IOError(std::io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "failed to fill whole buffer",
                    )))
                }
                Ok(bytes_read) => partial_buf = partial_buf.offset(bytes_read)?,
                Err(err) => return Err(err),
            }
        }

        Ok(())
    }
}

/// A version of the standard library's [`Write`] trait that operates on volatile memory instead of
/// slices
///
/// This trait is needed as rust slices (`&[u8]` and `&mut [u8]`) cannot be used when operating on
/// guest memory [1].
///
/// [1]: https://github.com/rust-vmm/vm-memory/pull/217
pub trait WriteVolatile {
    /// Tries to write some bytes from the given [`VolatileSlice`] buffer, returning how many bytes
    /// were written.
    ///
    /// The behavior of implementations should be identical to [`Write::write`]
    fn write_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<usize, VolatileMemoryError>;

    /// Tries write the entire content of the given [`VolatileSlice`] buffer to `self` returning an
    /// error if not all bytes could be written.
    ///
    /// The default implementation is identical to that of [`Write::write_all`]
    fn write_all_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<(), VolatileMemoryError> {
        // Based on https://github.com/rust-lang/rust/blob/7e7483d26e3cec7a44ef00cf7ae6c9c8c918bec6/library/std/src/io/mod.rs#L1570

        let mut partial_buf = buf.offset(0)?;

        while !partial_buf.is_empty() {
            match self.write_volatile(&partial_buf) {
                Err(VolatileMemoryError::IOError(err)) if err.kind() == ErrorKind::Interrupted => {
                    continue
                }
                Ok(0) => {
                    return Err(VolatileMemoryError::IOError(std::io::Error::new(
                        ErrorKind::WriteZero,
                        "failed to write whole buffer",
                    )))
                }
                Ok(bytes_written) => partial_buf = partial_buf.offset(bytes_written)?,
                Err(err) => return Err(err),
            }
        }

        Ok(())
    }
}

// We explicitly implement our traits for [`std::fs::File`] and [`std::os::unix::net::UnixStream`]
// instead of providing blanket implementation for [`AsRawFd`] due to trait coherence limitations: A
// blanket implementation would prevent us from providing implementations for `&mut [u8]` below, as
// "an upstream crate could implement AsRawFd for &mut [u8]`.

macro_rules! impl_read_write_volatile_for_raw_fd {
    ($raw_fd_ty:ty) => {
        impl ReadVolatile for $raw_fd_ty {
            fn read_volatile<B: BitmapSlice>(
                &mut self,
                buf: &mut VolatileSlice<B>,
            ) -> Result<usize, VolatileMemoryError> {
                read_volatile_raw_fd(self, buf)
            }
        }

        impl WriteVolatile for $raw_fd_ty {
            fn write_volatile<B: BitmapSlice>(
                &mut self,
                buf: &VolatileSlice<B>,
            ) -> Result<usize, VolatileMemoryError> {
                write_volatile_raw_fd(self, buf)
            }
        }
    };
}

impl_read_write_volatile_for_raw_fd!(std::fs::File);
impl_read_write_volatile_for_raw_fd!(std::os::unix::net::UnixStream);
impl_read_write_volatile_for_raw_fd!(std::os::fd::OwnedFd);
impl_read_write_volatile_for_raw_fd!(std::os::fd::BorrowedFd<'_>);

/// Tries to do a single `read` syscall on the provided file descriptor, storing the data raed in
/// the given [`VolatileSlice`].
///
/// Returns the numbers of bytes read.
fn read_volatile_raw_fd<Fd: AsRawFd>(
    raw_fd: &mut Fd,
    buf: &mut VolatileSlice<impl BitmapSlice>,
) -> Result<usize, VolatileMemoryError> {
    let fd = raw_fd.as_raw_fd();
    let guard = buf.ptr_guard_mut();

    let dst = guard.as_ptr().cast::<libc::c_void>();

    // SAFETY: We got a valid file descriptor from `AsRawFd`. The memory pointed to by `dst` is
    // valid for writes of length `buf.len() by the invariants upheld by the constructor
    // of `VolatileSlice`.
    let bytes_read = unsafe { libc::read(fd, dst, buf.len()) };

    if bytes_read < 0 {
        // We don't know if a partial read might have happened, so mark everything as dirty
        buf.bitmap().mark_dirty(0, buf.len());

        Err(VolatileMemoryError::IOError(std::io::Error::last_os_error()))
    } else {
        let bytes_read = bytes_read.try_into().unwrap();
        buf.bitmap().mark_dirty(0, bytes_read);
        Ok(bytes_read)
    }
}

/// Tries to do a single `write` syscall on the provided file descriptor, attempting to write the
/// data stored in the given [`VolatileSlice`].
///
/// Returns the numbers of bytes written.
fn write_volatile_raw_fd<Fd: AsRawFd>(
    raw_fd: &mut Fd,
    buf: &VolatileSlice<impl BitmapSlice>,
) -> Result<usize, VolatileMemoryError> {
    let fd = raw_fd.as_raw_fd();
    let guard = buf.ptr_guard();

    let src = guard.as_ptr().cast::<libc::c_void>();

    // SAFETY: We got a valid file descriptor from `AsRawFd`. The memory pointed to by `src` is
    // valid for reads of length `buf.len() by the invariants upheld by the constructor
    // of `VolatileSlice`.
    let bytes_written = unsafe { libc::write(fd, src, buf.len()) };

    if bytes_written < 0 {
        Err(VolatileMemoryError::IOError(std::io::Error::last_os_error()))
    } else {
        Ok(bytes_written.try_into().unwrap())
    }
}

impl WriteVolatile for &mut [u8] {
    fn write_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<usize, VolatileMemoryError> {
        let total = buf.len().min(self.len());
        let src = buf.subslice(0, total)?;

        // SAFETY:
        // We check above that `src` is contiguously allocated memory of length `total <= self.len())`.
        // Furthermore, both src and dst of the call to
        // copy_from_volatile_slice are valid for reads and writes respectively of length `total`
        // since total is the minimum of lengths of the memory areas pointed to. The areas do not
        // overlap, since `dst` is inside guest memory, and buf is a slice (no slices to guest
        // memory are possible without violating rust's aliasing rules).
        let written = unsafe { copy_from_volatile_slice(self.as_mut_ptr(), &src, total) };

        // Advance the slice, just like the stdlib: https://doc.rust-lang.org/src/std/io/impls.rs.html#335
        *self = std::mem::take(self).split_at_mut(written).1;

        Ok(written)
    }

    fn write_all_volatile<B: BitmapSlice>(
        &mut self,
        buf: &VolatileSlice<B>,
    ) -> Result<(), VolatileMemoryError> {
        // Based on https://github.com/rust-lang/rust/blob/f7b831ac8a897273f78b9f47165cf8e54066ce4b/library/std/src/io/impls.rs#L376-L382
        if self.write_volatile(buf)? == buf.len() {
            Ok(())
        } else {
            Err(VolatileMemoryError::IOError(std::io::Error::new(
                ErrorKind::WriteZero,
                "failed to write whole buffer",
            )))
        }
    }
}

impl ReadVolatile for &[u8] {
    fn read_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<usize, VolatileMemoryError> {
        let total = buf.len().min(self.len());
        let dst = buf.subslice(0, total)?;

        // SAFETY:
        // We check above that `dst` is contiguously allocated memory of length `total <= self.len())`.
        // Furthermore, both src and dst of the call to copy_to_volatile_slice are valid for reads
        // and writes respectively of length `total` since total is the minimum of lengths of the
        // memory areas pointed to. The areas do not overlap, since `dst` is inside guest memory,
        // and buf is a slice (no slices to guest memory are possible without violating rust's aliasing rules).
        let read = unsafe { copy_to_volatile_slice(&dst, self.as_ptr(), total) };

        // Advance the slice, just like the stdlib: https://doc.rust-lang.org/src/std/io/impls.rs.html#232-310
        *self = self.split_at(read).1;

        Ok(read)
    }

    fn read_exact_volatile<B: BitmapSlice>(
        &mut self,
        buf: &mut VolatileSlice<B>,
    ) -> Result<(), VolatileMemoryError> {
        // Based on https://github.com/rust-lang/rust/blob/f7b831ac8a897273f78b9f47165cf8e54066ce4b/library/std/src/io/impls.rs#L282-L302
        if buf.len() > self.len() {
            return Err(VolatileMemoryError::IOError(std::io::Error::new(
                ErrorKind::UnexpectedEof,
                "failed to fill whole buffer",
            )));
        }

        self.read_volatile(buf).map(|_| ())
    }
}
