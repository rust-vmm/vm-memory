// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Traits to track and access the physical memory of the guest.
//!
//! To make the abstraction as generic as possible, all the core traits declared here only define
//! methods to access guest's memory, and never define methods to manage (create, delete, insert,
//! remove etc) guest's memory. This way, the guest memory consumers (virtio device drivers,
//! vhost drivers and boot loaders etc) may be decoupled from the guest memory provider (typically
//! a hypervisor).
//!
//! Traits and Structs
//! - [`GuestAddress`](struct.GuestAddress.html): represents a guest physical address (GPA).
//! - [`MemoryRegionAddress`](struct.MemoryRegionAddress.html): represents an offset inside a
//!   region.
//! - [`GuestMemoryRegion`](trait.GuestMemoryRegion.html): represent a continuous region of guest's
//!   physical memory.
//! - [`GuestMemory`](trait.GuestMemory.html): represent a collection of `GuestMemoryRegion`
//!   objects.
//!   The main responsibilities of the `GuestMemory` trait are:
//!     - hide the detail of accessing guest's physical address.
//!     - map a request address to a `GuestMemoryRegion` object and relay the request to it.
//!     - handle cases where an access request spanning two or more `GuestMemoryRegion` objects.
//!
//! Whenever a collection of `GuestMemoryRegion` objects is mutable,
//! [`GuestAddressSpace`](trait.GuestAddressSpace.html) should be implemented
//! for clients to obtain a [`GuestMemory`] reference or smart pointer.
//!
//! The `GuestMemoryRegion` trait has an associated `B: Bitmap` type which is used to handle
//! dirty bitmap tracking. Backends are free to define the granularity (or whether tracking is
//! actually performed at all). Those that do implement tracking functionality are expected to
//! ensure the correctness of the underlying `Bytes` implementation. The user has to explicitly
//! record (using the handle returned by `GuestRegionMmap::bitmap`) write accesses performed
//! via pointers, references, or slices returned by methods of `GuestMemory`,`GuestMemoryRegion`,
//! `VolatileSlice`, `VolatileRef`, or `VolatileArrayRef`.

use std::convert::From;
use std::fs::File;
use std::io;
use std::iter::FusedIterator;
use std::mem::size_of;
use std::ops::{BitAnd, BitOr, Deref};
use std::rc::Rc;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use crate::address::{Address, AddressValue};
use crate::bitmap::MS;
use crate::bytes::{AtomicAccess, Bytes};
use crate::io::{ReadVolatile, WriteVolatile};
use crate::volatile_memory::{self, VolatileSlice};
use crate::GuestMemoryRegion;

/// Errors associated with handling guest memory accesses.
#[allow(missing_docs)]
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Failure in finding a guest address in any memory regions mapped by this guest.
    #[error("Guest memory error: invalid guest address {}",.0.raw_value())]
    InvalidGuestAddress(GuestAddress),
    /// Couldn't read/write from the given source.
    #[error("Guest memory error: {0}")]
    IOError(io::Error),
    /// Incomplete read or write.
    #[error("Guest memory error: only used {completed} bytes in {expected} long buffer")]
    PartialBuffer { expected: usize, completed: usize },
    /// Requested backend address is out of range.
    #[error("Guest memory error: invalid backend address")]
    InvalidBackendAddress,
    /// Host virtual address not available.
    #[error("Guest memory error: host virtual address not available")]
    HostAddressNotAvailable,
    /// The length returned by the callback passed to `try_access` is outside the address range.
    #[error(
        "The length returned by the callback passed to `try_access` is outside the address range."
    )]
    CallbackOutOfRange,
    /// The address to be read by `try_access` is outside the address range.
    #[error("The address to be read by `try_access` is outside the address range")]
    GuestAddressOverflow,
}

impl From<volatile_memory::Error> for Error {
    fn from(e: volatile_memory::Error) -> Self {
        match e {
            volatile_memory::Error::OutOfBounds { .. } => Error::InvalidBackendAddress,
            volatile_memory::Error::Overflow { .. } => Error::InvalidBackendAddress,
            volatile_memory::Error::TooBig { .. } => Error::InvalidBackendAddress,
            volatile_memory::Error::Misaligned { .. } => Error::InvalidBackendAddress,
            volatile_memory::Error::IOError(e) => Error::IOError(e),
            volatile_memory::Error::PartialBuffer {
                expected,
                completed,
            } => Error::PartialBuffer {
                expected,
                completed,
            },
        }
    }
}

/// Result of guest memory operations.
pub type Result<T> = std::result::Result<T, Error>;

/// Represents a guest physical address (GPA).
///
/// # Notes:
/// On ARM64, a 32-bit hypervisor may be used to support a 64-bit guest. For simplicity,
/// `u64` is used to store the the raw value no matter if the guest a 32-bit or 64-bit virtual
/// machine.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct GuestAddress(pub u64);
impl_address_ops!(GuestAddress, u64);

/// Represents an offset inside a region.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct MemoryRegionAddress(pub u64);
impl_address_ops!(MemoryRegionAddress, u64);

/// Type of the raw value stored in a `GuestAddress` object.
pub type GuestUsize = <GuestAddress as AddressValue>::V;

/// Represents the start point within a `File` that backs a `GuestMemoryRegion`.
#[derive(Clone, Debug)]
pub struct FileOffset {
    file: Arc<File>,
    start: u64,
}

impl FileOffset {
    /// Creates a new `FileOffset` object.
    pub fn new(file: File, start: u64) -> Self {
        FileOffset::from_arc(Arc::new(file), start)
    }

    /// Creates a new `FileOffset` object based on an exiting `Arc<File>`.
    pub fn from_arc(file: Arc<File>, start: u64) -> Self {
        FileOffset { file, start }
    }

    /// Returns a reference to the inner `File` object.
    pub fn file(&self) -> &File {
        self.file.as_ref()
    }

    /// Return a reference to the inner `Arc<File>` object.
    pub fn arc(&self) -> &Arc<File> {
        &self.file
    }

    /// Returns the start offset within the file.
    pub fn start(&self) -> u64 {
        self.start
    }
}

/// `GuestAddressSpace` provides a way to retrieve a `GuestMemory` object.
/// The vm-memory crate already provides trivial implementation for
/// references to `GuestMemory` or reference-counted `GuestMemory` objects,
/// but the trait can also be implemented by any other struct in order
/// to provide temporary access to a snapshot of the memory map.
///
/// In order to support generic mutable memory maps, devices (or other things
/// that access memory) should store the memory as a `GuestAddressSpace<M>`.
/// This example shows that references can also be used as the `GuestAddressSpace`
/// implementation, providing a zero-cost abstraction whenever immutable memory
/// maps are sufficient.
///
/// # Examples (uses the `backend-mmap` and `backend-atomic` features)
///
/// ```
/// # #[cfg(all(feature = "backend-mmap", target_family = "unix"))]
/// # {
/// # use std::sync::Arc;
/// # use vm_memory::{GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryMmap};
/// #
/// pub struct VirtioDevice<AS: GuestAddressSpace> {
///     mem: Option<AS>,
/// }
///
/// impl<AS: GuestAddressSpace> VirtioDevice<AS> {
///     fn new() -> Self {
///         VirtioDevice { mem: None }
///     }
///     fn activate(&mut self, mem: AS) {
///         self.mem = Some(mem)
///     }
/// }
///
/// fn get_mmap() -> GuestMemoryMmap<()> {
///     let start_addr = GuestAddress(0x1000);
///     GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)])
///         .expect("Could not create guest memory")
/// }
///
/// // Using `VirtioDevice` with an immutable GuestMemoryMmap:
/// let mut for_immutable_mmap = VirtioDevice::<&GuestMemoryMmap<()>>::new();
/// let mmap = get_mmap();
/// for_immutable_mmap.activate(&mmap);
/// let mut another = VirtioDevice::<&GuestMemoryMmap<()>>::new();
/// another.activate(&mmap);
///
/// # #[cfg(feature = "backend-atomic")]
/// # {
/// # use vm_memory::GuestMemoryAtomic;
/// // Using `VirtioDevice` with a mutable GuestMemoryMmap:
/// let mut for_mutable_mmap = VirtioDevice::<GuestMemoryAtomic<GuestMemoryMmap<()>>>::new();
/// let atomic = GuestMemoryAtomic::new(get_mmap());
/// for_mutable_mmap.activate(atomic.clone());
/// let mut another = VirtioDevice::<GuestMemoryAtomic<GuestMemoryMmap<()>>>::new();
/// another.activate(atomic.clone());
///
/// // atomic can be modified here...
/// # }
/// # }
/// ```
pub trait GuestAddressSpace: Clone {
    /// The type that will be used to access guest memory.
    type M: GuestMemory;

    /// A type that provides access to the memory.
    type T: Clone + Deref<Target = Self::M>;

    /// Return an object (e.g. a reference or guard) that can be used
    /// to access memory through this address space.  The object provides
    /// a consistent snapshot of the memory map.
    fn memory(&self) -> Self::T;
}

impl<M: GuestMemory> GuestAddressSpace for &M {
    type M = M;
    type T = Self;

    fn memory(&self) -> Self {
        self
    }
}

impl<M: GuestMemory> GuestAddressSpace for Rc<M> {
    type M = M;
    type T = Self;

    fn memory(&self) -> Self {
        self.clone()
    }
}

impl<M: GuestMemory> GuestAddressSpace for Arc<M> {
    type M = M;
    type T = Self;

    fn memory(&self) -> Self {
        self.clone()
    }
}

/// `GuestMemory` represents a container for an *immutable* collection of
/// `GuestMemoryRegion` objects.  `GuestMemory` provides the `Bytes<GuestAddress>`
/// trait to hide the details of accessing guest memory by physical address.
/// Interior mutability is not allowed for implementations of `GuestMemory` so
/// that they always provide a consistent view of the memory map.
///
/// The task of the `GuestMemory` trait are:
/// - map a request address to a `GuestMemoryRegion` object and relay the request to it.
/// - handle cases where an access request spanning two or more `GuestMemoryRegion` objects.
pub trait GuestMemory {
    /// Type of objects hosted by the address space.
    type R: GuestMemoryRegion;

    /// Returns the number of regions in the collection.
    fn num_regions(&self) -> usize {
        self.iter().count()
    }

    /// Returns the region containing the specified address or `None`.
    fn find_region(&self, addr: GuestAddress) -> Option<&Self::R> {
        self.iter()
            .find(|region| addr >= region.start_addr() && addr <= region.last_addr())
    }

    /// Gets an iterator over the entries in the collection.
    ///
    /// # Examples
    ///
    /// * Compute the total size of all memory mappings in KB by iterating over the memory regions
    ///   and dividing their sizes to 1024, then summing up the values in an accumulator. (uses the
    ///   `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(all(feature = "backend-mmap", target_family = "unix"))]
    /// # {
    /// # use vm_memory::{GuestAddress, GuestMemory, GuestMemoryRegion, GuestMemoryMmap};
    /// #
    /// let start_addr1 = GuestAddress(0x0);
    /// let start_addr2 = GuestAddress(0x400);
    /// let gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr1, 1024), (start_addr2, 2048)])
    ///     .expect("Could not create guest memory");
    ///
    /// let total_size = gm
    ///     .iter()
    ///     .map(|region| region.len() / 1024)
    ///     .fold(0, |acc, size| acc + size);
    /// assert_eq!(3, total_size)
    /// # }
    /// ```
    fn iter(&self) -> impl Iterator<Item = &Self::R>;

    /// Returns the maximum (inclusive) address managed by the
    /// [`GuestMemory`](trait.GuestMemory.html).
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(all(feature = "backend-mmap", target_family = "unix"))]
    /// # {
    /// # use vm_memory::{Address, GuestAddress, GuestMemory, GuestMemoryMmap};
    /// #
    /// let start_addr = GuestAddress(0x1000);
    /// let mut gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x400)])
    ///     .expect("Could not create guest memory");
    ///
    /// assert_eq!(start_addr.checked_add(0x3ff), Some(gm.last_addr()));
    /// # }
    /// ```
    fn last_addr(&self) -> GuestAddress {
        self.iter()
            .map(GuestMemoryRegion::last_addr)
            .fold(GuestAddress(0), std::cmp::max)
    }

    /// Tries to convert an absolute address to a relative address within the corresponding region.
    ///
    /// Returns `None` if `addr` isn't present within the memory of the guest.
    fn to_region_addr(&self, addr: GuestAddress) -> Option<(&Self::R, MemoryRegionAddress)> {
        self.find_region(addr)
            .map(|r| (r, r.to_region_addr(addr).unwrap()))
    }

    /// Returns `true` if the given address is present within the memory of the guest.
    fn address_in_range(&self, addr: GuestAddress) -> bool {
        self.find_region(addr).is_some()
    }

    /// Returns the given address if it is present within the memory of the guest.
    fn check_address(&self, addr: GuestAddress) -> Option<GuestAddress> {
        self.find_region(addr).map(|_| addr)
    }

    /// Check whether the range [base, base + len) is valid.
    fn check_range(&self, base: GuestAddress, len: usize) -> bool {
        // get_slices() ensures that if no error happens, the cumulative length of all slices
        // equal `len`.
        self.get_slices(base, len).all(|r| r.is_ok())
    }

    /// Returns the address plus the offset if it is present within the memory of the guest.
    fn checked_offset(&self, base: GuestAddress, offset: usize) -> Option<GuestAddress> {
        base.checked_add(offset as u64)
            .and_then(|addr| self.check_address(addr))
    }

    /// Invokes callback `f` to handle data in the address range `[addr, addr + count)`.
    ///
    /// The address range `[addr, addr + count)` may span more than one
    /// [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object, or even have holes in it.
    /// So [`try_access()`](trait.GuestMemory.html#method.try_access) invokes the callback 'f'
    /// for each [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) object involved and returns:
    /// - the error code returned by the callback 'f'
    /// - the size of the already handled data when encountering the first hole
    /// - the size of the already handled data when the whole range has been handled
    #[deprecated(
        since = "0.17.0",
        note = "supplemented by external iterator `get_slices()`"
    )]
    fn try_access<F>(&self, count: usize, addr: GuestAddress, mut f: F) -> Result<usize>
    where
        F: FnMut(usize, usize, MemoryRegionAddress, &Self::R) -> Result<usize>,
    {
        let mut cur = addr;
        let mut total = 0;
        while let Some(region) = self.find_region(cur) {
            let start = region.to_region_addr(cur).unwrap();
            let cap = region.len() - start.raw_value();
            let len = std::cmp::min(cap, (count - total) as GuestUsize);
            match f(total, len as usize, start, region) {
                // no more data
                Ok(0) => return Ok(total),
                // made some progress
                Ok(len) => {
                    total = match total.checked_add(len) {
                        Some(x) if x < count => x,
                        Some(x) if x == count => return Ok(x),
                        _ => return Err(Error::CallbackOutOfRange),
                    };
                    cur = match cur.overflowing_add(len as GuestUsize) {
                        (x @ GuestAddress(0), _) | (x, false) => x,
                        (_, true) => return Err(Error::GuestAddressOverflow),
                    };
                }
                // error happened
                e => return e,
            }
        }
        if total == 0 {
            Err(Error::InvalidGuestAddress(addr))
        } else {
            Ok(total)
        }
    }

    /// Get the host virtual address corresponding to the guest address.
    ///
    /// Some [`GuestMemory`](trait.GuestMemory.html) implementations, like `GuestMemoryMmap`,
    /// have the capability to mmap the guest address range into virtual address space of the host
    /// for direct access, so the corresponding host virtual address may be passed to other
    /// subsystems.
    ///
    /// # Note
    /// The underlying guest memory is not protected from memory aliasing, which breaks the
    /// Rust memory safety model. It's the caller's responsibility to ensure that there's no
    /// concurrent accesses to the underlying guest memory.
    ///
    /// # Arguments
    /// * `addr` - Guest address to convert.
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(all(feature = "backend-mmap", target_family = "unix"))]
    /// # {
    /// # use vm_memory::{GuestAddress, GuestMemory, GuestMemoryMmap};
    /// #
    /// # let start_addr = GuestAddress(0x1000);
    /// # let mut gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x500)])
    /// #    .expect("Could not create guest memory");
    /// #
    /// let addr = gm
    ///     .get_host_address(GuestAddress(0x1200))
    ///     .expect("Could not get host address");
    /// println!("Host address is {:p}", addr);
    /// # }
    /// ```
    fn get_host_address(&self, addr: GuestAddress) -> Result<*mut u8> {
        self.to_region_addr(addr)
            .ok_or(Error::InvalidGuestAddress(addr))
            .and_then(|(r, addr)| r.get_host_address(addr))
    }

    /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    /// `addr`.
    fn get_slice(&self, addr: GuestAddress, count: usize) -> Result<VolatileSlice<MS<Self>>> {
        self.to_region_addr(addr)
            .ok_or(Error::InvalidGuestAddress(addr))
            .and_then(|(r, addr)| r.get_slice(addr, count))
    }

    /// Returns an iterator over [`VolatileSlice`](struct.VolatileSlice.html)s, together covering
    /// `count` bytes starting at `addr`.
    ///
    /// Iterating in this way is necessary because the given address range may be fragmented across
    /// multiple [`GuestMemoryRegion`]s.
    ///
    /// The iterator’s items are wrapped in [`Result`], i.e. errors are reported on individual
    /// items.  If there is no such error, the cumulative length of all items will be equal to
    /// `count`.  If `count` is 0, an empty iterator will be returned.
    fn get_slices<'a>(
        &'a self,
        addr: GuestAddress,
        count: usize,
    ) -> GuestMemorySliceIterator<'a, Self> {
        GuestMemorySliceIterator {
            mem: self,
            addr,
            count,
        }
    }
}

/// Iterates over [`VolatileSlice`]s that together form a guest memory area.
///
/// Returned by [`GuestMemory::get_slices()`].
#[derive(Debug)]
pub struct GuestMemorySliceIterator<'a, M: GuestMemory + ?Sized> {
    /// Underlying memory
    mem: &'a M,
    /// Next address in the guest memory area
    addr: GuestAddress,
    /// Remaining bytes in the guest memory area
    count: usize,
}

impl<'a, M: GuestMemory + ?Sized> GuestMemorySliceIterator<'a, M> {
    /// Helper function for [`<Self as Iterator>::next()`](GuestMemorySliceIterator::next).
    ///
    /// Get the next slice (i.e. the one starting from `self.addr` with a length up to
    /// `self.count`) and update the internal state.
    ///
    /// # Safety
    ///
    /// This function does not reset to `self.count` to 0 in case of error, i.e. will not stop
    /// iterating.  Actual behavior after an error is ill-defined, so the caller must check the
    /// return value, and in case of an error, reset `self.count` to 0.
    ///
    /// (This is why this function exists, so this resetting can be done in a single central
    /// location.)
    unsafe fn do_next(&mut self) -> Option<Result<VolatileSlice<'a, MS<'a, M>>>> {
        if self.count == 0 {
            return None;
        }

        let Some((region, start)) = self.mem.to_region_addr(self.addr) else {
            return Some(Err(Error::InvalidGuestAddress(self.addr)));
        };

        let cap = region.len() - start.raw_value();
        let len = std::cmp::min(cap as usize, self.count);

        self.count -= len;
        self.addr = match self.addr.overflowing_add(len as GuestUsize) {
            (x @ GuestAddress(0), _) | (x, false) => x,
            (_, true) => return Some(Err(Error::GuestAddressOverflow)),
        };

        Some(region.get_slice(start, len).inspect(|s| {
            assert_eq!(
                s.len(),
                len,
                "get_slice() returned a slice with wrong length"
            )
        }))
    }

    /// Adapts this [`GuestMemorySliceIterator`] to return `None` (e.g. gracefully terminate)
    /// when it encounters an error after successfully producing at least one slice.
    /// Return an error if requesting the first slice returns an error.
    pub fn stop_on_error(self) -> Result<impl Iterator<Item = VolatileSlice<'a, MS<'a, M>>>> {
        let mut peek = self.peekable();
        if let Some(err) = peek.next_if(Result::is_err) {
            return Err(err.unwrap_err());
        }
        Ok(peek.filter_map(Result::ok))
    }
}

impl<'a, M: GuestMemory + ?Sized> Iterator for GuestMemorySliceIterator<'a, M> {
    type Item = Result<VolatileSlice<'a, MS<'a, M>>>;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // We reset `self.count` to 0 on error
        match unsafe { self.do_next() } {
            Some(Ok(slice)) => Some(Ok(slice)),
            other => {
                // On error (or end), reset to 0 so iteration remains stopped
                self.count = 0;
                other
            }
        }
    }
}

/// This iterator continues to return `None` when exhausted.
///
/// [`<Self as Iterator>::next()`](GuestMemorySliceIterator::next) sets `self.count` to 0 when
/// returning `None`, ensuring that it will only return `None` from that point on.
impl<M: GuestMemory + ?Sized> FusedIterator for GuestMemorySliceIterator<'_, M> {}

impl<T: GuestMemory + ?Sized> Bytes<GuestAddress> for T {
    type E = Error;

    fn write(&self, buf: &[u8], addr: GuestAddress) -> Result<usize> {
        self.get_slices(addr, buf.len())
            .stop_on_error()?
            .try_fold(0, |acc, slice| Ok(acc + slice.write(&buf[acc..], 0)?))
    }

    fn read(&self, buf: &mut [u8], addr: GuestAddress) -> Result<usize> {
        self.get_slices(addr, buf.len())
            .stop_on_error()?
            .try_fold(0, |acc, slice| Ok(acc + slice.read(&mut buf[acc..], 0)?))
    }

    /// # Examples
    ///
    /// * Write a slice at guestaddress 0x1000. (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(all(feature = "backend-mmap", target_family = "unix"))]
    /// # {
    /// # use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};
    /// #
    /// # let start_addr = GuestAddress(0x1000);
    /// # let mut gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x400)])
    /// #    .expect("Could not create guest memory");
    /// #
    /// gm.write_slice(&[1, 2, 3, 4, 5], start_addr)
    ///     .expect("Could not write slice to guest memory");
    /// # }
    /// ```
    fn write_slice(&self, buf: &[u8], addr: GuestAddress) -> Result<()> {
        let res = self.write(buf, addr)?;
        if res != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len(),
                completed: res,
            });
        }
        Ok(())
    }

    /// # Examples
    ///
    /// * Read a slice of length 16 at guestaddress 0x1000. (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(all(feature = "backend-mmap", target_family = "unix"))]
    /// # {
    /// # use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};
    /// #
    /// let start_addr = GuestAddress(0x1000);
    /// let mut gm = GuestMemoryMmap::<()>::from_ranges(&vec![(start_addr, 0x400)])
    ///     .expect("Could not create guest memory");
    /// let buf = &mut [0u8; 16];
    ///
    /// gm.read_slice(buf, start_addr)
    ///     .expect("Could not read slice from guest memory");
    /// # }
    /// ```
    fn read_slice(&self, buf: &mut [u8], addr: GuestAddress) -> Result<()> {
        let res = self.read(buf, addr)?;
        if res != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len(),
                completed: res,
            });
        }
        Ok(())
    }

    fn read_volatile_from<F>(&self, addr: GuestAddress, src: &mut F, count: usize) -> Result<usize>
    where
        F: ReadVolatile,
    {
        self.get_slices(addr, count)
            .stop_on_error()?
            .try_fold(0, |acc, slice| {
                Ok(acc + slice.read_volatile_from(0, src, slice.len())?)
            })
    }

    fn read_exact_volatile_from<F>(
        &self,
        addr: GuestAddress,
        src: &mut F,
        count: usize,
    ) -> Result<()>
    where
        F: ReadVolatile,
    {
        let res = self.read_volatile_from(addr, src, count)?;
        if res != count {
            return Err(Error::PartialBuffer {
                expected: count,
                completed: res,
            });
        }
        Ok(())
    }

    fn write_volatile_to<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<usize>
    where
        F: WriteVolatile,
    {
        self.get_slices(addr, count)
            .stop_on_error()?
            .try_fold(0, |acc, slice| {
                // For a non-RAM region, reading could have side effects, so we
                // must use write_all().
                slice.write_all_volatile_to(0, dst, slice.len())?;
                Ok(acc + slice.len())
            })
    }

    fn write_all_volatile_to<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<()>
    where
        F: WriteVolatile,
    {
        let res = self.write_volatile_to(addr, dst, count)?;
        if res != count {
            return Err(Error::PartialBuffer {
                expected: count,
                completed: res,
            });
        }
        Ok(())
    }

    fn store<O: AtomicAccess>(&self, val: O, addr: GuestAddress, order: Ordering) -> Result<()> {
        // No need to check past the first iterator item: It either has the size of `O`, then there
        // can be no further items; or it does not, and then `VolatileSlice::store()` will fail.
        self.get_slices(addr, size_of::<O>())
            .next()
            .unwrap()? // count > 0 never produces an empty iterator
            .store(val, 0, order)
            .map_err(Into::into)
    }

    fn load<O: AtomicAccess>(&self, addr: GuestAddress, order: Ordering) -> Result<O> {
        // No need to check past the first iterator item: It either has the size of `O`, then there
        // can be no further items; or it does not, and then `VolatileSlice::store()` will fail.
        self.get_slices(addr, size_of::<O>())
            .next()
            .unwrap()? // count > 0 never produces an empty iterator
            .load(0, order)
            .map_err(Into::into)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]

    use super::*;
    #[cfg(feature = "backend-mmap")]
    use std::time::{Duration, Instant};

    #[cfg(feature = "backend-mmap")]
    use crate::mmap::tests::AnyBackend;
    #[cfg(feature = "backend-mmap")]
    use crate::ByteValued;
    use vmm_sys_util::tempfile::TempFile;

    #[test]
    fn test_file_offset() {
        let file = TempFile::new().unwrap().into_file();
        let start = 1234;
        let file_offset = FileOffset::new(file, start);
        assert_eq!(file_offset.start(), start);
        assert_eq!(
            file_offset.file() as *const File,
            file_offset.arc().as_ref() as *const File
        );
    }

    #[cfg(feature = "backend-mmap")]
    fn make_image(size: u8) -> Vec<u8> {
        let mut image: Vec<u8> = Vec::with_capacity(size as usize);
        for i in 0..size {
            image.push(i);
        }
        image
    }

    #[test]
    #[cfg(feature = "backend-mmap")]
    fn checked_read_from() {
        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x40);
        for mem in AnyBackend::all(&[(start_addr1, 64, None), (start_addr2, 64, None)]) {
            let image = make_image(0x80);
            let offset = GuestAddress(0x30);
            let count: usize = 0x20;
            assert_eq!(
                0x20_usize,
                mem.read_volatile_from(offset, &mut image.as_slice(), count)
                    .unwrap()
            );
        }
    }

    // Runs the provided closure in a loop, until at least `duration` time units have elapsed.
    #[cfg(feature = "backend-mmap")]
    fn loop_timed<F>(duration: Duration, mut f: F)
    where
        F: FnMut(),
    {
        // We check the time every `CHECK_PERIOD` iterations.
        const CHECK_PERIOD: u64 = 1_000_000;
        let start_time = Instant::now();

        loop {
            for _ in 0..CHECK_PERIOD {
                f();
            }
            if start_time.elapsed() >= duration {
                break;
            }
        }
    }

    // Helper method for the following test. It spawns a writer and a reader thread, which
    // simultaneously try to access an object that is placed at the junction of two memory regions.
    // The part of the object that's continuously accessed is a member of type T. The writer
    // flips all the bits of the member with every write, while the reader checks that every byte
    // has the same value (and thus it did not do a non-atomic access). The test succeeds if
    // no mismatch is detected after performing accesses for a pre-determined amount of time.
    #[cfg(not(miri))] // This test simulates a race condition between guest and vmm
    #[cfg(feature = "backend-mmap")]
    fn non_atomic_access_helper<T>()
    where
        T: ByteValued
            + std::fmt::Debug
            + From<u8>
            + Into<u128>
            + std::ops::Not<Output = T>
            + PartialEq,
    {
        use std::mem;
        use std::thread;

        // A dummy type that's always going to have the same alignment as the first member,
        // and then adds some bytes at the end.
        #[derive(Clone, Copy, Debug, Default, PartialEq)]
        struct Data<T> {
            val: T,
            some_bytes: [u8; 8],
        }

        // Some sanity checks.
        assert_eq!(mem::align_of::<T>(), mem::align_of::<Data<T>>());
        assert_eq!(mem::size_of::<T>(), mem::align_of::<T>());

        // There must be no padding bytes, as otherwise implementing ByteValued is UB
        assert_eq!(mem::size_of::<Data<T>>(), mem::size_of::<T>() + 8);

        unsafe impl<T: ByteValued> ByteValued for Data<T> {}

        // Start of first guest memory region.
        let start = GuestAddress(0);
        let region_len = 1 << 12;

        // The address where we start writing/reading a Data<T> value.
        let data_start = GuestAddress((region_len - mem::size_of::<T>()) as u64);

        for mem in AnyBackend::all(&[
            (start, region_len, None),
            (start.unchecked_add(region_len as u64), region_len, None),
        ]) {
            // Need to clone this and move it into the new thread we create.
            let mem2 = mem.clone();
            // Just some bytes.
            let some_bytes = [1u8, 2, 4, 16, 32, 64, 128, 255];

            let mut data = Data {
                val: T::from(0u8),
                some_bytes,
            };

            // Simple check that cross-region write/read is ok.
            mem.write_obj(data, data_start).unwrap();
            let read_data = mem.read_obj::<Data<T>>(data_start).unwrap();
            assert_eq!(read_data, data);

            let t = thread::spawn(move || {
                let mut count: u64 = 0;

                loop_timed(Duration::from_secs(3), || {
                    let data = mem2.read_obj::<Data<T>>(data_start).unwrap();

                    // Every time data is written to memory by the other thread, the value of
                    // data.val alternates between 0 and T::MAX, so the inner bytes should always
                    // have the same value. If they don't match, it means we read a partial value,
                    // so the access was not atomic.
                    let bytes = data.val.into().to_le_bytes();
                    for i in 1..mem::size_of::<T>() {
                        if bytes[0] != bytes[i] {
                            panic!(
                                "val bytes don't match {:?} after {} iterations",
                                &bytes[..mem::size_of::<T>()],
                                count
                            );
                        }
                    }
                    count += 1;
                });
            });

            // Write the object while flipping the bits of data.val over and over again.
            loop_timed(Duration::from_secs(3), || {
                mem.write_obj(data, data_start).unwrap();
                data.val = !data.val;
            });

            t.join().unwrap()
        }
    }

    #[test]
    #[cfg(not(miri))]
    #[cfg(feature = "backend-mmap")]
    fn test_non_atomic_access() {
        non_atomic_access_helper::<u16>()
    }

    #[test]
    #[cfg(feature = "backend-mmap")]
    fn test_zero_length_accesses() {
        #[derive(Default, Clone, Copy)]
        #[repr(C)]
        struct ZeroSizedStruct {
            dummy: [u32; 0],
        }

        unsafe impl ByteValued for ZeroSizedStruct {}

        let addr = GuestAddress(0x1000);
        for mem in AnyBackend::all(&[(addr, 0x1000, None)]) {
            let obj = ZeroSizedStruct::default();
            let mut image = make_image(0x80);

            assert_eq!(mem.write(&[], addr).unwrap(), 0);
            assert_eq!(mem.read(&mut [], addr).unwrap(), 0);

            assert!(mem.write_slice(&[], addr).is_ok());
            assert!(mem.read_slice(&mut [], addr).is_ok());

            assert!(mem.write_obj(obj, addr).is_ok());
            assert!(mem.read_obj::<ZeroSizedStruct>(addr).is_ok());

            assert_eq!(
                mem.read_volatile_from(addr, &mut image.as_slice(), 0)
                    .unwrap(),
                0
            );

            assert!(mem
                .read_exact_volatile_from(addr, &mut image.as_slice(), 0)
                .is_ok());

            assert_eq!(
                mem.write_volatile_to(addr, &mut image.as_mut_slice(), 0)
                    .unwrap(),
                0
            );

            assert!(mem
                .write_all_volatile_to(addr, &mut image.as_mut_slice(), 0)
                .is_ok());
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    #[cfg(feature = "backend-mmap")]
    fn test_guest_memory_mmap_is_hugetlbfs() {
        let addr = GuestAddress(0x1000);
        for mem in AnyBackend::all(&[(addr, 0x1000, None)]) {
            let r = mem.find_region(addr).unwrap();
            assert_eq!(r.is_hugetlbfs(), None);
        }
    }
}
