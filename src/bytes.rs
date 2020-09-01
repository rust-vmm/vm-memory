// Portions Copyright 2019 Red Hat, Inc.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Define the `ByteValued` trait to mark that it is safe to instantiate the struct with random
//! data.

use std::io::{Read, Write};
use std::mem::{align_of, size_of};
use std::ptr;
use std::result::Result;
use std::slice::{from_raw_parts, from_raw_parts_mut};
use std::sync::atomic::Ordering;
use std::sync::atomic::{
    AtomicI16, AtomicI32, AtomicI8, AtomicIsize, AtomicU16, AtomicU32, AtomicU8, AtomicUsize,
};
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use std::sync::atomic::{AtomicI64, AtomicU64};

use crate::align::Aligned;
use crate::{Address, VolatileSlice};

/// Types for which it is safe to initialize from raw data.
///
/// A type `T` is `ByteValued` if and only if it can be initialized by reading its contents from a
/// byte array.  This is generally true for all plain-old-data structs.  It is notably not true for
/// any type that includes a reference.
///
/// Implementing this trait guarantees that it is safe to instantiate the struct with random data.
pub unsafe trait ByteValued: Copy + Default + Send + Sync {
    /// Converts a slice of raw data into a reference of `Self`.
    ///
    /// The value of `data` is not copied. Instead a reference is made from the given slice. The
    /// value of `Self` will depend on the representation of the type in memory, and may change in
    /// an unstable fashion.
    ///
    /// This will return `None` if the length of data does not match the size of `Self`, or if the
    /// data is not aligned for the type of `Self`.
    fn from_slice(data: &[u8]) -> Option<&Self> {
        // Early out to avoid an unneeded `align_to` call.
        if data.len() != size_of::<Self>() {
            return None;
        }

        // Safe because the ByteValued trait asserts any data is valid for this type, and we ensured
        // the size of the pointer's buffer is the correct size. The `align_to` method ensures that
        // we don't have any unaligned references. This aliases a pointer, but because the pointer
        // is from a const slice reference, there are no mutable aliases. Finally, the reference
        // returned can not outlive data because they have equal implicit lifetime constraints.
        match unsafe { data.align_to::<Self>() } {
            ([], [mid], []) => Some(mid),
            _ => None,
        }
    }

    /// Converts a mutable slice of raw data into a mutable reference of `Self`.
    ///
    /// Because `Self` is made from a reference to the mutable slice`, mutations to the returned
    /// reference are immediately reflected in `data`. The value of the returned `Self` will depend
    /// on the representation of the type in memory, and may change in an unstable fashion.
    ///
    /// This will return `None` if the length of data does not match the size of `Self`, or if the
    /// data is not aligned for the type of `Self`.
    fn from_mut_slice(data: &mut [u8]) -> Option<&mut Self> {
        // Early out to avoid an unneeded `align_to_mut` call.
        if data.len() != size_of::<Self>() {
            return None;
        }

        // Safe because the ByteValued trait asserts any data is valid for this type, and we ensured
        // the size of the pointer's buffer is the correct size. The `align_to` method ensures that
        // we don't have any unaligned references. This aliases a pointer, but because the pointer
        // is from a mut slice reference, we borrow the passed in mutable reference. Finally, the
        // reference returned can not outlive data because they have equal implicit lifetime
        // constraints.
        match unsafe { data.align_to_mut::<Self>() } {
            ([], [mid], []) => Some(mid),
            _ => None,
        }
    }

    /// Converts a reference to `self` into a slice of bytes.
    ///
    /// The value of `self` is not copied. Instead, the slice is made from a reference to `self`.
    /// The value of bytes in the returned slice will depend on the representation of the type in
    /// memory, and may change in an unstable fashion.
    fn as_slice(&self) -> &[u8] {
        // Safe because the entire size of self is accessible as bytes because the trait guarantees
        // it. The lifetime of the returned slice is the same as the passed reference, so that no
        // dangling pointers will result from this pointer alias.
        unsafe { from_raw_parts(self as *const Self as *const u8, size_of::<Self>()) }
    }

    /// Converts a mutable reference to `self` into a mutable slice of bytes.
    ///
    /// Because the slice is made from a reference to `self`, mutations to the returned slice are
    /// immediately reflected in `self`. The value of bytes in the returned slice will depend on
    /// the representation of the type in memory, and may change in an unstable fashion.
    fn as_mut_slice(&mut self) -> &mut [u8] {
        // Safe because the entire size of self is accessible as bytes because the trait guarantees
        // it. The trait also guarantees that any combination of bytes is valid for this type, so
        // modifying them in the form of a byte slice is valid. The lifetime of the returned slice
        // is the same as the passed reference, so that no dangling pointers will result from this
        // pointer alias. Although this does alias a mutable pointer, we do so by exclusively
        // borrowing the given mutable reference.
        unsafe { from_raw_parts_mut(self as *mut Self as *mut u8, size_of::<Self>()) }
    }

    /// Converts a mutable reference to `self` into a `VolatileSlice`.  This is
    /// useful because `VolatileSlice` provides a `Bytes<usize>` implementation.
    ///
    /// # Safety
    ///
    /// Unlike most `VolatileMemory` implementation, this method requires an exclusive
    /// reference to `self`; this trivially fulfills `VolatileSlice::new`'s requirement
    /// that all accesses to `self` use volatile accesses (because there can
    /// be no other accesses).
    fn as_bytes(&mut self) -> VolatileSlice {
        unsafe {
            // This is safe because the lifetime is the same as self
            VolatileSlice::new(self as *mut Self as usize as *mut _, size_of::<Self>())
        }
    }

    /// Attempts to reinterpret `self` as a value of type `U`, which is a safe operation
    /// for `ByteValued` types as long as they have the same size. This method is a no-op
    /// if `U` has the same alignment as `Self`.
    fn transmute<U: ByteValued>(&self) -> Option<U> {
        if size_of::<Self>() != size_of::<U>() {
            return None;
        }

        let src = self as *const Self as *const U;

        Some(if align_of::<U>() <= align_of::<Self>() {
            // Safe because `src` is valid for reads, properly aligned, and (trivially)
            // properly initialized.
            unsafe { ptr::read(src) }
        } else {
            // Safe because `src` is valid for reads and (trivially) properly initialized.
            unsafe { ptr::read_unaligned(src) }
        })
    }
}

// All intrinsic types and arrays of intrinsic types are ByteValued. They are just numbers.
macro_rules! byte_valued_array {
    ($T:ty, $($N:expr)+) => {
        $(
            unsafe impl ByteValued for [$T; $N] {}
        )+
    }
}

macro_rules! byte_valued_type {
    ($T:ty) => {
        unsafe impl ByteValued for $T {}
        byte_valued_array! {
            $T,
            0  1  2  3  4  5  6  7  8  9
            10 11 12 13 14 15 16 17 18 19
            20 21 22 23 24 25 26 27 28 29
            30 31 32
        }
    };
}

byte_valued_type!(u8);
byte_valued_type!(u16);
byte_valued_type!(u32);
byte_valued_type!(u64);
byte_valued_type!(usize);
byte_valued_type!(i8);
byte_valued_type!(i16);
byte_valued_type!(i32);
byte_valued_type!(i64);
byte_valued_type!(isize);

/// Objects that implement this trait must consist exclusively of atomic types
/// from [`std::sync::atomic`](https://doc.rust-lang.org/std/sync/atomic/), except for
/// [`AtomicPtr<T>`](https://doc.rust-lang.org/std/sync/atomic/struct.AtomicPtr.html).
pub unsafe trait AtomicInteger: Sync + Send {}

// TODO: Detect availability using #[cfg(target_has_atomic) when it is stabilized.
// Right now we essentially assume we're running on either x86 or Arm (32 or 64 bit). AFAIK,
// Rust starts using additional synchronization primitives to implement atomics when they're
// not natively available, and that doesn't interact safely with how we cast pointers to
// atomic value references. We should be wary of this when looking at a broader range of
// platforms.

unsafe impl AtomicInteger for AtomicI8 {}
unsafe impl AtomicInteger for AtomicI16 {}
unsafe impl AtomicInteger for AtomicI32 {}
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
unsafe impl AtomicInteger for AtomicI64 {}

unsafe impl AtomicInteger for AtomicU8 {}
unsafe impl AtomicInteger for AtomicU16 {}
unsafe impl AtomicInteger for AtomicU32 {}
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
unsafe impl AtomicInteger for AtomicU64 {}

unsafe impl AtomicInteger for AtomicIsize {}
unsafe impl AtomicInteger for AtomicUsize {}

/// A marker trait used to identify types which can be accessed atomically. We need to add some
/// more details here, but one important requirement is for types marked with `AtomicAccess` not
/// to span multiple regions when aligned.
pub unsafe trait AtomicAccess: ByteValued {}

unsafe impl AtomicAccess for u8 {}
unsafe impl AtomicAccess for u16 {}
unsafe impl AtomicAccess for u32 {}
unsafe impl AtomicAccess for usize {}
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
unsafe impl AtomicAccess for u64 {}
unsafe impl AtomicAccess for i8 {}
unsafe impl AtomicAccess for i16 {}
unsafe impl AtomicAccess for i32 {}
unsafe impl AtomicAccess for isize {}
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
unsafe impl AtomicAccess for i64 {}

/// A container to host a range of bytes and access its content.
///
/// Candidates which may implement this trait include:
/// - anonymous memory areas
/// - mmapped memory areas
/// - data files
/// - a proxy to access memory on remote
pub trait Bytes<A: Address> {
    /// Associated error codes
    type E;

    /// Writes a slice into the container at `addr`.
    ///
    /// Returns the number of bytes written. The number of bytes written can
    /// be less than the length of the slice if there isn't enough room in the
    /// container.
    fn write(&self, buf: &[u8], addr: A) -> Result<usize, Self::E>;

    /// Reads data from the container at `addr` into a slice.
    ///
    /// Returns the number of bytes read. The number of bytes read can be less than the length
    /// of the slice if there isn't enough data within the container.
    fn read(&self, buf: &mut [u8], addr: A) -> Result<usize, Self::E>;

    /// Writes the entire content of a slice into the container at `addr`.
    ///
    /// # Errors
    ///
    /// Returns an error if there isn't enough space within the container to write the entire slice.
    /// Part of the data may have been copied nevertheless.
    fn write_slice(&self, buf: &[u8], addr: A) -> Result<(), Self::E>;

    /// Reads data from the container at `addr` to fill an entire slice.
    ///
    /// # Errors
    ///
    /// Returns an error if there isn't enough data within the container to fill the entire slice.
    /// Part of the data may have been copied nevertheless.
    fn read_slice(&self, buf: &mut [u8], addr: A) -> Result<(), Self::E>;

    /// Returns a reference that allows atomic operations for `T` at the specified address.
    fn atomic_ref<T: AtomicInteger>(&self, addr: Aligned<A, T>) -> Result<&T, Self::E>;

    /// Perform an atomic write at the specified address.
    fn write_atomic<T: AtomicAccess>(
        &self,
        val: T,
        addr: Aligned<A, T>,
        order: Ordering,
    ) -> Result<(), Self::E> {
        // This invariant must hold for every type that implements `AtomicAccess`.
        assert_eq!(size_of::<T>(), align_of::<T>());

        match size_of::<T>() {
            // The `addr.cast().unwrap()` and `val.transmute().unwrap()` are both no-ops
            // because we ensure the types have the same size and alignment.
            1 => self
                .atomic_ref::<AtomicU8>(addr.cast().unwrap())?
                .store(val.transmute().unwrap(), order),
            2 => self
                .atomic_ref::<AtomicU16>(addr.cast().unwrap())?
                .store(val.transmute().unwrap(), order),
            4 => self
                .atomic_ref::<AtomicU32>(addr.cast().unwrap())?
                .store(val.transmute().unwrap(), order),
            #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
            8 => self
                .atomic_ref::<AtomicU64>(addr.cast().unwrap())?
                .store(val.transmute().unwrap(), order),
            _ => unreachable!(),
        }

        Ok(())
    }

    /// Perform an atomic read from the specified address.
    fn read_atomic<T: AtomicAccess>(
        &self,
        addr: Aligned<A, T>,
        order: Ordering,
    ) -> Result<T, Self::E> {
        // This invariant must hold for every type that implements `AtomicAccess`.
        assert_eq!(size_of::<T>(), align_of::<T>());

        Ok(match size_of::<T>() {
            // The `addr.cast().unwrap()` and `transmute().unwrap()` are both no-ops
            // because we ensure the types have the same size and alignment.
            1 => self
                .atomic_ref::<AtomicU8>(addr.cast().unwrap())?
                .load(order)
                .transmute()
                .unwrap(),
            2 => self
                .atomic_ref::<AtomicU16>(addr.cast().unwrap())?
                .load(order)
                .transmute()
                .unwrap(),
            4 => self
                .atomic_ref::<AtomicU32>(addr.cast().unwrap())?
                .load(order)
                .transmute()
                .unwrap(),
            #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
            8 => self
                .atomic_ref::<AtomicU64>(addr.cast().unwrap())?
                .load(order)
                .transmute()
                .unwrap(),
            _ => unreachable!(),
        })
    }

    /// Writes an object into the container at `addr`, which is guaranteed to be aligned with
    /// respect to `T`.
    fn write_aligned<T: ByteValued>(&self, val: T, addr: Aligned<A, T>) -> Result<(), Self::E> {
        self.write_obj(val, addr.into())
    }

    /// Reads an object from the container at `addr`, which is guaranteed to be aligned with
    /// respect to `T`.
    fn read_aligned<T: ByteValued>(&self, addr: Aligned<A, T>) -> Result<T, Self::E> {
        self.read_obj(addr.into())
    }

    /// Writes an object into the container at `addr`.
    ///
    /// # Errors
    ///
    /// Returns an error if the object doesn't fit inside the container.
    fn write_obj<T: ByteValued>(&self, val: T, addr: A) -> Result<(), Self::E> {
        self.write_slice(val.as_slice(), addr)
    }

    /// Reads an object from the container at `addr`.
    ///
    /// Reading from a volatile area isn't strictly safe as it could change mid-read.
    /// However, as long as the type T is plain old data and can handle random initialization,
    /// everything will be OK.
    ///
    /// # Errors
    ///
    /// Returns an error if there's not enough data inside the container.
    fn read_obj<T: ByteValued>(&self, addr: A) -> Result<T, Self::E> {
        let mut result: T = Default::default();
        self.read_slice(result.as_mut_slice(), addr).map(|_| result)
    }

    /// Reads up to `count` bytes from an object and writes them into the container at `addr`.
    ///
    /// Returns the number of bytes written into the container.
    ///
    /// # Arguments
    /// * `addr` - Begin writing at this address.
    /// * `src` - Copy from `src` into the container.
    /// * `count` - Copy `count` bytes from `src` into the container.
    fn read_from<F>(&self, addr: A, src: &mut F, count: usize) -> Result<usize, Self::E>
    where
        F: Read;

    /// Reads exactly `count` bytes from an object and writes them into the container at `addr`.
    ///
    /// # Errors
    ///
    /// Returns an error if `count` bytes couldn't have been copied from `src` to the container.
    /// Part of the data may have been copied nevertheless.
    ///
    /// # Arguments
    /// * `addr` - Begin writing at this address.
    /// * `src` - Copy from `src` into the container.
    /// * `count` - Copy exactly `count` bytes from `src` into the container.
    fn read_exact_from<F>(&self, addr: A, src: &mut F, count: usize) -> Result<(), Self::E>
    where
        F: Read;

    /// Reads up to `count` bytes from the container at `addr` and writes them it into an object.
    ///
    /// Returns the number of bytes written into the object.
    ///
    /// # Arguments
    /// * `addr` - Begin reading from this address.
    /// * `dst` - Copy from the container to `dst`.
    /// * `count` - Copy `count` bytes from the container to `dst`.
    fn write_to<F>(&self, addr: A, dst: &mut F, count: usize) -> Result<usize, Self::E>
    where
        F: Write;

    /// Reads exactly `count` bytes from the container at `addr` and writes them into an object.
    ///
    /// # Errors
    ///
    /// Returns an error if `count` bytes couldn't have been copied from the container to `dst`.
    /// Part of the data may have been copied nevertheless.
    ///
    /// # Arguments
    /// * `addr` - Begin reading from this address.
    /// * `dst` - Copy from the container to `dst`.
    /// * `count` - Copy exactly `count` bytes from the container to `dst`.
    fn write_all_to<F>(&self, addr: A, dst: &mut F, count: usize) -> Result<(), Self::E>
    where
        F: Write;
}

#[cfg(test)]
pub(crate) mod tests {
    use std::fmt::Debug;
    use std::io::{Read, Write};
    use std::mem::{align_of, size_of};
    use std::slice;

    use crate::{AddressValue, Aligned, AtomicInteger, ByteValued, Bytes};

    use super::*;

    fn check_byte_valued_type<T>()
    where
        T: ByteValued + PartialEq + Debug + Default,
    {
        let mut data = [0u8; 32];
        let pre_len = {
            let (pre, _, _) = unsafe { data.align_to::<T>() };
            pre.len()
        };
        {
            let aligned_data = &mut data[pre_len..pre_len + size_of::<T>()];
            {
                let mut val: T = Default::default();
                assert_eq!(T::from_slice(aligned_data), Some(&val));
                assert_eq!(T::from_mut_slice(aligned_data), Some(&mut val));
                assert_eq!(val.as_slice(), aligned_data);
                assert_eq!(val.as_mut_slice(), aligned_data);
            }
        }
        for i in 1..size_of::<T>() {
            let begin = pre_len + i;
            let end = begin + size_of::<T>();
            let unaligned_data = &mut data[begin..end];
            {
                if align_of::<T>() != 1 {
                    assert_eq!(T::from_slice(unaligned_data), None);
                    assert_eq!(T::from_mut_slice(unaligned_data), None);
                }
            }
        }
        // Check the early out condition
        {
            assert!(T::from_slice(&data).is_none());
            assert!(T::from_mut_slice(&mut data).is_none());
        }
    }

    #[test]
    fn test_byte_valued() {
        check_byte_valued_type::<u8>();
        check_byte_valued_type::<u16>();
        check_byte_valued_type::<u32>();
        check_byte_valued_type::<u64>();
        check_byte_valued_type::<usize>();
        check_byte_valued_type::<i8>();
        check_byte_valued_type::<i16>();
        check_byte_valued_type::<i32>();
        check_byte_valued_type::<i64>();
        check_byte_valued_type::<isize>();
    }

    pub const MOCK_BYTES_CONTAINER_SIZE: usize = 10;

    pub struct MockBytesContainer {
        container: [u8; MOCK_BYTES_CONTAINER_SIZE],
    }

    impl MockBytesContainer {
        pub fn new() -> Self {
            MockBytesContainer {
                container: [0; MOCK_BYTES_CONTAINER_SIZE],
            }
        }

        pub fn validate_slice_op(&self, buf: &[u8], addr: usize) -> Result<(), ()> {
            if MOCK_BYTES_CONTAINER_SIZE - buf.len() <= addr {
                return Err(());
            }

            Ok(())
        }
    }

    impl Bytes<usize> for MockBytesContainer {
        type E = ();

        fn write(&self, _: &[u8], _: usize) -> Result<usize, Self::E> {
            unimplemented!()
        }

        fn read(&self, _: &mut [u8], _: usize) -> Result<usize, Self::E> {
            unimplemented!()
        }

        fn write_slice(&self, buf: &[u8], addr: usize) -> Result<(), Self::E> {
            self.validate_slice_op(buf, addr)?;

            // We need to get a mut reference to `self.container`.
            let container_ptr = self.container[addr..].as_ptr() as usize as *mut u8;
            let container = unsafe { slice::from_raw_parts_mut(container_ptr, buf.len()) };
            container.copy_from_slice(buf);

            Ok(())
        }

        fn read_slice(&self, buf: &mut [u8], addr: usize) -> Result<(), Self::E> {
            self.validate_slice_op(buf, addr)?;

            buf.copy_from_slice(&self.container[addr..buf.len()]);

            Ok(())
        }

        fn atomic_ref<T: AtomicInteger>(&self, _: Aligned<usize, T>) -> Result<&T, Self::E> {
            unimplemented!()
        }

        fn read_from<F>(&self, _: usize, _: &mut F, _: usize) -> Result<usize, Self::E>
        where
            F: Read,
        {
            unimplemented!()
        }

        fn read_exact_from<F>(&self, _: usize, _: &mut F, _: usize) -> Result<(), Self::E>
        where
            F: Read,
        {
            unimplemented!()
        }

        fn write_to<F>(&self, _: usize, _: &mut F, _: usize) -> Result<usize, Self::E>
        where
            F: Write,
        {
            unimplemented!()
        }

        fn write_all_to<F>(&self, _: usize, _: &mut F, _: usize) -> Result<(), Self::E>
        where
            F: Write,
        {
            unimplemented!()
        }
    }

    // Making this pub to be used by different `Bytes` implementors. It helps testing the
    // `atomic_ref`, `atomic_write`, and `atomic_read` method implementations.
    pub(crate) fn test_atomic_access<A, B>(bytes: &B, addr: A, bad_offset: <A as AddressValue>::V)
    where
        A: Address,
        B: Bytes<A>,
        B::E: Debug,
    {
        let aligned_atomic = Aligned::<A, AtomicU32>::from_addr(addr).unwrap();
        let aligned_u32 = aligned_atomic.cast::<u32>().unwrap();

        let value = 123;
        let another_value = 456;

        bytes
            .atomic_ref(aligned_atomic)
            .unwrap()
            .store(value, Ordering::Relaxed);
        assert_eq!(bytes.read_aligned(aligned_u32).unwrap(), value);

        bytes
            .write_atomic(another_value, aligned_u32, Ordering::Relaxed)
            .unwrap();
        assert_eq!(
            bytes.read_atomic(aligned_u32, Ordering::Relaxed).unwrap(),
            another_value
        );

        // Invalid addresses.
        assert!(bytes
            .atomic_ref(aligned_atomic.offset::<AtomicU32>(bad_offset).unwrap())
            .is_err());

        assert!(bytes
            .write_atomic(
                value,
                aligned_u32.offset(bad_offset).unwrap(),
                Ordering::Relaxed
            )
            .is_err());

        assert!(bytes
            .read_atomic(
                aligned_u32.offset::<u32>(bad_offset).unwrap(),
                Ordering::Relaxed
            )
            .is_err());
    }

    #[test]
    fn test_bytes() {
        let bytes = MockBytesContainer::new();

        assert!(bytes.write_obj(std::u64::MAX, 0).is_ok());
        assert_eq!(bytes.read_obj::<u64>(0).unwrap(), std::u64::MAX);

        assert!(bytes
            .write_obj(std::u64::MAX, MOCK_BYTES_CONTAINER_SIZE)
            .is_err());
        assert!(bytes.read_obj::<u64>(MOCK_BYTES_CONTAINER_SIZE).is_err());
    }

    #[repr(C)]
    #[derive(Copy, Clone, Default)]
    struct S {
        a: u32,
        b: u32,
    }

    unsafe impl ByteValued for S {}

    #[test]
    fn byte_valued_slice() {
        let a: [u8; 8] = [0, 0, 0, 0, 1, 1, 1, 1];
        let mut s: S = Default::default();
        s.as_bytes().copy_from(&a);
        assert_eq!(s.a, 0);
        assert_eq!(s.b, 0x0101_0101);
    }

    #[test]
    fn test_transmute() {
        let a: u64 = 1234;
        let b = a.transmute::<S>().unwrap();

        assert_eq!(a, b.transmute::<u64>().unwrap());
        assert!(a.transmute::<u32>().is_none());
    }
}
