//! Provides abstractions (often effectively zero-cost) for modeling the alignment
//! of addresses by leveraging the type system.

use std::convert::TryFrom;
use std::fmt::{self, Debug, Formatter};
use std::marker::PhantomData;
use std::mem::align_of;
use std::result;

use crate::Address;

/// Errors related to operations which involve aligned addresses.
#[derive(Debug, PartialEq)]
pub enum AlignmentError {
    /// Misalignment was detected during a conversion.
    Misaligned,
    /// An overflow occurred while computing address values.
    Overflow,
}

// Check whether `addr` is aligned with respect to `T`.
fn check_addr_aligned<Addr: Address, T>(addr: Addr) -> result::Result<(), AlignmentError> {
    // The value returned from `align_of` should fit within an `u8`
    // for the foreseeable future.
    let align = u8::try_from(align_of::<T>()).expect("Unexpected align_of value.");
    let aligned_addr = addr
        .checked_align_up(Addr::V::from(align))
        .ok_or(AlignmentError::Overflow)?;
    if addr == aligned_addr {
        Ok(())
    } else {
        Err(AlignmentError::Misaligned)
    }
}

/// An address that's aligned with respect to `T`.
pub struct Aligned<Addr, T> {
    addr: Addr,
    phantom: PhantomData<*const T>,
}

// Implementing `Clone` and `Copy` manually because deriving them did not work well
// (most likely because `T` does not need to be `Clone`/`Copy` here).
impl<Addr: Clone, T> Clone for Aligned<Addr, T> {
    fn clone(&self) -> Self {
        Self {
            addr: self.addr.clone(),
            phantom: PhantomData,
        }
    }
}

impl<Addr: Copy, T> Copy for Aligned<Addr, T> {}

impl<Addr: Debug, T> Debug for Aligned<Addr, T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "Aligned({:?}, {})", self.addr, align_of::<T>())
    }
}

impl<Addr, T> Aligned<Addr, T> {
    /// Instantiate a new `Aligned` value without checking the alignment.
    ///
    /// # Safety
    ///
    /// The value of `addr` must be aligned with respect to `T`.
    pub unsafe fn new(addr: Addr) -> Self {
        Aligned {
            addr,
            phantom: PhantomData,
        }
    }

    /// Return the inner address value.
    pub fn into(self) -> Addr {
        self.addr
    }

    /// Convert `self` into an `Aligned` value with the specified alignment without
    /// performing any checks.
    ///
    /// # Safety
    ///
    /// The inner address value must be aligned with respect to `U`.
    pub unsafe fn reinterpret<U>(self) -> Aligned<Addr, U> {
        Aligned {
            addr: self.addr,
            phantom: PhantomData,
        }
    }
}

impl<Addr: Address, T> Aligned<Addr, T> {
    /// Attempt to create an `Aligned` value based on `addr`.
    pub fn from_addr(addr: Addr) -> result::Result<Self, AlignmentError> {
        check_addr_aligned::<Addr, T>(addr)?;
        // Safe because we checked the alignment.
        Ok(unsafe { Self::new(addr) })
    }

    /// Attempt to convert `self` into an `Aligned` value with the specified alignment.
    pub fn cast<U>(self) -> result::Result<Aligned<Addr, U>, AlignmentError> {
        // Fast (compile time) conversion path.
        if align_of::<T>() >= align_of::<U>() {
            // Safe because the above inequality holds.
            Ok(unsafe { self.reinterpret::<U>() })
        } else {
            Aligned::from_addr(self.addr)
        }
    }

    /// Attempt to obtain an `Aligned<Addr, U>` after offsetting the current address by `value`.
    pub fn offset<U>(self, value: Addr::V) -> result::Result<Aligned<Addr, U>, AlignmentError> {
        let addr = self
            .addr
            .checked_add(value)
            .ok_or(AlignmentError::Overflow)?;

        // Fast path.
        if align_of::<T>() >= align_of::<U>() {
            // We only need to check if the offset value is aligned here w.r.t. `U`, because we
            // know the  base is aligned based on the condition above. This check can be optimized
            // away in certain conditions (i.e. when `value` is known at compile time).
            check_addr_aligned::<Addr, U>(Addr::new(value))?;

            // Safe because the above checks/conditions ensure `addr` is properly aligned.
            Ok(unsafe { Aligned::new(addr) })
        } else {
            Aligned::from_addr(addr)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::GuestAddress;

    use super::*;

    #[test]
    fn test_check_addr_aligned() {
        assert!(check_addr_aligned::<_, u64>(GuestAddress(0x8)).is_ok());
        assert_eq!(
            check_addr_aligned::<_, u64>(GuestAddress(0x107)).unwrap_err(),
            AlignmentError::Misaligned
        );
        assert_eq!(
            check_addr_aligned::<_, u64>(GuestAddress(std::u64::MAX)).unwrap_err(),
            AlignmentError::Overflow
        );
    }

    #[test]
    fn test_aligned() {
        let guest_addr = GuestAddress(0x100);
        let odd_guest_addr = GuestAddress(0x101);

        let a = unsafe { Aligned::<_, u32>::new(guest_addr) };
        assert_eq!(a.addr, guest_addr);
        assert_eq!(a.into(), guest_addr);

        {
            let b = a.clone();
            assert_eq!(a.addr, b.addr);
        }

        {
            let b = unsafe { a.reinterpret::<i32>() };
            assert_eq!(a.addr, b.addr);
        }

        {
            let b = Aligned::<_, u32>::from_addr(guest_addr).unwrap();
            assert_eq!(b.addr, guest_addr);

            assert_eq!(
                Aligned::<_, u32>::from_addr(odd_guest_addr).unwrap_err(),
                AlignmentError::Misaligned
            );
        }

        {
            let b = a.cast::<u16>().unwrap();
            assert_eq!(a.addr, b.addr);
            // This is ok because, even though `a` is an `Aligned<GuestAddress, u32>`, the
            // inner `addr` value is aligned w.r.t. `u64` as well.
            assert!(a.cast::<u64>().is_ok());

            // Let's also try out an `Aligned<GuestAddress, u32>` that's no longer
            // aligned for `u64`.
            let c = Aligned::<_, u32>::from_addr(GuestAddress(0x4)).unwrap();
            assert_eq!(c.cast::<u64>().unwrap_err(), AlignmentError::Misaligned);
        }

        {
            let u32_offset = 4;
            let b = a.offset::<u32>(u32_offset).unwrap();
            assert_eq!(b.addr, a.addr.unchecked_add(u32_offset));

            assert_eq!(
                a.offset::<u64>(u32_offset).unwrap_err(),
                AlignmentError::Misaligned
            );

            let c = b.offset::<u64>(u32_offset).unwrap();
            assert_eq!(c.addr, b.addr.unchecked_add(u32_offset));
        }
    }
}
