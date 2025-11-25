#![allow(unused_imports)]
pub use vm_memory::Address;
mod address {
    pub use vm_memory::address::Address;
    pub use vm_memory::address::AddressValue;
}
pub use vm_memory::AddressValue;
pub use vm_memory::AtomicAccess;
mod atomic {
    #[cfg(feature = "backend-atomic")]
    pub use vm_memory::atomic::GuestMemoryAtomic;
    #[cfg(feature = "backend-atomic")]
    pub use vm_memory::atomic::GuestMemoryExclusiveGuard;
    #[cfg(feature = "backend-atomic")]
    pub use vm_memory::atomic::GuestMemoryLoadGuard;
}
pub use vm_memory::AtomicInteger;
pub use vm_memory::Be16;
pub use vm_memory::Be32;
pub use vm_memory::Be64;
pub use vm_memory::BeSize;
mod bitmap {
    #[cfg(feature = "backend-bitmap")]
    pub use vm_memory::bitmap::AtomicBitmap;
    pub use vm_memory::bitmap::Bitmap;
    pub use vm_memory::bitmap::BitmapSlice;
    pub use vm_memory::bitmap::NewBitmap;
    pub use vm_memory::bitmap::WithBitmapSlice;
}
pub use vm_memory::Bytes;
mod bytes {
    pub use vm_memory::bytes::AtomicAccess;
    pub use vm_memory::bytes::ByteValued;
    pub use vm_memory::bytes::Bytes;
}
pub use vm_memory::ByteValued;
mod endian {
    pub use vm_memory::endian::Be16;
    pub use vm_memory::endian::Be32;
    pub use vm_memory::endian::Be64;
    pub use vm_memory::endian::BeSize;
    pub use vm_memory::endian::Le16;
    pub use vm_memory::endian::Le32;
    pub use vm_memory::endian::Le64;
    pub use vm_memory::endian::LeSize;
}
pub use vm_memory::FileOffset;
pub use vm_memory::GuestAddress;
pub use vm_memory::GuestAddressSpace;
pub use vm_memory::GuestMemory;
#[cfg(feature = "backend-atomic")]
pub use vm_memory::GuestMemoryAtomic;
pub use vm_memory::GuestMemoryError;
mod guest_memory {
    pub use vm_memory::guest_memory::Error;
    pub use vm_memory::guest_memory::FileOffset;
    pub use vm_memory::guest_memory::GuestAddress;
    pub use vm_memory::guest_memory::GuestAddressSpace;
    pub use vm_memory::guest_memory::GuestMemory;
    pub use vm_memory::guest_memory::GuestMemorySliceIterator;
    pub use vm_memory::guest_memory::MemoryRegionAddress;
}
#[cfg(feature = "backend-atomic")]
pub use vm_memory::GuestMemoryLoadGuard;
pub use vm_memory::GuestMemoryRegion;
pub use vm_memory::GuestMemoryRegionBytes;
pub use vm_memory::GuestRegionCollection;
pub use vm_memory::GuestRegionCollectionError;
#[cfg(feature = "backend-mmap")]
pub use vm_memory::GuestRegionMmap;
mod io {
    pub use vm_memory::io::ReadVolatile;
    pub use vm_memory::io::WriteVolatile;
}
pub use vm_memory::Le16;
pub use vm_memory::Le32;
pub use vm_memory::Le64;
pub use vm_memory::LeSize;
pub use vm_memory::MemoryRegionAddress;
mod mmap {
    #[cfg(feature = "backend-mmap")]
    pub use vm_memory::mmap::FromRangesError;
    #[cfg(feature = "backend-mmap")]
    pub use vm_memory::mmap::GuestRegionMmap;
    #[cfg(all(feature = "backend-mmap", feature = "xen", target_family = "unix"))]
    pub use vm_memory::mmap::MmapRange;
    #[cfg(feature = "backend-mmap")]
    pub use vm_memory::mmap::MmapRegion;
    #[cfg(feature = "backend-mmap")]
    pub use vm_memory::mmap::MmapRegionError;
    #[cfg(all(feature = "backend-mmap", feature = "xen", target_family = "unix"))]
    pub use vm_memory::mmap::MmapXenFlags;
    #[cfg(feature = "backend-mmap")]
    pub use vm_memory::mmap::NewBitmap;
}
#[cfg(all(feature = "backend-mmap", feature = "xen", target_family = "unix"))]
pub use vm_memory::MmapRange;
#[cfg(feature = "backend-mmap")]
pub use vm_memory::MmapRegion;
#[cfg(all(feature = "backend-mmap", feature = "xen", target_family = "unix"))]
pub use vm_memory::MmapXenFlags;
pub use vm_memory::ReadVolatile;
mod region {
    pub use vm_memory::region::GuestMemoryRegion;
    pub use vm_memory::region::GuestMemoryRegionBytes;
    pub use vm_memory::region::GuestRegionCollection;
    pub use vm_memory::region::GuestRegionCollectionError;
}
pub use vm_memory::VolatileArrayRef;
pub use vm_memory::VolatileMemory;
pub use vm_memory::VolatileMemoryError;
mod volatile_memory {
    pub use vm_memory::volatile_memory::Error;
    pub use vm_memory::volatile_memory::PtrGuard;
    pub use vm_memory::volatile_memory::PtrGuardMut;
    pub use vm_memory::volatile_memory::VolatileArrayRef;
    pub use vm_memory::volatile_memory::VolatileMemory;
    pub use vm_memory::volatile_memory::VolatileRef;
    pub use vm_memory::volatile_memory::VolatileSlice;
}
pub use vm_memory::VolatileRef;
pub use vm_memory::VolatileSlice;
pub use vm_memory::WriteVolatile;
