# Changelog
## [Unreleased]

## [v0.8.0]

### Fixed

- [[#190]](https://github.com/rust-vmm/vm-memory/pull/190):
  `VolatileSlice::read/write` when input slice is empty.

## [v0.7.0]

### Changed

- [[#176]](https://github.com/rust-vmm/vm-memory/pull/176): Relax the trait
  bounds of `Bytes` auto impl for `T: GuestMemory`
- [[#178]](https://github.com/rust-vmm/vm-memory/pull/178):
  `MmapRegion::build_raw` no longer requires that the length of the region is a
  multiple of the page size.

## [v0.6.0]

### Added

  - [[#160]](https://github.com/rust-vmm/vm-memory/pull/160): Add `ArcRef` and `AtomicBitmapArc` bitmap
    backend implementations.
  - [[#149]](https://github.com/rust-vmm/vm-memory/issues/149): Implement builder for MmapRegion.
  - [[#140]](https://github.com/rust-vmm/vm-memory/issues/140): Add dirty bitmap tracking abstractions. 

### Deprecated 

  - [[#133]](https://github.com/rust-vmm/vm-memory/issues/8): Deprecate `GuestMemory::with_regions()`,
   `GuestMemory::with_regions_mut()`, `GuestMemory::map_and_fold()`.

## [v0.5.0]

### Added

- [[#8]](https://github.com/rust-vmm/vm-memory/issues/8): Add GuestMemory method to return an Iterator
- [[#120]](https://github.com/rust-vmm/vm-memory/pull/120): Add is_hugetlbfs() to GuestMemoryRegion
- [[#126]](https://github.com/rust-vmm/vm-memory/pull/126): Add VolatileSlice::split_at()
- [[#128]](https://github.com/rust-vmm/vm-memory/pull/128): Add VolatileSlice::subslice()

## [v0.4.0]

### Fixed

- [[#100]](https://github.com/rust-vmm/vm-memory/issues/100): Performance
  degradation after fixing [#95](https://github.com/rust-vmm/vm-memory/pull/95).
- [[#122]](https://github.com/rust-vmm/vm-memory/pull/122): atomic,
  Cargo.toml: Update for arc-swap 1.0.0.

## [v0.3.0]

### Added

- [[#109]](https://github.com/rust-vmm/vm-memory/pull/109): Added `build_raw` to
  `MmapRegion` which can be used to operate on externally created mappings.
- [[#101]](https://github.com/rust-vmm/vm-memory/pull/101): Added `check_range` for
  GuestMemory which could be used to validate a range of guest memory.
- [[#115]](https://github.com/rust-vmm/vm-memory/pull/115): Add methods for atomic
  access to `Bytes`.

### Fixed

- [[#93]](https://github.com/rust-vmm/vm-memory/issues/93): DoS issue when using
  virtio with rust-vmm/vm-memory.
- [[#106]](https://github.com/rust-vmm/vm-memory/issues/106): Asserts trigger
  on zero-length access.  

### Removed

- `integer-atomics` is no longer a distinct feature of the crate.

## [v0.2.0]

### Added

- [[#76]](https://github.com/rust-vmm/vm-memory/issues/76): Added `get_slice` and
  `as_volatile_slice` to `GuestMemoryRegion`.
- [[#82]](https://github.com/rust-vmm/vm-memory/issues/82): Added `Clone` bound
  for `GuestAddressSpace::T`, the return value of `GuestAddressSpace::memory()`.
- [[#88]](https://github.com/rust-vmm/vm-memory/issues/88): Added `as_bytes` for
  `ByteValued` which can be used for reading into POD structures from
  raw bytes.

## [v0.1.0]

### Added

- Added traits for working with VM memory.
- Added a mmap based implemention for the Guest Memory.
