# Changelog 

## [Unreleased]

### Fixed

- [[#106]](https://github.com/rust-vmm/vm-memory/issues/106): Asserts trigger
  on zero-length access.  

### Added

- [[#104]](https://github.com/rust-vmm/vm-memory/pull/104): Add explicit atomic
  and aligned operations to the `Bytes` interface.
- [[#109]](https://github.com/rust-vmm/vm-memory/pull/109): Added `build_raw` to
  `MmapRegion` which can be used to operate on externally created mappings.

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
