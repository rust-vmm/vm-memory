# Changelog 

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
