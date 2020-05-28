# [v0.2.1]

## Fixed
- [[#93]](https://github.com/rust-vmm/vm-memory/issues/93): Avoid torn writes
  with memcpy.

# [v0.2.0]

## Added

- [[#76]](https://github.com/rust-vmm/vm-memory/issues/76): Added `get_slice` and
  `as_volatile_slice` to `GuestMemoryRegion`.
- [[#82]](https://github.com/rust-vmm/vm-memory/issues/82): Added `Clone` bound
  for `GuestAddressSpace::T`, the return value of `GuestAddressSpace::memory()`.
- [[#88]](https://github.com/rust-vmm/vm-memory/issues/88): Added `as_bytes` for
  `ByteValued` which can be used for reading into POD structures from
  raw bytes.

# [v0.1.0]

## Added

- Added traits for working with VM memory.
- Added a mmap based implemention for the Guest Memory.
