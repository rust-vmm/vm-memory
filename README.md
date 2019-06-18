# vm-memory

A library to access the physical memory of a virtual machine.

In a typical Virtual Machine Monitor (VMM) there are several components, such
as boot loader, virtual device drivers, virtio backend drivers and vhost
drivers, that need to access the VM physical memory. The `vm-memory` crate
provides a set of traits to decouple VM memory consumers from VM memory
providers. Based on these traits, VM memory consumers can access the physical
memory of the VM without knowing the implementation details of the VM memory
provider. Thus VMM components based on these traits can be shared and reused by
multiple virtualization solutions.

## Platform Support

- Arch: x86, AMD64, ARM64
- OS: Linux/Unix/Windows

## Example

- Create a VM physical memory objects in hypervisor specific ways using the
  `GuestMemoryMmap` implementation of the `GuestMemory` trait:

```rust
fn provide_mem_to_virt_dev() {
    let gm = GuestMemoryMmap::new(&[
        (GuestAddress(0), 0x1000),
        (GuestAddress(0x1000), 0x1000)
    ]).unwrap();
    virt_device_io(&gm);
}
```

- Consumers access VM's physical memory

```rust
fn virt_device_io<T: GuestMemory>(mem: &T) {
    let sample_buf = &[1, 2, 3, 4, 5];
    assert_eq!(mem.write(sample_buf, GuestAddress(0xffc)).unwrap(), 5);
    let buf = &mut [0u8; 5];
    assert_eq!(mem.read(buf, GuestAddress(0xffc)).unwrap(), 5);
    assert_eq!(buf, sample_buf);
}
```

## Documentations & References

- [Design of The `vm-memory` Crate](DESIGN.md)
- [TODO List](TODO.md)
- [The rust-vmm Project](https://github.com/rust-vmm/)

## License

This project is licensed under

- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
