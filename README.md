# tinybitset

This crate provides a small, fixed size bitset type that stores its data inline
rather than on the heap. It uses const generics to have a single type that is
generic over the size and the underlying storage type.

While the crate supports bitsets of any size, it is best used for cases where
the data is small enough to be cheaply copyable. For bitsets using over 256 bits
a heap-allocated implementation such as the one provided by
[`fixedbitset`][fixedbitset] might be more suitable.

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

[fixedbitset]: https://github.com/petgraph/fixedbitset
