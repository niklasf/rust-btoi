btoi
====

Parse integers from byte slices.

Provides functions similar to [`from_str_radix`](https://doc.rust-lang.org/std/primitive.u32.html#method.from_str_radix),
but is faster when parsing directly from byte slices instead of strings.

[![Build Status](https://travis-ci.org/niklasf/rust-btoi.svg?branch=master)](https://travis-ci.org/niklasf/rust-btoi)
[![crates.io](https://img.shields.io/crates/v/btoi.svg)](https://crates.io/crates/btoi)

Example
-------

```rust
use btoi::btoi;

assert_eq!(Ok(42), btoi(b"42"));
assert_eq!(Ok(-1000), btoi(b"-1000"));
```

Documentation
-------------

[Read the documentation](https://docs.rs/btoi)

License
-------

btoi is dual licensed under the Apache 2.0 and MIT license.
