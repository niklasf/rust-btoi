btoi
====

Parse integers from byte slices.

[![Build Status](https://travis-ci.org/niklasf/rust-btoi.svg?branch=master)](https://travis-ci.org/niklasf/rust-btoi)
[![crates.io](https://img.shields.io/crates/v/btoi.svg)](https://crates.io/crates/btoi)

Introduction
------------

Provides functions similar to [`from_str_radix`](https://doc.rust-lang.org/std/primitive.u32.html#method.from_str_radix),
but is faster when parsing directly from byte slices instead of strings.

```rust
use btoi::btoi;

assert_eq!(Ok(42), btoi(b"42"));
assert_eq!(Ok(-1000), btoi(b"-1000"));
```

Documentation
-------------

[Read the documentation](https://docs.rs/btoi)

Changelog
---------

* 0.2.0
  - No longer reexport num-traits.
* 0.1.3
  - Update to num-traits 0.2 (semver compatible).
* 0.1.2
  - Fix documentation warnings.
  - Update dependencies.
* 0.1.1
  - Documentation fixes.
* 0.1.0
  - Initial release.

License
-------

btoi is dual licensed under the [Apache 2.0](http://www.apache.org/licenses/LICENSE-2.0)
and [MIT](http://opensource.org/licenses/MIT) license, at your option.
