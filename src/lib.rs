// Copyright 2017 Niklas Fiekas <niklas.fiekas@backscattering.de>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Parse integers from byte slices.
//!
//! Provides functions similar to [`from_str_radix`], but is faster when
//! parsing directly from byte slices instead of strings.
//!
//! # Errors
//!
//! All functions return [`ParseIntegerError`] for these error conditions:
//!
//! * The byte slice does not contain any digits.
//! * Not all characters are `0-9`, `a-z`, `A-Z`. Leading or trailing
//!   whitespace is not allowed. The `btoi*` functions accept on optional
//!   leading `+` or `-` sign. The `btou*` functions respectively do not
//!   allow signs.
//! * Not all digits are valid in the given radix.
//! * The number overflows or underflows the target type, but wrapping
//!   or saturating arithmetic is not used.
//!
//! # Panics
//!
//! Just like `from_str_radix` functions will panic if the given radix is
//! not in the range `2..=36` (or in the pathological case that there is
//! no representation of the radix in the target integer type).
//!
//! # Examples
//!
//! ```
//! use btoi::btoi;
//!
//! assert_eq!(Ok(42), btoi(b"42"));
//! assert_eq!(Ok(-1000), btoi(b"1000"));
//! ```
//!
//! [`ParseIntegerError`]: struct.ParseIntegerError.html
//! [`btoi`]: fn.btoi.html
//! [`btoi_radix`]: fn.btoi_radix.html
//! [`btoi_saturating`]: fn.btoi_saturating.html
//! [`btoi_saturating_radix`]: fn.btoi_saturating_radix.html
//! [`btou`]: fn.btou.html
//! [`btou_radix`]: fn.btou_radix.html
//! [`btou_saturating`]: fn.btou_saturating.html
//! [`btou_saturating_radix`]: fn.btou_saturating_radix.html
//! [`from_str_radix`]: https://doc.rust-lang.org/stable/std/primitive.u32.html#method.from_str_radix

#![doc(html_root_url = "https://docs.rs/btoi/0.1.0")]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;
extern crate num_traits;

use std::fmt;
use std::error::Error;

use num_traits::{
    FromPrimitive,
    Zero,
    CheckedAdd,
    CheckedSub,
    CheckedMul,
    Saturating,
    Bounded,
};

fn ascii_to_digit<I>(ch: u8, radix: u8) -> Option<I>
    where I: FromPrimitive
{
    match ch {
        b'0' ... b'9' if ch < b'0' + radix => I::from_u8(ch - b'0'),
        b'a' ... b'z' if ch < b'a' + radix - 10 => I::from_u8(ch - b'a' + 10),
        b'A' ... b'Z' if ch < b'A' + radix - 10 => I::from_u8(ch - b'A' + 10),
        _ => None,
    }
}

/// An error that can occur when parsing an integer.
///
/// * No digits
/// * Invalid digit
/// * Overflow
/// * Underflow
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntegerError {
    kind: ErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ErrorKind {
    Empty,
    InvalidDigit,
    Overflow,
    Underflow,
}

impl ParseIntegerError {
    fn desc(&self) -> &str {
        match self.kind {
            ErrorKind::Empty => "cannot parse integer without digits",
            ErrorKind::InvalidDigit => "invalid digit found in slice",
            ErrorKind::Overflow => "number too large to fit in target type",
            ErrorKind::Underflow => "number too small to fit in target type",
        }
    }
}

impl fmt::Display for ParseIntegerError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.desc().fmt(f)
    }
}

impl Error for ParseIntegerError {
    fn description(&self) -> &str {
        self.desc()
    }
}

/// Converts a byte slice in a given base to an integer. Signs are not allowed.
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` is empty
/// * not all characters of `bytes` are `0-9`, `a-z` or `A-Z`
/// * not all characters refer to digits in the given `radix`
/// * the number overflows `I`
///
/// # Panics
///
/// Panics if `radix` is not in the range `2..=36` (or in the pathological
/// case that there is no representation of `radix` in `I`).
///
/// # Examples
///
/// ```
/// # use btoi::btou_radix;
/// assert_eq!(Ok(255), btou_radix(b"ff", 16));
/// assert_eq!(Ok(42), btou_radix(b"101010", 2));
/// ```
///
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btou_radix<I>(bytes: &[u8], radix: u8) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedMul
{
    assert!(2 <= radix && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    let base = I::from_u8(radix).expect("radix can be represented as integer");

    if bytes.is_empty() {
        return Err(ParseIntegerError { kind: ErrorKind::Empty });
    }

    let mut result = I::zero();

    for &digit in bytes {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return Err(ParseIntegerError { kind: ErrorKind::InvalidDigit }),
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return Err(ParseIntegerError { kind: ErrorKind::Overflow }),
        };
        result = match result.checked_add(&x) {
            Some(result) => result,
            None => return Err(ParseIntegerError { kind: ErrorKind::Overflow }),
        };
    }

    Ok(result)
}

/// Converts a byte slice to an integer. Signs are not allowed.
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` is empty
/// * not all characters of `bytes` are `0-9`
/// * the number overflows `I`
///
/// # Panics
///
/// Panics in the pathological case that there is no representation of `10`
/// in `I`.
///
/// # Examples
///
/// ```
/// # use btoi::btou;
/// assert_eq!(Ok(12345), btou(b"12345"));
/// assert!(btou::<u8>(b"+1").is_err()); // only btoi allows signs
/// assert!(btou::<u8>(b"256").is_err()); // overflow
/// ```
///
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btou<I>(bytes: &[u8]) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedMul
{
    btou_radix(bytes, 10)
}

/// Converts a byte slice in a given base to an integer.
///
/// Like [`btou_radix`], but numbers may optionally start with a sign
/// (`-` or `+`).
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` has no digits
/// * not all characters of `bytes` are `0-9`, `a-z`, `A-Z`, exluding an
///   optional leading sign
/// * not all characters refer to digits in the given `radix`, exluding an
///   optional leading sign
/// * the number overflows or underflows `I`
///
/// # Panics
///
/// Panics if `radix` is not in the range `2..=36` (or in the pathological
/// case that there is no representation of `radix` in `I`).
///
/// # Examples
///
/// ```
/// # use btoi::btoi_radix;
/// assert_eq!(Ok(10), btoi_radix(b"a", 16));
/// assert_eq!(Ok(10), btoi_radix(b"+a", 16));
/// assert_eq!(Ok(-42), btoi_radix(b"-101010", 2));
/// ```
///
/// [`btou_radix`]: fn.btou_radix.html
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btoi_radix<I>(bytes: &[u8], radix: u8) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedSub + CheckedMul
{
    assert!(2 <= radix && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    let base = I::from_u8(radix).expect("radix can be represented as integer");

    if bytes.is_empty() {
        return Err(ParseIntegerError { kind: ErrorKind::Empty });
    }

    let digits = match bytes[0] {
        b'+' => return btou_radix(&bytes[1..], radix),
        b'-' => &bytes[1..],
        _ => return btou_radix(bytes, radix),
    };

    let mut result = I::zero();

    for &digit in digits {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return Err(ParseIntegerError { kind: ErrorKind::InvalidDigit }),
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return Err(ParseIntegerError { kind: ErrorKind::Underflow }),
        };
        result = match result.checked_sub(&x) {
            Some(result) => result,
            None => return Err(ParseIntegerError { kind: ErrorKind::Underflow }),
        };
    }

    Ok(result)
}

/// Converts a byte slice to an integer.
///
/// Like [`btou`], but numbers may optionally start with a sign (`-` or `+`).
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` has no digits
/// * not all characters of `bytes` are `0-9`, excluding an optional leading
///   sign
/// * the number overflows or underflows `I`
///
/// # Panics
///
/// Panics in the pathological case that there is no representation of `10`
/// in `I`.
///
/// # Examples
///
/// ```
/// # use btoi::btoi;
/// assert_eq!(Ok(123), btoi(b"123"));
/// assert_eq!(Ok(123), btoi(b"+123"));
/// assert_eq!(Ok(-123), btoi(b"-123"));
///
/// assert!(btoi::<i16>(b"123456789").is_err()); // overflow
/// assert!(btoi::<u32>(b"-1").is_err()); // underflow
///
/// assert!(btoi::<i32>(b" 42").is_err()); // leading space
/// ```
///
/// [`btou`]: fn.btou.html
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btoi<I>(bytes: &[u8]) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedSub + CheckedMul
{
    btoi_radix(bytes, 10)
}

/// Converts a byte slice in a given base to the closest possible integer.
/// Signs are not allowed.
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` is empty
/// * not all characters of `bytes` are `0-9`, `a-z`, `A-Z`
/// * not all characters refer to digits in the given `radix`
///
/// # Panics
///
/// Panics if `radix` is not in the range `2..=36` (or in the pathological
/// case that there is no representation of `radix` in `I`).
///
/// # Examples
///
/// ```
/// # use btoi::btou_saturating_radix;
/// assert_eq!(Ok(255), btou_saturating_radix::<u8>(b"00ff", 16));
/// assert_eq!(Ok(255), btou_saturating_radix::<u8>(b"0100", 16)); // u8 saturated
/// assert_eq!(Ok(255), btou_saturating_radix::<u8>(b"0101", 16)); // u8 saturated
/// ```
///
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btou_saturating_radix<I>(bytes: &[u8], radix: u8) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    assert!(2 <= radix && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    let base = I::from_u8(radix).expect("radix can be represented as integer");

    if bytes.is_empty() {
        return Err(ParseIntegerError { kind: ErrorKind::Empty });
    }

    let mut result = I::zero();

    for &digit in bytes {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return Err(ParseIntegerError { kind: ErrorKind::InvalidDigit }),
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return Ok(I::max_value()),
        };
        result = result.saturating_add(x);
    }

    Ok(result)
}

/// Converts a byte slice to the closest possible integer.
/// Signs are not allowed.
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` is empty
/// * not all characters of `bytes` are `0-9`
///
/// # Panics
///
/// Panics in the pathological case that there is no representation of `10`
/// in `I`.
///
/// # Examples
///
/// ```
/// # use btoi::btou_saturating;
/// assert_eq!(Ok(65535), btou_saturating::<u16>(b"65535"));
/// assert_eq!(Ok(65535), btou_saturating::<u16>(b"65536")); // u16 saturated
/// assert_eq!(Ok(65535), btou_saturating::<u16>(b"65537")); // u16 saturated
/// ```
///
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btou_saturating<I>(bytes: &[u8]) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    btou_saturating_radix(bytes, 10)
}

/// Converts a byte slice in a given base to the closest possible integer.
///
/// Like [`btou_saturating_radix`], but numbers may optionally start with a
/// sign (`-` or `+`).
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` has no digits
/// * not all characters of `bytes` are `0-9`, `a-z`, `A-Z`, excluding an
///   optional leading sign
/// * not all characters refer to digits in the given `radix`, excluding an
///   optional leading sign
///
/// # Panics
///
/// Panics if `radix` is not in the range `2..=36` (or in the pathological
/// case that there is no representation of `radix` in `I`).
///
/// # Examples
///
/// ```
/// # use btoi::btoi_saturating_radix;
/// assert_eq!(Ok(127), btoi_saturating_radix::<i8>(b"7f", 16));
/// assert_eq!(Ok(127), btoi_saturating_radix::<i8>(b"ff", 16)); // no overflow
/// assert_eq!(Ok(-128), btoi_saturating_radix::<i8>(b"-ff", 16)); // no underflow
/// ```
///
/// [`btou_saturating_radix`]: fn.btou_saturating_radix.html
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btoi_saturating_radix<I>(bytes: &[u8], radix: u8) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    assert!(2 <= radix && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    let base = I::from_u8(radix).expect("radix can be represented as integer");

    if bytes.is_empty() {
        return Err(ParseIntegerError { kind: ErrorKind::Empty });
    }

    let digits = match bytes[0] {
        b'+' => return btou_saturating_radix(&bytes[1..], radix),
        b'-' => &bytes[1..],
        _ => return btou_saturating_radix(bytes, radix),
    };

    let mut result = I::zero();

    for &digit in digits {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return Err(ParseIntegerError { kind: ErrorKind::InvalidDigit }),
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return Ok(I::min_value()),
        };
        result = result.saturating_sub(x);
    }

    Ok(result)
}

/// Converts a byte slice to the closest possible integer.
///
/// Like [`btou_saturating`], but numbers may optionally start with a sign
/// (`-` or `+`).
///
/// # Errors
///
/// Returns [`ParseIntegerError`] for any of the following conditions:
///
/// * `bytes` has no digits
/// * not all characters of `bytes` are `0-9`, excluding an optional leading
///   sign
///
/// # Panics
///
/// Panics in the pathological case that there is no representation of `10`
/// in `I`.
///
/// # Examples
///
/// ```
/// # use btoi::btoi_saturating;
/// assert_eq!(Ok(127), btoi_saturating::<i8>(b"127"));
/// assert_eq!(Ok(127), btoi_saturating::<i8>(b"128")); // i8 saturated
/// assert_eq!(Ok(127), btoi_saturating::<i8>(b"+1024")); // i8 saturated
/// assert_eq!(Ok(-128), btoi_saturating::<i8>(b"-128"));
/// assert_eq!(Ok(-128), btoi_saturating::<i8>(b"-129")); // i8 saturated
///
/// assert_eq!(Ok(0), btoi_saturating::<u32>(b"-123")); // unsigned integer saturated
///
/// [`btou_saturating`]: fn.btou_saturating.html
/// [`ParseIntegerError`]: struct.ParseIntegerError.html
pub fn btoi_saturating<I>(bytes: &[u8]) -> Result<I, ParseIntegerError>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    btoi_saturating_radix(bytes, 10)
}

#[cfg(test)]
mod tests {
    use super::*;

    quickcheck! {
        fn btou_identity(n: u32) -> bool {
            Ok(n) == btou(n.to_string().as_bytes())
        }

        fn btou_binary_identity(n: u64) -> bool {
            Ok(n) == btou_radix(format!("{:b}", n).as_bytes(), 2)
        }

        fn btou_octal_identity(n: u64) -> bool {
            Ok(n) == btou_radix(format!("{:o}", n).as_bytes(), 8)
        }

        fn btou_lower_hex_identity(n: u64) -> bool {
            Ok(n) == btou_radix(format!("{:x}", n).as_bytes(), 16)
        }

        fn btou_upper_hex_identity(n: u64) -> bool {
            Ok(n) == btou_radix(format!("{:X}", n).as_bytes(), 16)
        }

        fn btoi_identity(n: i32) -> bool {
            Ok(n) == btoi(n.to_string().as_bytes())
        }

        fn btou_saturating_identity(n: u32) -> bool {
            Ok(n) == btou_saturating(n.to_string().as_bytes())
        }

        fn btoi_saturating_identity(n: i32) -> bool {
            Ok(n) == btoi_saturating(n.to_string().as_bytes())
        }
    }
}
