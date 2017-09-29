#[cfg(test)]
#[macro_use]
extern crate quickcheck;
extern crate num_traits;

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
    assert!(2 <= radix && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    match ch {
        b'0' ... b'9' if ch < b'0' + radix => I::from_u8(ch - b'0'),
        b'a' ... b'z' if ch < b'a' + radix - 10 => I::from_u8(ch - b'a' + 10),
        b'A' ... b'Z' if ch < b'A' + radix - 10 => I::from_u8(ch - b'A' + 10),
        _ => None,
    }
}

pub fn btou_radix<I>(bytes: &[u8], radix: u8) -> Option<I>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedMul
{
    if bytes.is_empty() {
        return None;
    }

    let mut result = I::zero();
    let base = I::from_u8(radix).expect("radix can be represented as integer");

    for &digit in bytes {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return None,
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return None,
        };
        result = match result.checked_add(&x) {
            Some(result) => result,
            None => return None,
        };
    }

    Some(result)
}

pub fn btou<I>(bytes: &[u8]) -> Option<I>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedMul
{
    btou_radix(bytes, 10)
}

pub fn btoi_radix<I>(bytes: &[u8], radix: u8) -> Option<I>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedSub + CheckedMul
{
    if bytes.is_empty() {
        return None;
    }

    let digits = match bytes[0] {
        b'+' => return btou_radix(&bytes[1..], radix),
        b'-' => &bytes[1..],
        _ => return btou_radix(bytes, radix),
    };

    let mut result = I::zero();
    let base = I::from_u8(radix).expect("radix can be represented as integer");

    for &digit in digits {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return None,
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return None,
        };
        result = match result.checked_sub(&x) {
            Some(result) => result,
            None => return None,
        };
    }

    Some(result)
}

pub fn btoi<I>(bytes: &[u8]) -> Option<I>
    where I: FromPrimitive + Zero + CheckedAdd + CheckedSub + CheckedMul
{
    btoi_radix(bytes, 10)
}

pub fn btou_saturating_radix<I>(bytes: &[u8], radix: u8) -> Option<I>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    if bytes.is_empty() {
        return None;
    }

    let mut result = I::zero();
    let base = I::from_u8(radix).expect("radix can be represented as integer");

    for &digit in bytes {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return None,
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return Some(I::max_value()),
        };
        result = result.saturating_add(x);
    }

    Some(result)
}

pub fn btou_saturating<I>(bytes: &[u8]) -> Option<I>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    btou_saturating_radix(bytes, 10)
}

pub fn btoi_saturating_radix<I>(bytes: &[u8], radix: u8) -> Option<I>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    if bytes.is_empty() {
        return None;
    }

    let digits = match bytes[0] {
        b'+' => return btou_saturating_radix(&bytes[1..], radix),
        b'-' => &bytes[1..],
        _ => return btou_saturating_radix(bytes, radix),
    };

    let mut result = I::zero();
    let base = I::from_u8(radix).expect("radix can be represented as integer");

    for &digit in digits {
        let x = match ascii_to_digit(digit, radix) {
            Some(x) => x,
            None => return None,
        };
        result = match result.checked_mul(&base) {
            Some(result) => result,
            None => return Some(I::min_value()),
        };
        result = result.saturating_sub(x);
    }

    Some(result)
}

pub fn btoi_saturating<I>(bytes: &[u8]) -> Option<I>
    where I: FromPrimitive + Zero + CheckedMul + Saturating + Bounded
{
    btoi_saturating_radix(bytes, 10)
}

#[cfg(test)]
mod tests {
    use super::*;

    quickcheck! {
        fn btou_identity(n: u32) -> bool {
            Some(n) == btou(n.to_string().as_bytes())
        }

        fn btoi_identity(n: i32) -> bool {
            Some(n) == btoi(n.to_string().as_bytes())
        }

        fn btou_saturating_identity(n: u32) -> bool {
            Some(n) == btou_saturating(n.to_string().as_bytes())
        }

        fn btoi_saturating_identity(n: i32) -> bool {
            Some(n) == btoi_saturating(n.to_string().as_bytes())
        }
    }
}
