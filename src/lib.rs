#[cfg(test)]
#[macro_use]
extern crate quickcheck;
extern crate num_traits;

use num_traits::FromPrimitive;

#[inline]
fn ascii_to_digit<I: FromPrimitive>(ch: u8, radix: u8) -> Option<I> {
    assert!(radix >= 2 && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    match ch {
        b'0' ... b'9' if ch < b'0' + radix      => I::from_u8(ch - b'0'),
        b'a' ... b'z' if ch < b'a' + radix - 10 => I::from_u8(ch - b'a' + 10),
        b'A' ... b'Z' if ch < b'A' + radix - 10 => I::from_u8(ch - b'A' + 10),
        _ => None,
    }
}

pub fn btou(bytes: &[u8]) -> Option<u32> {
    if bytes.is_empty() {
        return None;
    }

    let mut result = 0u32;

    for &digit in bytes {
        let x = match ascii_to_digit(digit, 10) {
            Some(x) => x,
            None => return None,
        };
        result = match result.checked_mul(10) {
            Some(result) => result,
            None => return None,
        };
        result = match result.checked_add(x) {
            Some(result) => result,
            None => return None,
        };
    }

    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    quickcheck! {
        fn btou_identity(n: u32) -> bool {
            Some(n) == btou(n.to_string().as_bytes())
        }
    }
}
