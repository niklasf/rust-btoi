#[cfg(test)]
#[macro_use]
extern crate quickcheck;

fn ascii_to_digit(ch: u8, radix: u32) -> Option<u32> {
    assert!(radix >= 2 && radix <= 36,
            "radix must lie in the range 2..=36, found {}", radix);

    let val = match ch {
        b'0' ... b'9' => (ch - b'0') as u32,
        b'a' ... b'z' => (ch - b'a') as u32 + 10,
        b'A' ... b'Z' => (ch - b'A') as u32 + 10,
        _ => return None,
    };

    if val < radix { Some(val) }
    else { None }
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
