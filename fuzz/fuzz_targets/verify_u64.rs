#![no_main]

use libfuzzer_sys::fuzz_target;
use std::str::FromStr;

fuzz_target!(|data: &[u8]| {
    // choose a random radix
    if data.len() == 0 {
        return;
    }
    let radix: u32 = data[0].into();
    let data = &data[1..];
    if radix < 2 || radix > 36 {
        return;
    }
    // parse the input
    let result = btoi::btoi_radix::<u64>(data, radix);
    // compare the resut to the stdlib implementation
    if let Ok(string) = std::str::from_utf8(data) {
        // std cannot handle "-0" in an unsigned type while btoi can
        if string.starts_with("-0") {
            return;
        }
        let std_result = u64::from_str_radix(string, radix);
        match (result, std_result) {
            (Ok(ours), Ok(std)) => assert_eq!(ours, std),
            (Err(_), Err(_)) => (), // both failed, nothing to do
            (ours, std) => panic!("Parsing result mismatch! Ours: {ours:?}, std: {std:?}"),
        }
    }
});
