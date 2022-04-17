#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _ = btoi::btoi_radix::<i32>(data, 36);
});
