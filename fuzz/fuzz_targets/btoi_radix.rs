#![no_main]

#[macro_use]
extern crate libfuzzer_sys;
extern crate btoi;

fuzz_target!(|data: &[u8]| {
    let _ = btoi::btoi_radix::<i32>(data, 36);
});
