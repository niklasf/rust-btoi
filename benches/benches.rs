#[macro_use]
extern crate bencher;
extern crate btoi;

use bencher::{Bencher, black_box};

fn bench_btou(b: &mut Bencher) {
    b.iter(|| assert_eq!(Some(123456789u32), btoi::btou(black_box(b"123456789"))));
}

fn bench_small_btou(b: &mut Bencher) {
    b.iter(|| assert_eq!(Some(42u8), btoi::btou(black_box(b"42"))));
}

fn bench_btoi(b: &mut Bencher) {
    b.iter(|| assert_eq!(Some(-123456789i32), btoi::btoi(black_box(b"-123456789"))));
}

fn bench_from_str(b: &mut Bencher) {
    fn btou_from_str(s: &[u8]) -> Option<u32> {
        ::std::str::from_utf8(s).ok().and_then(|s| s.parse().ok())
    }

    b.iter(|| assert_eq!(Some(123456789), btou_from_str(black_box(b"123456789"))));
}

fn bench_from_str_unchecked(b: &mut Bencher) {
    unsafe fn btou_from_str_unchecked(s: &[u8]) -> Option<u32> {
        ::std::str::from_utf8_unchecked(s).parse().ok()
    }

    b.iter(|| assert_eq!(Some(123456789), unsafe { btou_from_str_unchecked(black_box(b"123456789")) }));
}

fn bench_small_from_str(b: &mut Bencher) {
    fn btou_from_str(s: &[u8]) -> Option<u8> {
        ::std::str::from_utf8(s).ok().and_then(|s| s.parse().ok())
    }

    b.iter(|| assert_eq!(Some(42u8), btou_from_str(black_box(b"42"))));
}

fn bench_small_from_str_unchecked(b: &mut Bencher) {
    unsafe fn btou_from_str_unchecked(s: &[u8]) -> Option<u8> {
        ::std::str::from_utf8_unchecked(s).parse().ok()
    }

    b.iter(|| assert_eq!(Some(42u8), unsafe { btou_from_str_unchecked(black_box(b"42")) }));
}

benchmark_group!(benches,
    bench_btou,
    bench_btoi,
    bench_from_str,
    bench_from_str_unchecked,
    bench_small_btou,
    bench_small_from_str,
    bench_small_from_str_unchecked
);

benchmark_main!(benches);
