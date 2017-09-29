#[macro_use]
extern crate bencher;
extern crate btoi;

use bencher::{Bencher, black_box};

fn bench_btou(b: &mut Bencher) {
    b.iter(|| assert_eq!(Some(12345), btoi::btou(black_box(b"12345"))));
}

fn bench_btoi(b: &mut Bencher) {
    b.iter(|| assert_eq!(Some(-987654321), btoi::btoi(black_box(b"-987654321"))));
}

fn bench_from_str(b: &mut Bencher) {
    fn btou_from_str(s: &[u8]) -> Option<u32> {
        ::std::str::from_utf8(s).ok().and_then(|s| s.parse().ok())
    }

    b.iter(|| assert_eq!(Some(12345), btou_from_str(black_box(b"12345"))));
}

fn bench_from_str_unchecked(b: &mut Bencher) {
    unsafe fn btou_from_str_unchecked(s: &[u8]) -> Option<u32> {
        ::std::str::from_utf8_unchecked(s).parse().ok()
    }

    b.iter(|| assert_eq!(Some(12345), unsafe { btou_from_str_unchecked(black_box(b"12345")) }));
}

benchmark_group!(benches,
    bench_btou,
    bench_btoi,
    bench_from_str,
    bench_from_str_unchecked);

benchmark_main!(benches);
