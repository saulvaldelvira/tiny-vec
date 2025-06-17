#![feature(test)]
extern crate test;

use test::bench::Bencher;
use tiny_str::TinyString;

const N_ITER: usize = 20000;
const INPUT: &str = "aAbBcCdDeEfFgGhHiIjJkKlLmMnNoOpPqQrRsStT";

#[bench]
fn bench_std_string(b: &mut Bencher) {
    b.iter(|| {
        for _ in 0..N_ITER {
            let s: String = INPUT.chars().filter(|c| c.is_ascii_lowercase()).collect();
            let n = &s.as_str()[s.len() / 2..];
            println!("{n}")
        }
    });
}

fn bench_tiny<const N: usize>() {
    for _ in 0..N_ITER {
        let s: TinyString<N> = INPUT.chars().filter(|c| c.is_ascii_lowercase()).collect();
        let n = &s.as_str()[s.len() / 2..];
        println!("{n}");
    }
}

#[bench]
fn bench_tiny_string_exact(b: &mut Bencher) {
    let s: TinyString<20> = INPUT.chars().filter(|c| c.is_ascii_lowercase()).collect();
    assert_eq!(s.len(), 20);
    b.iter(|| {
        bench_tiny::<20>()
    });
}

#[bench]
fn bench_tiny_string_realloc_end(b: &mut Bencher) {
    b.iter(|| {
        bench_tiny::<17>()
    });
}

#[bench]
fn bench_tiny_string_realloc_half(b: &mut Bencher) {
    b.iter(|| {
        bench_tiny::<10>()
    });
}

#[bench]
fn bench_tiny_string_realloc_start(b: &mut Bencher) {
    b.iter(|| {
        bench_tiny::<5>()
    });
}
