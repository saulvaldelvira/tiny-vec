#![feature(test)]
extern crate test;

use test::bench::Bencher;
use tiny_vec::TinyVec;

const N_ITER: usize = 10000;

#[bench]
fn bench_std_vector(b: &mut Bencher) {
    b.iter(|| {
        for _ in 0..N_ITER {
            let vec: Vec<_> = (0..20).filter(|n| n % 2 == 0).map(|n| n * n).collect();
            let n = vec[vec.len() / 2];
            println!("{n}")
        }
    });
}

fn bench_tiny<const N: usize>() {
    let vec: TinyVec<_, N> = (0..20).filter(|n| n % 2 == 0).map(|n| n * n).collect();
    let n = vec[vec.len() / 2];
    println!("{n}")
}

#[bench]
fn bench_tiny_vector_exact(b: &mut Bencher) {
    b.iter(|| {
         for _ in 0..N_ITER {
            bench_tiny::<20>()
         }
    });
}

#[bench]
fn bench_tiny_vector_realloc_end(b: &mut Bencher) {
    b.iter(|| {
         for _ in 0..N_ITER {
            bench_tiny::<17>()
        }
    });
}

#[bench]
fn bench_tiny_vector_realloc_half(b: &mut Bencher) {
    b.iter(|| {
         for _ in 0..N_ITER {
            bench_tiny::<10>()
        }
    });
}

#[bench]
fn bench_tiny_vector_realloc_start(b: &mut Bencher) {
    b.iter(|| {
         for _ in 0..N_ITER {
            bench_tiny::<5>()
        }
    });
}
