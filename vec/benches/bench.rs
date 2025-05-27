/* Benches taken from the smallvec crate, and addapted to TinyVec
 * <https://github.com/servo/rust-smallvec/blob/3906fe419285250261af4376a4224f075ca37eab/benches/bench.rs>
 * */

#![feature(test)]
#![allow(deprecated)]

extern crate test;

use test::Bencher;
use tiny_vec::{tinyvec, TinyVec};

const N: usize = 16;
const BIG: usize = 100;

type TVec = TinyVec<u64, N>;

macro_rules! make_benches {
    ($typ:ty { $($b_name:ident => $g_name:ident($($args:expr),*),)* }) => {
        $(
            #[bench]
            fn $b_name(b: &mut Bencher) {
                $g_name($($args,)* b)
            }
        )*
    }
}

make_benches! {
    TinyVec<u64, VEC_SIZE> {
        bench_push => gen_push(BIG as _),
        bench_push_small => gen_push(N as _),
        bench_insert_push => gen_insert_push(BIG as _),
        bench_insert_push_small => gen_insert_push(N as _),
        bench_insert => gen_insert(BIG as _),
        bench_insert_small => gen_insert(N as _),
        bench_remove => gen_remove(BIG as _),
        bench_remove_small => gen_remove(N as _),
        bench_extend => gen_extend(BIG as _),
        bench_extend_small => gen_extend(N as _),
        bench_extend_filtered => gen_extend_filtered(BIG as _),
        bench_extend_filtered_small => gen_extend_filtered(N as _),
        bench_from_iter => gen_from_iter(BIG as _),
        bench_from_iter_small => gen_from_iter(N as _),
        bench_from_slice => gen_from_slice(BIG as _),
        bench_from_slice_small => gen_from_slice(N as _),
        bench_extend_from_slice => gen_extend_from_slice(BIG as _),
        bench_extend_from_slice_small => gen_extend_from_slice(N as _),
        bench_macro_from_elem => gen_from_elem(BIG as _),
        bench_macro_from_elem_small => gen_from_elem(N as _),
        bench_pushpop => gen_pushpop(),
    }
}

fn gen_push(n: u64, b: &mut Bencher) {
    #[inline(never)]
    fn push_noinline(vec: &mut TVec, x: u64) {
        vec.push(x);
    }

    b.iter(|| {
        let mut vec = TVec::new();
        for x in 0..n {
            push_noinline(&mut vec, x);
        }
        vec
    });
}

fn gen_insert_push(n: u64, b: &mut Bencher) {
    #[inline(never)]
    fn insert_push_noinline(vec: &mut TVec, x: u64) {
        vec.insert(x as usize, x).unwrap();
    }

    b.iter(|| {
        let mut vec = TVec::new();
        for x in 0..n {
            insert_push_noinline(&mut vec, x);
        }
        vec
    });
}

fn gen_insert(n: u64, b: &mut Bencher) {
    #[inline(never)]
    fn insert_noinline(vec: &mut TVec, p: usize, x: u64) {
        vec.insert(p, x).unwrap();
    }

    b.iter(|| {
        let mut vec = TVec::new();
        // Always insert at position 0 so that we are subject to shifts of
        // many different lengths.
        vec.push(0);
        for x in 0..n {
            insert_noinline(&mut vec, 0, x);
        }
        vec
    });
}

fn gen_remove(n: usize, b: &mut Bencher) {
    #[inline(never)]
    fn remove_noinline(vec: &mut TVec, p: usize) -> u64 {
        vec.remove(p).unwrap()
    }

    b.iter(|| {
        let mut vec = tinyvec![0; n as _];

        for _ in 0..n {
            remove_noinline(&mut vec, 0);
        }
    });
}

fn gen_extend(n: u64, b: &mut Bencher) {
    b.iter(|| {
        let mut vec = TVec::new();
        vec.extend(0..n);
        vec
    });
}

fn gen_extend_filtered(n: u64, b: &mut Bencher) {
    b.iter(|| {
        let mut vec = TVec::new();
        vec.extend((0..n).filter(|i| i % 2 == 0));
        vec
    });
}

fn gen_from_iter(n: u64, b: &mut Bencher) {
    let v: Vec<u64> = (0..n).collect();
    b.iter(|| {
        TVec::from(&v[..])
    });
}

fn gen_from_slice(n: u64, b: &mut Bencher) {
    let v: Vec<u64> = (0..n).collect();
    b.iter(|| {
        TVec::from(&v[..])
    });
}

fn gen_extend_from_slice(n: u64, b: &mut Bencher) {
    let v: Vec<u64> = (0..n).collect();
    b.iter(|| {
        let mut vec = TVec::new();
        vec.extend_from_slice(&v);
        vec
    });
}

fn gen_pushpop(b: &mut Bencher) {
    #[inline(never)]
    fn pushpop_noinline(vec: &mut TVec, x: u64) -> Option<u64> {
        vec.push(x);
        vec.pop()
    }

    b.iter(|| {
        let mut vec = TVec::new();
        for x in 0..BIG as _ {
            pushpop_noinline(&mut vec, x);
        }
        vec
    });
}

fn gen_from_elem(n: usize, b: &mut Bencher) {
    b.iter(|| -> TVec {
        tinyvec![42; n as _]
    });
}

#[bench]
fn bench_macro_from_list(b: &mut Bencher) {
    b.iter(|| {
        let vec: TinyVec<u64, 16> = tinyvec![
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 24, 32, 36, 0x40, 0x80,
            0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000, 0x40000,
            0x80000, 0x100000,
        ];
        vec
    });
}

