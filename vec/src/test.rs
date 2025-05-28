use core::mem;
use super::TinyVec;

extern crate std;
use std::prelude::rust_2024::*;

macro_rules! assert_size_eq {
    ($($t:ty, $u:ty ;)*) => {
        const _: () = const {
            $(
                assert!(
                    mem::size_of::<$t>()
                    ==
                    mem::size_of::<$u>() + mem::size_of::<usize>()
                );
            )*
        };
    };
}

macro_rules! assert_size_def {
    ($($t:ty),*) => {
        const _: () = const {
            $(
                assert!(
                    mem::size_of::<super::TinyVecInner<$t, { super::n_elements_for_stack::<$t>() } >>()
                    ==
                    mem::size_of::<super::RawVec<$t>>()
                );
            )*
        };
    };
}

assert_size_eq!(
    TinyVec<i32, 12>, [i32; 12];
    TinyVec<i32, 12>, [i32; 12];
    TinyVec<u8, 3>, super::RawVec<u8>;
    TinyVec<u8, 24>, Vec<u8>;
);

#[allow(dead_code)]
struct S(u8,u16);
assert_size_def!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64, S);

#[test]
fn simple() {
    let mut svec = TinyVec::<i32, 12>::new();

    for i in 0..12 {
        svec.push(i);
        assert_eq!(svec.len(), i as usize + 1);
    }

    assert_eq!(&svec[..], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);

    for i in (0..12).rev() {
        assert_eq!(svec.pop().unwrap(), i);
        assert_eq!(svec.len(), i as usize);
    }

    assert_eq!(&svec[..], &[]);
    assert!(svec.is_empty());
}

#[test]
fn macro_test() {
    let tv: TinyVec<i32, 5> = tinyvec![1, 2, 3];
    assert_eq!(tv.len(), 3);

    let tv: TinyVec<i32, 5> = tinyvec![10; 20];
    assert_eq!(tv.len(), 20);
}

#[test]
fn swap_test() {
    let mut tv = TinyVec::from([1, 2, 3, 4, 5]);
    tv.swap(1, 3);
    assert_eq!(tv.as_slice(), &[1, 4, 3, 2, 5]);
    tv.swap(1, 1);
    assert_eq!(tv.as_slice(), &[1, 4, 3, 2, 5]);
    tv.swap_checked(3, 1).unwrap();
    assert_eq!(tv.as_slice(), &[1, 2, 3, 4, 5]);
}

macro_rules! panic_test {
    ($n:ident, $msg:literal, $b:expr) => {
        #[test]
        #[should_panic(expected = $msg)]
        fn $n() {
            $b;
        }
    };
}

panic_test!(
    swap_out_of_bounds,
    "index out of bounds: the len is 2 but the index is 2",
    TinyVec::from([1, 2]).swap(2, 0)
);

