use super::TinyVec;

extern crate std;
use std::prelude::rust_2024::*;

#[test]
fn check_sizes() {
    use core::mem;

    macro_rules! eq_to_vec {
        ($t:ty) => {{
            const _TMP: usize = super::n_elements_for_stack::<$t>();
            assert_eq!(
                mem::size_of::<TinyVec<$t, _TMP>>(),
                mem::size_of::<Vec<$t>>()
            );
        }};
    }

    #[allow(dead_code)]
    struct S(u8,u16);
    eq_to_vec!(u8);
    eq_to_vec!(u16);
    eq_to_vec!(u32);
    eq_to_vec!(u64);
    eq_to_vec!(i8);
    eq_to_vec!(i16);
    eq_to_vec!(i32);
    eq_to_vec!(i64);
    eq_to_vec!(f32);
    eq_to_vec!(f64);
    eq_to_vec!(S);
}


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
    let empty: TinyVec<i32, 10> = tinyvec![];
    assert_eq!(empty.len(), 0);

    let tv: TinyVec<i32, 5> = tinyvec![1, 2, 3, 4, 5, 6];
    assert_eq!(tv.len(), 6);
    assert_eq!(tv.capacity(), 6);

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

#[test]
fn iter_test() {
    let tv = TinyVec::from([0, 1, 2, 3, 4]);

    let mut iter = tv.into_iter();

    assert_eq!(iter.len(), 5);

    assert_eq!(iter.next(), Some(0));
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.next(), Some(2));

    assert_eq!(iter.len(), 2);

    assert_eq!(iter.next_back(), Some(4));
    assert_eq!(iter.next(), Some(3));
}

#[test]
fn drain_test() {
    let mut tv = TinyVec::from([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);

    let mut drain = tv.drain(3..6);
    assert_eq!(drain.next(), Some(3));
    assert_eq!(drain.next(), Some(4));
    drop(drain);

    assert_eq!(tv.as_slice(), &[0, 1, 2, 6, 7, 8, 9]);
}

#[test]
fn drain_keep_rest() {
    let mut tv = TinyVec::from([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);

    let mut drain = tv.drain(3..7);

    assert_eq!(drain.next(), Some(3));
    assert_eq!(drain.next(), Some(4));

    assert_eq!(drain.as_slice(), &[5, 6]);
    drain.keep_rest();

    assert_eq!(tv.as_slice(), &[0, 1, 2, 5, 6, 7, 8, 9]);
}

#[test]
fn zst() {
    #[derive(Clone, Copy)]
    struct One;
    impl One {
        fn one(&self) -> usize { 1 }
    }

    assert_eq!(super::n_elements_for_stack::<One>(), isize::MAX as usize);
    assert_eq!(super::n_elements_for_bytes::<One>(919), isize::MAX as usize);

    let mut tv = TinyVec::<One, 10>::new();

    for _ in 0..1000 {
        tv.push(One);
    }
    let mut n = 0;
    for elem in tv.as_slice() {
        n += elem.one();
    }

    assert_eq!(tv.capacity(), isize::MAX as usize);
    assert_eq!(tv.len(), 1000);
    assert_eq!(n, 1000);
    assert!(tv.lives_on_stack());
}

#[test]
fn extract_if() {
    let mut numbers = TinyVec::<i32, 10>::from(&[1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15]);

    let evens = numbers.extract_if(.., |x| *x % 2 == 0).collect::<TinyVec<_, 8>>();
    let odds = numbers;

    assert_eq!(evens, &[2, 4, 6, 8, 14]);
    assert_eq!(odds, &[1, 3, 5, 9, 11, 13, 15]);

    let mut items = TinyVec::<i32, 10>::from(&[0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2]);
    let ones = items.extract_if(7.., |x| *x == 1).collect::<TinyVec<_, 4>>();
    assert_eq!(items, &[0, 0, 0, 0, 0, 0, 0, 2, 2, 2]);
    assert_eq!(ones.len(), 3);
}

#[test]
fn extract_if_vs_retain() {
    let mut vec1 = TinyVec::<i32, 10>::from(&[1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15]);
    let mut vec2 = vec1.clone();

    let pred = |x: &i32| *x % 2 == 0;
    vec1.extract_if(.., |n| pred(n)).for_each(|_| {});
    vec2.retain(|n| !pred(n));

    assert_eq!(vec1, vec2);
}

#[test]
fn extend() {
    let mut vec = TinyVec::<i32, 10>::new();
    vec.extend((0..10).map(|n| n * 2));
    assert_eq!(vec, &[0, 2, 4, 6, 8, 10, 12, 14, 16, 18]);
}

#[cfg(not(feature = "alloc"))]
mod no_alloc {

    use super::*;

    #[test]
    fn no_overflow() {
        let mut tv = TinyVec::<_, 5>::new();

        for n in 0..5 {
            tv.push(n);
        }

        assert_eq!(tv, &[0, 1, 2, 3, 4]);
    }

    #[test]
    #[should_panic(expected = "Alloc is not enabled. Can't switch the buffer to the heap")]
    fn overflows() {
        let mut tv = TinyVec::<_, 5>::new();

        for n in 0..10 {
            tv.push(n);
        }
    }

}
