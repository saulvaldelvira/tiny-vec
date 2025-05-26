use core::mem;
use super::TinyVec;

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

assert_size_eq!(
    TinyVec<i32, 12>, [i32; 12];
    TinyVec<u8, 3>, super::RawVec<u8>;
);


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
