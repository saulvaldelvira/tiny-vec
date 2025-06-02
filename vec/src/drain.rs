use crate::TinyVec;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop};
use core::ops::{Bound, RangeBounds};
use core::ptr::{self, NonNull};
use core::slice;

pub struct Drain<'a, T: 'a, const N: usize> {
    remaining_start: usize,
    remaining_len: usize,
    tail_start: usize,
    tail_len: usize,
    vec: NonNull<TinyVec<T, N>>,
    _marker: PhantomData<&'a mut TinyVec<T, N>>,
}

impl<'a, T: 'a, const N: usize> Drain<'a, T, N> {

    /// Returns the remaining elements as a slice
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe {
            let ptr = self.vec.as_ref().as_ptr().add(self.remaining_start);
            slice::from_raw_parts(ptr, self.remaining_len)
        }
    }

    /// Consumes this [Drain], preserving any un-yielded elements
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut tv = TinyVec::from([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// let mut drain = tv.drain(3..7);
    ///
    /// assert_eq!(drain.next(), Some(3));
    /// assert_eq!(drain.next(), Some(4));
    ///
    /// drain.keep_rest();
    ///
    /// assert_eq!(tv.as_slice(), &[0, 1, 2, 5, 6, 7, 8, 9]);
    /// ```
    pub fn keep_rest(self) {
        let mut slf = ManuallyDrop::new(self);

        /* [ HEAD ] [ yieled  | remaining | yielded_back ] [ TAIL ]
         *         ^          ^           ^                ^
         *         |          |           |                |
         *      vec.len   iter.ptr  (iter.ptr + iter.len)  tail_start
         * */
        unsafe {
            let vec = slf.vec.as_mut();
            let start = vec.len();

            if mem::size_of::<T>() != 0 {
                let buf = vec.as_mut_ptr();

                let start_ptr = buf.add(start);
                let remaining_ptr = buf.add(slf.remaining_start);

                if remaining_ptr != start_ptr {
                    /* First: We move the remaining chunk to the start */
                    ptr::copy(remaining_ptr, start_ptr, slf.remaining_len);
                }

                if slf.tail_start != (start + slf.remaining_len) {
                    let src = buf.add(slf.tail_start);
                    let dst = start_ptr.add(slf.remaining_len);
                    /* Now we move the tail */
                    ptr::copy(src, dst, slf.tail_len);
                }
            }
            vec.set_len(start + slf.remaining_len + slf.tail_len);
        }
    }
}

impl<'a, T: 'a, const N: usize> Iterator for Drain<'a, T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_len == 0 {
            None
        } else {
            unsafe {
                let e = self.vec.as_ref().as_ptr().add(self.remaining_start).read();
                self.remaining_start += 1;
                self.remaining_len -= 1;
                Some(e)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining_len, Some(self.remaining_len))
    }
}

impl<'a, T: 'a, const N: usize> DoubleEndedIterator for Drain<'a, T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.remaining_len == 0 {
            None
        } else {
            unsafe {
                let e = self.vec.as_ref()
                                .as_ptr()
                                .add(self.remaining_start + self.remaining_len - 1)
                                .read();
                self.remaining_len -= 1;
                Some(e)
            }
        }
    }
}

impl<'a, T: 'a, const N: usize> ExactSizeIterator for Drain<'a, T, N> { }

impl<'a, T: 'a, const N: usize> FusedIterator for Drain<'a, T, N> { }

impl<'a, T: 'a, const N: usize> Drop for Drain<'a, T, N> {
    fn drop(&mut self) {
        /* FIXME: The std implementation does some complex
         * thing with a DropGuard struct. */
        for e in &mut *self { drop(e) }
        unsafe {
            let vec = self.vec.as_mut();

            let len = vec.len();
            let ptr = vec.as_mut_ptr();

            let src = ptr.add(self.tail_start);
            let dst = ptr.add(len);

            ptr::copy(src, dst, self.tail_len);

            vec.set_len(len + self.tail_len);
        }
    }
}

impl<T, const N: usize> TinyVec<T, N> {

    /// Removes the subslice indicated by the given range from the vector,
    /// returning a double-ended iterator over the removed subslice.
    ///
    /// If the iterator is dropped before being fully consumed,
    /// it drops the remaining removed elements.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the vector.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the vector may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_vec::{tinyvec, TinyVec};
    /// let mut v: TinyVec<_, 10> = tinyvec![0, 1, 2, 3, 4, 5, 6];
    /// let mut drain = v.drain(2..=4);
    /// assert_eq!(drain.next(), Some(2));
    /// assert_eq!(drain.next(), Some(3));
    /// assert_eq!(drain.next(), Some(4));
    /// assert_eq!(drain.next(), None);
    /// drop(drain);
    ///
    /// assert_eq!(v, &[0, 1, 5, 6]);
    ///
    /// // A full range clears the vector, like `clear()` does
    /// v.drain(..);
    /// assert_eq!(v, &[]);
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<T, N>
    where
        R: RangeBounds<usize>
    {

        let len = self.len();

        let start = match range.start_bound() {
            Bound::Included(n) => *n,
            Bound::Excluded(n) => *n + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(n) => *n + 1,
            Bound::Excluded(n) => *n,
            Bound::Unbounded => len,
        };

        assert!(start <= end);
        assert!(end <= len);

        unsafe {
            self.set_len(start);

            Drain {
                vec: NonNull::new_unchecked(self as *mut _),
                remaining_start: start,
                remaining_len: end - start,
                tail_start: end,
                tail_len: len - end,
                _marker: PhantomData,
            }
        }
    }
}
