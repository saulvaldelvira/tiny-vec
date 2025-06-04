//! [drain](TinyVec::drain) implementation
//!
use crate::TinyVec;
use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop};
use core::ptr::{self, NonNull};
use core::slice;

/// A draining iterator for [TinyVec]
///
/// This struct is created by the [TinyVec::drain] method
pub struct Drain<'a, T: 'a, const N: usize> {
    pub (super) remaining_start: usize,
    pub (super) remaining_len: usize,
    pub (super) tail_start: usize,
    pub (super) tail_len: usize,
    pub (super) vec: NonNull<TinyVec<T, N>>,
    pub (super) _marker: PhantomData<&'a mut TinyVec<T, N>>,
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

        /* [ HEAD ] [ yieled  | remaining | yielded_back ] [ TAIL ] */
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
