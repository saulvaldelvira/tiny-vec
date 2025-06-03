//! [drain](TinyString::drain) implementation

use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::{Bound, RangeBounds};
use core::ptr::{self, NonNull};

use alloc::{slice, str};

use crate::TinyString;

/// A draining iterator for [TinyString]
///
/// This struct is created by the [TinyString::drain] method
pub struct Drain<'a, const N: usize> {
    string: NonNull<TinyString<N>>,
    remaining_start: usize,
    remaining_len: usize,
    tail_start: usize,
    tail_len: usize,
    _marker: PhantomData<&'a mut TinyString<N>>,
}

impl<const N: usize> Drain<'_, N> {

    /// Returns the remaining slice
    pub const fn as_str(&mut self) -> &str {
        if self.remaining_len == 0 {
            return ""
        }
        unsafe {
            let str = self.string.as_ref().as_ptr().add(self.remaining_start);
            let slice = slice::from_raw_parts(str, self.remaining_len);
            str::from_utf8_unchecked(slice)
        }
    }

    /// Consumes this [Drain], preserving any un-yielded characters
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let mut tv = TinyString::<10>::from("abcdefghijk");
    ///
    /// let mut drain = tv.drain(3..7);
    ///
    /// assert_eq!(drain.next(), Some('d'));
    /// assert_eq!(drain.next(), Some('e'));
    ///
    /// drain.keep_rest();
    ///
    /// assert_eq!(tv.as_str(), "abcfghijk");
    /// ```
    pub fn keep_rest(self) {
        let mut slf = ManuallyDrop::new(self);

        /* [ HEAD ] [ yieled  | remaining | yielded_back ] [ TAIL ]
         *         ^          ^           ^                ^
         *         |          |           |                |
         *      vec.len   iter.ptr  (iter.ptr + iter.len)  tail_start
         * */
        unsafe {
            let string = slf.string.as_mut();
            let start = string.len();

            let buf = string.as_mut_ptr();

            let dst = buf.add(start);
            let src = buf.add(slf.remaining_start);
            /* First: We move the remaining chunk to the start */
            ptr::copy(src, dst, slf.remaining_len);

            let src = buf.add(slf.tail_start);
            let dst = dst.add(slf.remaining_len);
            /* Now we move the tail */
            ptr::copy(src, dst, slf.tail_len);

            string.0.set_len(start + slf.remaining_len + slf.tail_len);
        }
    }
}

impl<const N: usize> Iterator for Drain<'_, N> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let c = self.as_str().chars().next()?;
        self.remaining_start += c.len_utf8();
        self.remaining_len -= c.len_utf8();
        Some(c)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining_len, Some(self.remaining_len))
    }
}

impl<const N: usize> DoubleEndedIterator for Drain<'_, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let c = self.as_str().chars().next_back()?;
        self.remaining_len -= c.len_utf8();
        Some(c)
    }
}

impl<const N: usize> ExactSizeIterator for Drain<'_, N> {}

impl<const N: usize> FusedIterator for Drain<'_, N> {}

impl<const N: usize> Drop for Drain<'_, N> {
    fn drop(&mut self) {
        unsafe {
            let string = self.string.as_mut();
            let len = string.len();
            let ptr = string.as_mut_ptr();

            let src = ptr.add(self.tail_start);
            let dst = ptr.add(len);
            ptr::copy(src, dst, self.tail_len);

            string.0.set_len(len + self.tail_len);
        }
    }
}

impl<const N: usize> TinyString<N> {

    /// Removes the substring indicated by the given range from the string,
    /// returning a double-ended iterator over the removed substring.
    ///
    /// If the iterator is dropped before being fully consumed,
    /// it drops the remaining removed elements.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point, if
    /// the end point is greater than the length of the vector,
    /// or if any of the ends of the range fall outside a char boundary.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`core::mem::forget`], for example), the vector may have lost characters
    /// arbitrarily, including characters outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_str::TinyString;
    /// let mut s = TinyString::<10>::from("abcdefghijk");
    ///
    /// let mut drain = s.drain(2..=4);
    /// assert_eq!(drain.next(), Some('c'));
    /// assert_eq!(drain.next(), Some('d'));
    /// assert_eq!(drain.next(), Some('e'));
    /// assert_eq!(drain.next(), None);
    /// drop(drain);
    ///
    /// assert_eq!(s.as_str(), "abfghijk");
    ///
    /// // A full range clears the string, like `clear()` does
    /// s.drain(..);
    /// assert_eq!(s.as_str(), "");
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<N>
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
        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        unsafe {
            self.0.set_len(start);

            let string = NonNull::new_unchecked(self as *mut _);
            Drain {
                tail_len: len - end,
                tail_start: end,
                remaining_start: start,
                remaining_len: end - start,
                string,
                _marker: PhantomData,
            }
        }
    }
}
