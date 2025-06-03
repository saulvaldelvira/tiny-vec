use core::iter::FusedIterator;
use core::ops::{Range, RangeBounds};
use core::ptr;

use alloc::slice;

use crate::{slice_range, TinyVec};

pub struct ExtractIf<'a, T, const N: usize, F>
where
    T: 'a,
    F: FnMut(&mut T) -> bool,
{
    vec: &'a mut TinyVec<T, N>,

    next: usize,
    last: usize,
    original_len: usize,
    deleted: usize,
    pred: F,
}

impl<T, const N: usize, F> Iterator for ExtractIf<'_, T, N, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            while self.next < self.last {
                let i = self.next;
                let v = slice::from_raw_parts_mut(self.vec.as_mut_ptr(), self.original_len);
                let drained = (self.pred)(&mut v[i]);

                // Update the index *after* the predicate is called. If the index
                // is updated prior and the predicate panics, the element at this
                // index would be leaked.

                self.next += 1;

                if drained {
                    self.deleted += 1;
                    return Some(ptr::read(&v[i]));
                } else if self.deleted > 0 {
                    let del = self.deleted;
                    let src: *const T = &v[i];
                    let dst: *mut T = &mut v[i - del];
                    ptr::copy_nonoverlapping(src, dst, 1);
                }
            }
            None
        }
    }
}

impl<T, const N: usize, F> FusedIterator for ExtractIf<'_, T, N, F>
where
    F: FnMut(&mut T) -> bool {}

impl<T, const N: usize, F> Drop for ExtractIf<'_, T, N, F>
where
    F: FnMut(&mut T) -> bool,
{
    fn drop(&mut self) {
        unsafe {
            if self.next < self.original_len && self.deleted > 0 {
                let ptr = self.vec.as_mut_ptr();
                let src = ptr.add(self.next);
                let dst = src.sub(self.deleted);
                let tail_len = self.original_len - self.next;
                src.copy_to(dst, tail_len);
            }
            self.vec.set_len(self.original_len - self.deleted);
        }
    }
}

impl<T, const N: usize> TinyVec<T, N> {

    /// Creates an iterator which uses a closure to determine if the element in the range should be removed.
    ///
    /// If the closure returns true, then the element is removed and yielded.
    /// If the closure returns false, the element will remain in the vector and will not be yielded
    /// by the iterator.
    ///
    /// Only elements that fall in the provided range are considered for extraction, but any elements
    /// after the range will still have to be moved if any element has been extracted.
    ///
    /// If the returned `ExtractIf` is not exhausted, e.g. because it is dropped without iterating
    /// or the iteration short-circuits, then the remaining elements will be retained.
    ///
    /// Note that `extract_if` also lets you mutate the elements passed to the filter closure,
    /// regardless of whether you choose to keep or remove them.
    ///
    /// # Panics
    ///
    /// If `range` is out of bounds.
    ///
    /// # Examples
    ///
    /// Splitting an array into evens and odds, reusing the original allocation:
    ///
    /// ```
    /// use tiny_vec::TinyVec;
    /// let mut numbers = TinyVec::<i32, 10>::from(&[1, 2, 3, 4, 5, 6, 8, 9, 11, 13, 14, 15]);
    ///
    /// let evens = numbers.extract_if(.., |x| *x % 2 == 0).collect::<TinyVec<_, 8>>();
    /// let odds = numbers;
    ///
    /// assert_eq!(evens, &[2, 4, 6, 8, 14]);
    /// assert_eq!(odds, &[1, 3, 5, 9, 11, 13, 15]);
    /// ```
    ///
    /// Using the range argument to only process a part of the vector:
    ///
    /// ```
    /// use tiny_vec::TinyVec;
    /// let mut items = TinyVec::<i32, 10>::from(&[0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 1, 2]);
    /// let ones = items.extract_if(7.., |x| *x == 1).collect::<TinyVec<_, 4>>();
    /// assert_eq!(items, vec![0, 0, 0, 0, 0, 0, 0, 2, 2, 2]);
    /// assert_eq!(ones.len(), 3);
    /// ```
    pub fn extract_if<R, F>(&mut self, range: R, pred: F) -> ExtractIf<'_, T, N, F>
    where
        R: RangeBounds<usize>,
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len();
        let Range { start, end } = slice_range(range, len);

        unsafe { self.set_len(start) }

        ExtractIf {
            original_len: len,
            deleted: 0,
            next: start,
            last: end,
            vec: self,
            pred,
        }
    }
}
