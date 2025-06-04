//! [extract_if](TinyVec::extract_if) implementation for TinyVec

use core::iter::FusedIterator;
use core::ptr;

use alloc::slice;

use crate::TinyVec;

pub struct ExtractIf<'a, T, const N: usize, F>
where
    T: 'a,
    F: FnMut(&mut T) -> bool,
{
    pub (super) vec: &'a mut TinyVec<T, N>,
    pub (super) next: usize,
    pub (super) last: usize,
    pub (super) original_len: usize,
    pub (super) deleted: usize,
    pub (super) pred: F,
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
