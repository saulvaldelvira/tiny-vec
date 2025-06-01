//! Iterator implementation for TinyVec

use core::iter::FusedIterator;
use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ptr;

use alloc::slice;

use crate::raw::RawVec;
use crate::TinyVec;

enum Kind<T, const N: usize> {
    Stack([MaybeUninit<T>; N]),
    Heap(RawVec<T>),
}

impl<T, const N: usize> Kind<T, N> {
    const fn ptr(&self) -> *const T {
        match self {
            Kind::Stack(s) => s.as_ptr().cast(),
            Kind::Heap(rv) => rv.ptr.as_ptr()
        }
    }

    const fn ptr_mut(&mut self) -> *mut T {
        match self {
            Kind::Stack(s) => s.as_mut_ptr().cast(),
            Kind::Heap(rv) => rv.ptr.as_ptr()
        }
    }
}

/// Iterator over the elements of a [TinyVec]
///
/// This struct is returned from the [TinyVec::into_iter] function
pub struct TinyVecIter<T, const N: usize> {
    start: usize,
    len: usize,
    buf: Kind<T, N>,
    _marker: PhantomData<TinyVec<T, N>>,
}

impl<T, const N: usize> TinyVecIter<T, N> {
    /// Casts the remaining portion of this iterator as a slice of T
    pub const fn as_slice(&self) -> &[T] {
        unsafe {
            let ptr = self.buf.ptr().add(self.start);
            slice::from_raw_parts(ptr, self.len)
        }
    }

    /// Casts the remaining portion of this iterator as a mutable slice of T
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            let ptr = self.buf.ptr_mut().add(self.start);
            slice::from_raw_parts_mut(ptr, self.len)
        }
    }
}

impl<T, const N: usize> Drop for TinyVecIter<T, N> {
    fn drop(&mut self) {
        let raw = match self.buf {
            Kind::Stack(_) => None,
            Kind::Heap(raw) => Some(raw),
        };

        if mem::needs_drop::<T>() {
            for e in self {
                mem::drop(e);
            }
        }

        if let Some(mut raw) = raw {
            unsafe { raw.destroy(); }
        }
    }
}

impl<T, const N: usize> Iterator for TinyVecIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            let e = unsafe {
                self.buf
                    .ptr_mut()
                    .add(self.start)
                    .read()
            };
            self.start += 1;
            self.len -= 1;
            Some(e)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T, const N: usize> DoubleEndedIterator for TinyVecIter<T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            let e = unsafe {
                self.buf
                    .ptr_mut()
                    .add(self.start + self.len)
                    .read()
            };
            Some(e)
        }
    }
}

impl<T, const N: usize> ExactSizeIterator for TinyVecIter<T, N> { }

impl<T, const N: usize> FusedIterator for TinyVecIter<T, N> { }

impl<T, const N: usize> IntoIterator for TinyVec<T, N> {
    type Item = T;

    type IntoIter = TinyVecIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let vec = ManuallyDrop::new(self);

        let is_stack = vec.lives_on_stack();
        let len = vec.len();

        let buf = unsafe {
            let inner = ptr::read( &vec.inner );
            if is_stack {
                Kind::Stack(ManuallyDrop::into_inner( inner.stack ))
            } else {
                Kind::Heap(inner.raw)
            }
        };

        TinyVecIter { start: 0, len, buf, _marker: PhantomData }
    }
}
