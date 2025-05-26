/*  Copyright (C) 2025 Saúl Valdelvira
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, version 3.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>. */

use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use core::{fmt, ptr};
use core::slice;

mod raw;
use raw::{next_cap, RawVec};

union TinyVecInner<T, const N: usize> {
    stack: ManuallyDrop<[MaybeUninit<T>; N]>,
    raw: RawVec<T>,
}

impl<T, const N: usize> TinyVecInner<T, N> {
    unsafe fn as_ptr_stack(&self) -> *const T {
        unsafe { &self.stack as *const _ as *const T }
    }

    unsafe fn as_ptr_stack_mut(&mut self) -> *mut T {
        unsafe { &mut self.stack as *mut _ as *mut T }
    }

    unsafe fn as_ptr_heap(&self) -> *const T {
        unsafe { self.raw.ptr.as_ptr() }
    }

    unsafe fn as_ptr_heap_mut(&mut self) -> *mut T {
        unsafe { self.raw.ptr.as_ptr() }
    }
}

#[repr(transparent)]
struct Length(usize);

impl Length {
    const fn new_heap(len: usize) -> Self {
        Self(len << 1 | 0b1)
    }

    #[inline]
    const fn is_stack(&self) -> bool {
        (self.0 & 0b1) == 0
    }

    #[inline]
    const fn set_heap(&mut self) {
        self.0 |= 0b1;
    }

    #[inline]
    const fn get(&self) -> usize {
        self.0 >> 1
    }

    #[inline]
    const fn add(&mut self, n: usize) {
        self.0 += n << 1;
    }

    #[inline]
    const fn sub(&mut self, n: usize) {
        self.0 -= n << 1;
    }
}

pub struct TinyVec<T, const N: usize> {
    inner: TinyVecInner<T, N>,
    len: Length,
}

impl<T, const N: usize> TinyVec<T, N> {
    fn ptr(&self) -> *const T {
        unsafe {
            if self.len.is_stack() {
                self.inner.as_ptr_stack()
            } else {
                self.inner.as_ptr_heap()
            }
        }
    }

    fn ptr_mut(&mut self) -> *mut T {
        unsafe {
            if self.len.is_stack() {
                self.inner.as_ptr_stack_mut()
            } else {
                self.inner.as_ptr_heap_mut()
            }
        }
    }

    unsafe fn switch(&mut self, n: usize) {
        let cap = next_cap(self.len.get() + n);
        let vec = RawVec::with_capacity(cap);
        unsafe {
            let src = self.inner.as_ptr_stack();
            let dst = vec.ptr.as_ptr();
            ptr::copy(
                src,
                dst,
                self.len.get()
            );
            self.inner.raw = vec;
        }
        self.len.set_heap();
    }
}

impl<T, const N: usize> TinyVec<T, N> {
    pub const fn new() -> Self {
        let stack = [ const { MaybeUninit::uninit() }; N ];
        Self {
            inner: TinyVecInner { stack: ManuallyDrop::new(stack) },
            len: Length(0),
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        let mut len = Length(0);
        let inner = if cap <= N {
            let s = [ const { MaybeUninit::uninit() }; N ];
            TinyVecInner { stack: ManuallyDrop::new(s) }
        } else {
            len.set_heap();
            TinyVecInner { raw: RawVec::with_capacity(cap) }
        };

        Self { inner, len }
    }

    /// Returns the number of elements inside this vec
    #[inline]
    pub const fn len(&self) -> usize { self.len.get() }

    /// Returns true if the vector is empty
    #[inline]
    pub const fn is_empty(&self) -> bool { self.len.get() == 0 }

    /// Returns the allocated capacity for this vector
    pub const fn capacity(&self) -> usize {
        if self.len.is_stack() {
            N
        } else {
            unsafe { self.inner.raw.cap }
        }
    }

    /// Reserves space for, at least, n elements
    pub fn reserve(&mut self, n: usize) {
        if self.len.is_stack() {
            if self.len.get() + n > N {
                unsafe {
                    self.switch(n);
                }
            }
        } else {
            unsafe {
                self.inner.raw.expand_if_needed(self.len.get(), n);
            }
        }
    }

    /// Appends an element to the back of the vector
    pub fn push(&mut self, elem: T) {
        self.reserve(1);
        unsafe {
            let dst = self.ptr_mut().add(self.len.get());
            dst.write(elem);
        }
        self.len.add(1);
    }

    /// Try to push an element inside the vector, only if
    /// there's room for it. If the push would've caused a
    /// reallocation of the buffer, returns the value.
    pub fn push_within_capacity(&mut self, val: T) -> Result<(),T> {
        if self.len.get() < self.capacity() {
            unsafe {
                // TODO CHECK
                self.ptr_mut().add(self.len.get()).write(val)
            }
            self.len.add(1);
            Ok(())
        } else {
            Err(val)
        }
    }
    /// Removes the last element of this vector (if present)
    pub fn pop(&mut self) -> Option<T> {
        if self.len.get() == 0 {
            None
        } else {
            self.len.sub(1);
            let val =
            unsafe {
                self.ptr().add(self.len.get()).read()
            };
            Some(val)
        }
    }

    /// Inserts an element in the given index position
    #[inline]
    pub fn insert(&mut self, index: usize, elem: T) -> Result<(),T> {
        if index > self.len.get() { return Err(elem) }
        unsafe { self.insert_unckecked(index, elem); }
        Ok(())
    }

    /// # Safety
    ///
    /// The index should be valid.
    pub unsafe fn insert_unckecked(&mut self, index: usize, elem: T) {
        self.reserve(1);

        unsafe {
            ptr::copy(
                self.ptr().add(index),
                self.ptr_mut().add(index + 1),
                self.len.get() - index,
            );
            self.ptr_mut().add(index).write(elem);
        }
        self.len.add(1);
    }

    /// Reserves space for exactly n elements more
    pub fn reserve_exact(&mut self, n: usize) {
        if self.len.is_stack() {
            if self.len.get() + n > N {
                unsafe { self.switch(n); }
            }
        } else {
            let vec = unsafe { &mut self.inner.raw };
            let new_cap = vec.cap.max(self.len.get() + n);
            vec.expand(new_cap);
        }
    }

    /// # Safety
    /// Index should be < Vec::len()
    pub unsafe fn remove_unchecked(&mut self, index: usize) -> T {
        debug_assert!(index < self.len.get(), "Index is >= than {}, this will trigger UB", self.len.get());

        unsafe {
            self.len.sub(1);
            let result = self.ptr_mut().add(index).read();
            ptr::copy(
                self.ptr().add(index + 1),
                self.ptr_mut().add(index),
                self.len.get() - index,
            );
            result
        }
    }

    #[inline]
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len.get() { return None }
        /* Safety: We've just checked the invariant. Index will always
         * be < self.len, so it's 100% safe to call this function */
        Some( unsafe { self.remove_unchecked(index) } )
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        if !self.len.is_stack() {
            unsafe { self.inner.raw.shrink_to_fit(self.len.get()); }
        }
    }

    pub fn push_slice(&mut self, s: &[T]) {
        let len = s.len();
        let src = s.as_ptr();

        self.reserve(len);

        unsafe {
            ptr::copy(
                src,
                self.ptr_mut().add(self.len.get()),
                len
            )
        }

        self.len.add(len);
    }

    pub fn extend_from<I>(&mut self, it: I)
    where
        I: IntoIterator<Item = T>,
    {
        let it = it.into_iter();

        let (min, max) = it.size_hint();
        let reserve = match max {
            Some(max) => max,
            None => min,
        };

        if reserve > 0 {
            self.reserve(reserve);
        }

        for elem in it {
            self.push(elem);
        }
    }
}

impl<T, const N: usize> Default for TinyVec<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for TinyVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self[..], f)
    }
}

impl<T: PartialEq, const N: usize> PartialEq for TinyVec<T, N> {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<T, const N: usize> Deref for TinyVec<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        unsafe { slice::from_raw_parts(self.ptr(), self.len.get()) }
    }
}


impl<T, const N: usize> DerefMut for TinyVec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { slice::from_raw_parts_mut(self.ptr_mut(), self.len.get()) }
    }
}

impl<T, const N: usize> Drop for TinyVec<T, N> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            for e in self.deref_mut() {
                unsafe { ptr::drop_in_place(e) };
            }
        }
        if !self.len.is_stack() {
            unsafe { self.inner.raw.destroy(); }
        }
    }
}

impl<T, const N: usize> From<Vec<T>> for TinyVec<T, N> {
    fn from(value: Vec<T>) -> Self {
        let mut md = ManuallyDrop::new(value);
        let ptr = unsafe { NonNull::new_unchecked( md.as_mut_ptr() ) };
        let inner = TinyVecInner {
            raw: RawVec {
                cap: md.capacity(),
                ptr,
            }
        };

        Self {
            inner,
            len: Length::new_heap(md.len()),
        }
    }
}

#[cfg(test)]
mod test;
