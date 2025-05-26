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

//! Tiny Vec
//!
//! A dynamic array that can store a small amount of elements on the stack.
//!
//! This struct provides a vec-like API, but performs small-vector optimization.
//! This means that a `TinyVec<T, N>` stores up to N elements on the stack.
//! If the vector grows bigger than that, it moves the contents to the heap.
//!
//! # Example
//! ```
//! use tiny_vec::TinyVec;
//!
//! let mut tv = TinyVec::<u8, 16>::new();
//!
//! for n in 0..16 {
//!     tv.push(n);
//! }
//!
//! // Up to this point, no heap allocations are needed.
//! // All the elements are stored on the stack.
//!
//! tv.push(123); // This moves the vector to the heap
//!
//! assert_eq!(&tv[..], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
//!                       10, 11, 12, 13, 14, 15, 123])
//! ```
//!
//! # Memory layout
//! For a TinyVec<T, N>
//!
//! On the stack (length <= N)
//! - [T; N] : Data
//! - usize  : Length
//!
//! On the heap (length > N)
//! - T*    : Data
//! - usize : Capacity
//! - usize : Length
//!
//! If N is equal to `sizeof (T*, usize) / sizeof T`, the
//! TinyVec is the same size as a regular vector \
//! NOTE: The [n_elements_for_stack] function returns the maximun
//! number of elements for a type, such that it doesn't waste extra
//! space when moved to the heap
//!

#![allow(incomplete_features)]
#![cfg_attr(feature = "nightly-const-generics", feature(generic_const_exprs))]

use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use core::{fmt, ptr};
use core::slice;

mod raw;
use raw::RawVec;

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
    const fn set_stack(&mut self) {
        self.0 &= 0b0;
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

/// The maximun number of elements that can be stored in the stack
/// for the vector, without incrementing it's size
///
/// This means, that [`n_elements_for_stack`] for T returns the max
/// number of elements, so that when switching to a heap allocated
/// buffer, no stack size is wasted
///
/// # Examples
/// ```
/// use tiny_vec::n_elements_for_stack;
///
/// assert_eq!(n_elements_for_stack::<u8>(), 16);
/// assert_eq!(n_elements_for_stack::<u16>(), 8);
/// assert_eq!(n_elements_for_stack::<i32>(), 4);
/// ```
pub const fn n_elements_for_stack<T>() -> usize {
    mem::size_of::<RawVec<T>>() / mem::size_of::<T>()
}

/// A dynamic array that can store a small amount of elements on the stack.
pub struct TinyVec<T,
    #[cfg(not(feature = "nightly-const-generics"))]
    const N: usize,

    #[cfg(feature = "nightly-const-generics")]
    const N: usize = { n_elements_for_stack::<T>() },
> {
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

    unsafe fn switch_to_heap(&mut self, n: usize) {
        let mut vec = RawVec::new();
        vec.expand_if_needed(0, self.len.get() + n);
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

    unsafe fn switch_to_stack(&mut self) {
        let mut rv = unsafe { self.inner.raw };

        let stack = [ const { MaybeUninit::uninit() }; N ];

        unsafe {
            let src = rv.ptr.as_ptr();
            let dst = stack.as_ptr() as *mut T;
            ptr::copy(
                src,
                dst,
                self.len.get()
            );

            rv.destroy();
        }

        self.inner.stack =  ManuallyDrop::new(stack);
        self.len.set_stack();
    }
}

impl<T, const N: usize> TinyVec<T, N> {

    /// Creates a new [TinyVec]
    pub const fn new() -> Self {
        let stack = [ const { MaybeUninit::uninit() }; N ];
        Self {
            inner: TinyVecInner { stack: ManuallyDrop::new(stack) },
            len: Length(0),
        }
    }

    /// Creates a new [TinyVec] with the specified initial capacity
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

    /// Returns true if the vector is currently using stack memory.
    ///
    /// This means that [Self::len] <= `N`
    #[inline]
    pub const fn lives_on_stack(&self) -> bool { self.len.is_stack() }

    /// Reserves space for, at least, n elements
    pub fn reserve(&mut self, n: usize) {
        if self.len.is_stack() {
            if self.len.get() + n > N {
                unsafe {
                    self.switch_to_heap(n);
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
        unsafe { self.push_unchecked(elem); }
    }

    /// Appends an element to the back of the vector without
    /// checking for space.
    ///
    /// # Safety
    /// The caller must ensure that there's enought capacity
    /// for this element.
    /// This means that [Self::len] < [Self::capacity]
    pub unsafe fn push_unchecked(&mut self, elem: T) {
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
            unsafe { self.push_unchecked(val); }
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
                unsafe { self.switch_to_heap(n); }
            }
        } else {
            let vec = unsafe { &mut self.inner.raw };
            let len = self.len.get();
            let new_cap = vec.cap.max(len + n);
            vec.expand_if_needed_exact(len, new_cap);
        }
    }

    /// # Safety
    /// Index should be < [TinyVec::len]\()
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
        Some(unsafe { self.remove_unchecked(index) })
    }

    /// Swaps the elements on index a and b
    ///
    /// # Panics
    /// If either a or b are out of bounds for [0, len)
    pub fn swap(&mut self, a: usize, b: usize) {
        self.swap_checked(a, b).unwrap_or_else(|| {
            panic!("Index out of bounds")
        });
    }

    /// Swaps the elements on index a and b
    ///
    /// Returns [None] if either a or b are out of bounds for [0, len)
    pub fn swap_checked(&mut self, a: usize, b: usize) -> Option<()> {
        if a >= self.len.get() {
            return None
        };
        if b >= self.len.get() {
            return None
        };
        unsafe { self.swap_unchecked(a, b); }
        Some(())
    }

    /// Swaps the elements on index a and b, without checking bounds
    ///
    /// # Safety
    /// The caller must ensure that both `a` and `b` are in bounds [0, len)
    /// For a checked version of this function, check [swap_checked](Self::swap_checked)
    pub unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        unsafe {
            let ap = self.ptr_mut().add(a);
            let bp = self.ptr_mut().add(b);
            let tmp = ap.read();
            ap.write(bp.read());
            bp.write(tmp);
        }
    }

    /// Removes the element at the given index by swaping it with the last one
    pub fn swap_remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len.get() {
            None
        } else if index == self.len.get() - 1 {
            self.pop()
        } else {
            unsafe { self.swap_unchecked(index, self.len.get() - 1) }
            self.pop()
        }
    }

    #[inline]
    /// Shrinks the capacity of the vector to fit exactly it's length
    pub fn shrink_to_fit(&mut self) {
        if self.len.is_stack() { return }

        if self.len.get() <= N {
            unsafe { self.switch_to_stack(); }
        } else {
            unsafe { self.inner.raw.shrink_to_fit(self.len.get()); };
        }
    }

    /// Copies all the elements of the given slice into the vector
    pub fn push_slice(&mut self, s: &[T])
    where
        T: Copy
    {
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

    /// Pushes all the available elements from the iterator into the vector
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
            unsafe { self.push_unchecked(elem); }
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

impl<T, const N: usize> FromIterator<T> for TinyVec<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let cap = match iter.size_hint() {
            (_, Some(max)) => max,
            (n, None) => n,
        };
        let mut vec = Self::with_capacity(cap);
        for elem in iter {
            unsafe { vec.push_unchecked(elem) };
        }
        vec
    }
}

#[cfg(test)]
mod test;
