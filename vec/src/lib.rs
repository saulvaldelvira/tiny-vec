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

#![allow(incomplete_features)]
#![cfg_attr(feature = "nightly-const-generics", feature(generic_const_exprs))]

#![no_std]

extern crate alloc;
use alloc::vec::Vec;

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

    #[inline(always)]
    const unsafe fn as_ptr_stack(&self) -> *const T {
        unsafe { &self.stack as *const _ as *const T }
    }

    #[inline(always)]
    const unsafe fn as_ptr_stack_mut(&mut self) -> *mut T {
        unsafe { &mut self.stack as *mut _ as *mut T }
    }

    #[inline(always)]
    const unsafe fn as_ptr_heap(&self) -> *const T {
        unsafe { self.raw.ptr.as_ptr() }
    }

    #[inline(always)]
    const unsafe fn as_ptr_heap_mut(&mut self) -> *mut T {
        unsafe { self.raw.ptr.as_ptr() }
    }
}

#[repr(transparent)]
struct Length(usize);

impl Length {
    #[inline(always)]
    const fn new_stack(len: usize) -> Self {
        Self(len << 1)
    }

    #[inline(always)]
    const fn new_heap(len: usize) -> Self {
        Self(len << 1 | 0b1)
    }

    #[inline(always)]
    const fn is_stack(&self) -> bool {
        (self.0 & 0b1) == 0
    }

    #[inline(always)]
    const fn set_heap(&mut self) {
        self.0 |= 0b1;
    }

    #[inline(always)]
    const fn set_stack(&mut self) {
        self.0 &= 0b0;
    }

    #[inline(always)]
    const fn set(&mut self, n: usize) {
        self.0 &= 0b1;
        self.0 |= n << 1;
    }

    #[inline(always)]
    const fn get(&self) -> usize {
        self.0 >> 1
    }

    #[inline(always)]
    const fn add(&mut self, n: usize) {
        self.0 += n << 1;
    }

    #[inline(always)]
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

    /// Creates a new [TinyVec] from the given array
    pub const fn from_array(arr: [T; N]) -> Self {
        let md = ManuallyDrop::new(arr);
        /* TODO: Use MaybeUninit::transpose when stabilized
         * SAFETY: MaybeUninit<T> has the same memory layout as T */
        let arr: [MaybeUninit<T>; N] = unsafe { mem::transmute_copy(&md) };
        let arr = ManuallyDrop::new(arr);
        Self {
            inner: TinyVecInner { stack: arr },
            len: Length::new_stack(N)
        }
    }

    /// Returns the number of elements inside this vec
    #[inline]
    pub const fn len(&self) -> usize { self.len.get() }

    /// Returns true if the vector is empty
    #[inline]
    pub const fn is_empty(&self) -> bool { self.len.get() == 0 }

    /// Returns the allocated capacity for this vector
    #[inline]
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
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::new();
    ///
    /// for n in 0..5 {
    ///     vec.push(n)
    /// }
    ///
    /// assert!(vec.lives_on_stack());
    /// vec.push(6);
    /// assert!(!vec.lives_on_stack());
    /// ```
    #[inline]
    pub const fn lives_on_stack(&self) -> bool { self.len.is_stack() }

    /// Gets a const pointer to the vec's buffer
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        unsafe {
            if self.len.is_stack() {
                self.inner.as_ptr_stack()
            } else {
                self.inner.as_ptr_heap()
            }
        }
    }

    /// Gets a mutable pointer to the vec's buffer
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        unsafe {
            if self.len.is_stack() {
                self.inner.as_ptr_stack_mut()
            } else {
                self.inner.as_ptr_heap_mut()
            }
        }
    }

    /// Gets a mutable pointer to the vec's buffer as a [NonNull]
    #[inline]
    pub const fn as_non_null(&mut self) -> NonNull<T> {
        unsafe {
            NonNull::new_unchecked(self.as_mut_ptr())
        }
    }

    /// Gets a slice of the whole vector
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        unsafe {
            slice::from_raw_parts(self.as_ptr(), self.len.get())
        }
    }

    /// Gets a mutable slice of the whole vector
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe {
            slice::from_raw_parts_mut(self.as_mut_ptr(), self.len.get())
        }
    }

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
    #[inline]
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
            let dst = self.as_mut_ptr().add(self.len.get());
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
                self.as_ptr().add(self.len.get()).read()
            };
            Some(val)
        }
    }

    /// Inserts an element in the given index position
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
                self.as_ptr().add(index),
                self.as_mut_ptr().add(index + 1),
                self.len.get() - index,
            );
            self.as_mut_ptr().add(index).write(elem);
        }
        self.len.add(1);
    }

    /// Resizes the vector, cloning elem to fill any possible new slot
    pub fn resize(&mut self, cap: usize, elem: T)
    where
        T: Clone
    {
        if cap < self.len() {
            self.truncate(cap);
        } else {
            let n = self.len() - cap;
            self.reserve(n);

            unsafe {
                let mut ptr = self.as_mut_ptr().add(self.len());
                let len = &mut self.len;

                for _ in 1..n {
                    ptr::write(ptr, elem.clone());
                    ptr = ptr.add(1);
                    len.add(1);
                }

                if n > 0 {
                    ptr::write(ptr, elem);
                    len.add(1);
                }

            }
        }
    }

    /// Resizes the vector, using the given generator closure
    /// to fill any possible new slot
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut v = TinyVec::<i32, 10>::new();
    ///
    /// let mut n = 0;
    /// v.resize_with(5, || {
    ///     n += 1;
    ///     n
    /// });
    ///
    /// assert_eq!(v.len(), 5);
    /// assert_eq!(v.as_slice(), &[1, 2, 3, 4, 5]);
    /// ```
    pub fn resize_with<F>(&mut self, cap: usize, mut f: F)
    where
        F: FnMut() -> T
    {
        if cap < self.len() {
            self.truncate(cap);
        } else {
            let n = cap - self.len();
            self.reserve(n);

            unsafe {
                let mut ptr = self.as_mut_ptr().add(self.len());
                let len = &mut self.len;

                for _ in 0..n {
                    ptr::write(ptr, f());
                    ptr = ptr.add(1);
                    len.add(1);
                }
            }
        }
    }

    /// Resizes the vector, initializing the new elements to 0
    ///
    /// # Safety
    /// The caller must ensure that an all-zero byte representation
    /// is valid for T.
    ///
    /// If [mem::zeroed] is valid for T, this function is valid too
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut v = TinyVec::<_, 10>::from(&[1, 2, 3]);
    ///
    /// /* SAFETY: i32 can be initialized to 0b0 */
    /// unsafe { v.resize_zeroed(8); }
    ///
    /// /* The above is the same as
    ///    v.resize_with(8, || unsafe { core::mem::zeroed() }); */
    ///
    /// assert_eq!(v.len(), 8);
    /// assert_eq!(v.as_slice(), &[1, 2, 3, 0, 0, 0, 0, 0]);
    /// ```
    pub unsafe fn resize_zeroed(&mut self, cap: usize) {
        if cap < self.len() {
            self.truncate(cap);
        } else {
            let n = cap - self.len();
            self.reserve(n);
            unsafe {
                let ptr = self.as_mut_ptr().add(self.len());
                ptr.write_bytes(0, n);
            }
            self.len.add(n);
        }
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
            let result = self.as_mut_ptr().add(index).read();
            ptr::copy(
                self.as_ptr().add(index + 1),
                self.as_mut_ptr().add(index),
                self.len.get() - index,
            );
            result
        }
    }

    #[inline]
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len.get() { return None }
        /* Safety: We've just checked that index is < self.len */
        Some(unsafe { self.remove_unchecked(index) })
    }

    /// Swaps the elements on index a and b
    ///
    /// # Panics
    /// If either a or b are out of bounds for [0, len)
    #[inline]
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
    pub const unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        unsafe {
            let ap = self.as_mut_ptr().add(a);
            let bp = self.as_mut_ptr().add(b);
            ptr::swap(ap, bp);
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

    /// Sets the length of the vector.
    ///
    /// # Safety
    /// The caller must ensure that changing the length doesn't
    /// leave the vector in an inconsistent state. This is:
    ///
    /// - If you reduce de length, you may leak memory, if the type
    ///   stored need to be droped
    /// - If you extend the length, you may access uninitialized memory
    #[inline]
    pub const unsafe fn set_len(&mut self, len: usize) {
        self.len.set(len);
    }

    /// Reduces the length in the vector, dropping the elements
    /// in range [new_len, old_len)
    pub fn truncate(&mut self, len: usize) {
        if len < self.len.get() {
            for e in &mut self[len..] {
                unsafe { ptr::drop_in_place(e) }
            }
            unsafe { self.set_len(len); }
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
                self.as_mut_ptr().add(self.len.get()),
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
        self.as_slice()
    }
}


impl<T, const N: usize> DerefMut for TinyVec<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
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

impl<T: Copy, const N: usize> From<&[T]> for TinyVec<T, N> {
    fn from(value: &[T]) -> Self {
        let mut v = Self::with_capacity(value.len());
        v.push_slice(value);
        v
    }
}

impl<T: Copy, const N: usize, const M: usize> From<&[T; M]> for TinyVec<T, N> {
    fn from(value: &[T; M]) -> Self {
        Self::from(value as &[T])
    }
}

impl<T, const N: usize> From<[T; N]> for TinyVec<T, N> {
    fn from(value: [T; N]) -> Self {
        Self::from_array(value)
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
