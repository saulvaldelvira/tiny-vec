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
#![cfg_attr(feature = "use-nightly-features", feature(min_specialization, slice_swap_unchecked, generic_const_exprs))]

#![no_std]

extern crate alloc;
use alloc::vec::Vec;
use alloc::boxed::Box;

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

/// Macro to create [TinyVec]s
///
/// # Example
/// ```
/// use tiny_vec::{TinyVec, tinyvec};
///
/// // Create a TinyVec with a list of elements
/// let v: TinyVec<_, 10> = tinyvec![1, 2, 3, 4];
/// assert_eq!(&v[0..4], &[1, 2, 3, 4]);
///
/// // Create a TinyVec with 100 zeroes
/// let v: TinyVec<_, 10> = tinyvec![0; 100];
/// assert_eq!(v[20], 0);
/// ```
#[macro_export]
macro_rules! tinyvec {
    ($elem:expr; $n:expr) => ({
        let mut tv = $crate::TinyVec::new();
        tv.resize($n, $elem);
        tv
    });
    ($($x:expr),*$(,)?) => ({
        $crate::TinyVec::from(&[ $( $x ,)*])
    });
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
    #[cfg(not(feature = "use-nightly-features"))]
    const N: usize,

    #[cfg(feature = "use-nightly-features")]
    const N: usize = { n_elements_for_stack::<T>() },
> {
    inner: TinyVecInner<T, N>,
    len: Length,
}

impl<T, const N: usize> TinyVec<T, N> {

    unsafe fn switch_to_heap(&mut self, n: usize, exact: bool) {
        debug_assert!(self.lives_on_stack());

        let mut vec = RawVec::new();
        if exact {
            vec.expand_if_needed_exact(0, self.len.get() + n);
        } else {
            vec.expand_if_needed(0, self.len.get() + n);
        }
        unsafe {
            let src = self.inner.as_ptr_stack();
            let dst = vec.ptr.as_ptr();
            ptr::copy_nonoverlapping(src, dst, self.len());
            self.inner.raw = vec;
        }
        self.len.set_heap();
    }

    unsafe fn switch_to_stack(&mut self) {
        debug_assert!(!self.lives_on_stack());

        let mut rv = unsafe { self.inner.raw };

        let stack = [ const { MaybeUninit::uninit() }; N ];

        unsafe {
            let src = rv.ptr.as_ptr();
            let dst = stack.as_ptr() as *mut T;
            ptr::copy_nonoverlapping(src,dst,self.len());
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
            len: Length::new_stack(0),
        }
    }

    /// Creates a new [TinyVec] with the specified initial capacity
    pub fn with_capacity(cap: usize) -> Self {
        let mut len = Length(0);
        let inner = if cap <= N {
            let s = [const { MaybeUninit::uninit() }; N];
            TinyVecInner {
                stack: ManuallyDrop::new(s)
            }
        } else {
            len.set_heap();
            TinyVecInner {
                raw: RawVec::with_capacity(cap)
            }
        };

        Self { inner, len }
    }

    /// Creates a new [TinyVec] from the given array
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let tv = TinyVec::<i32, 10>::from_array([1, 2, 3, 4]);
    ///
    /// assert_eq!(tv.capacity(), 10);
    /// assert!(tv.lives_on_stack());
    /// ```
    pub fn from_array<const M: usize>(arr: [T; M]) -> Self {
        let arr = ManuallyDrop::new(arr);
        let mut tv = Self::with_capacity(M);

        let src = arr.as_ptr();
        let dst = tv.as_mut_ptr();

        unsafe {
            ptr::copy(src, dst, M);
            tv.set_len(M);
        }

        tv
    }

    /// Like [from_array](Self::from_array), but the array's length
    /// and the TinyVec's N are equal, so we can call it on const functions.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let tv = TinyVec::from_array_eq_size([1, 2, 3, 4]);
    ///
    /// assert_eq!(tv.capacity(), 4);
    /// assert!(tv.lives_on_stack());
    /// ```
    pub const fn from_array_eq_size(arr: [T; N]) -> Self {
        let mut tv = Self::new();

        let src = arr.as_ptr();
        let dst = tv.as_mut_ptr();

        unsafe {
            ptr::copy(src, dst, N);
            tv.set_len(N);
        }

        mem::forget(arr);
        tv
    }

    /// Creates a new [TinyVec] from the given [Vec]
    ///
    /// The returned TinyVec will have no extra capacity.
    /// This means that it won't reuse the Vec's buffer,
    /// and won't allocate more that vec.len() elements.
    ///
    /// If the vector has less than N elements, they'll
    /// be stored in the stack.
    ///
    /// If you want to reuse the Vec's buffer, use the
    /// [from_vec_reuse_buffer](Self::from_vec_reuse_buffer) function
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let vec = vec![1, 2, 3, 4, 5];
    ///
    /// let tv = TinyVec::<i32, 10>::from_vec(vec);
    ///
    /// /* vec fits on the stack, so it won't heap-allocate the TinyVec */
    /// assert!(tv.lives_on_stack());
    /// ```
    pub fn from_vec(mut vec: Vec<T>) -> Self {
        let mut tv = Self::with_capacity(vec.len());
        let dst = tv.as_mut_ptr();
        let src = vec.as_ptr();
        unsafe {
            ptr::copy(src, dst, vec.len());
            vec.set_len(0);
        }
        tv
    }

    /// Like [from_vec](Self::from_vec), but it reuses the
    /// [Vec]'s buffer.
    ///
    /// The returned TinyVec will have no extra capacity.
    /// This means that it won't reuse the Vec's buffer,
    /// and won't allocate more that vec.len() elements.
    ///
    /// For a version that creates a TinyVec with the mininum
    /// capacity for this vec, check [from_vec](Self::from_vec)
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let vec = vec![1, 2, 3, 4, 5];
    ///
    /// let tv = TinyVec::<i32, 10>::from_vec_reuse_buffer(vec);
    ///
    /// /* This version of from_vec, will use the same buffer vec used */
    /// assert!(!tv.lives_on_stack());
    /// ```
    pub fn from_vec_reuse_buffer(vec: Vec<T>) -> Self {
        let mut vec = ManuallyDrop::new(vec);

        let ptr = vec.as_mut_ptr();
        let ptr = unsafe { NonNull::new_unchecked(ptr) };

        let len = Length::new_heap(vec.len());
        let cap = vec.capacity();
        let raw = RawVec { cap, ptr };

        let inner = TinyVecInner { raw };
        Self { inner, len }
    }

    /// Creates a TinyVec from a boxed slice of T
    pub fn from_boxed_slice(boxed: Box<[T]>) -> Self {
        let len = boxed.len();
        let ptr = Box::into_raw(boxed);
        let ptr = unsafe { NonNull::new_unchecked(ptr as *mut T) };

        let raw = RawVec { ptr, cap: len };

        Self {
            inner: TinyVecInner { raw },
            len: Length::new_heap(len)
        }
    }

    /// Builds a TinyVec from a TinyVec with a different capacity generic parameter
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let v1 = TinyVec::<i32, 10>::from(&[1, 2, 3, 4]);
    ///
    /// let v2 = TinyVec::<i32, 7>::from_tiny_vec(v1.clone());
    /// assert!(v2.lives_on_stack());
    ///
    /// let v3 = TinyVec::<i32, 2>::from_tiny_vec(v1);
    /// /* v3 must be heap-allocated, since it can only store 2 elements
    ///    on the stack, and v1 has 3*/
    /// assert!(!v3.lives_on_stack());
    ///
    /// ```
    pub fn from_tiny_vec<const M: usize>(mut vec: TinyVec<T, M>) -> Self {
        let len = vec.len();
        if len > N && len > M {
            /* If the buffer must be on the heap on both src and dest,
             * just copy the RawVec from vec to Self */
            let tv = Self {
                len: Length::new_heap(len),
                inner: TinyVecInner {
                    raw: unsafe { vec.inner.raw }
                }
            };
            mem::forget(vec);
            return tv
        }

        let mut tv = Self::with_capacity(len);
        let src = vec.as_ptr();
        let dst = tv.as_mut_ptr();
        unsafe {
            /* SAFETY: src points to vec, and dst to tv. They are two different
             * objects, so their buffers can't overap */
            ptr::copy_nonoverlapping(src, dst, len);
            vec.set_len(0);
            tv.set_len(len);
        }
        tv
    }

    /// Creates a new [TinyVec] from the given slice.
    ///
    /// This function clones the elements in the slice.
    /// If the type T is [Copy], the [from_slice_copied](Self::from_slice_copied)
    /// function is a more optimized alternative
    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone
    {
        let mut v = Self::with_capacity(slice.len());
        v.extend_from_slice(slice);
        v
    }

    /// Creates a new [TinyVec] from the given slice.
    ///
    /// This function copies the slice into the buffer, which
    /// is faster that calling [clone](Clone::clone).
    /// That's why it requires T to implement [Copy].
    ///
    /// For a cloning alternative, use [from_slice](Self::from_slice)
    pub fn from_slice_copied(slice: &[T]) -> Self
    where
        T: Copy
    {
        let mut v = Self::with_capacity(slice.len());
        v.extend_from_slice_copied(slice);
        v
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
        debug_assert!(!self.as_mut_ptr().is_null());
        unsafe {
            /* SAFETY: as_mut_ptr should never return a null ptr */
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
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::new();
    ///
    /// assert_eq!(vec.capacity(), 5);
    /// assert!(vec.lives_on_stack());
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 10);
    /// assert!(!vec.lives_on_stack());
    /// ```
    pub fn reserve(&mut self, n: usize) {
        if self.len.is_stack() {
            if self.len.get() + n > N {
                unsafe { self.switch_to_heap(n, false); }
            }
        } else {
            unsafe {
                self.inner.raw.expand_if_needed(self.len.get(), n);
            }
        }
    }

    /// Reserves space for n more elements, but unline
    /// [reserve](Self::reserve), this function doesn't over-allocate.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::new();
    ///
    /// assert_eq!(vec.capacity(), 5);
    /// assert!(vec.lives_on_stack());
    /// vec.reserve_exact(10);
    /// assert_eq!(vec.capacity(), 10);
    /// assert!(!vec.lives_on_stack());
    /// ```
    pub fn reserve_exact(&mut self, n: usize) {
        if self.len.is_stack() {
            if self.len.get() + n > N {
                unsafe { self.switch_to_heap(n, true); }
            }
        } else {
            let vec = unsafe { &mut self.inner.raw };
            let len = self.len.get();
            let new_cap = vec.cap.max(len + n);
            vec.expand_if_needed_exact(len, new_cap);
        }
    }

    /// Appends an element to the back of the vector
    /// This operation is O(1), if no resize takes place.
    /// If the buffer needs to be resized, it has an O(n)
    /// time complexity.
    ///
    /// See also: [push_within_capacity](Self::push_within_capacity)
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::from(&[1, 2, 3, 4]);
    ///
    /// vec.push(5); // No resize. O(1)
    /// vec.push(6); // Resize, must realloc. O(n)
    ///
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5, 6]);
    /// ```
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
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 10>::with_capacity(10);
    ///
    /// // We've allocated a TinyVec with an initial capacity of 10.
    /// // We can skip the bounds checking, since there will be room
    /// // for all the elements on the iterator
    /// for n in 0..10 {
    ///     unsafe { vec.push_unchecked(n); }
    /// }
    /// assert_eq!(vec.as_slice(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
    /// ```
    pub unsafe fn push_unchecked(&mut self, elem: T) {
        unsafe {
            let dst = self.as_mut_ptr().add(self.len.get());
            dst.write(elem);
        }
        self.len.add(1);
    }

    /// Try to push an element inside the vector, only if
    /// there's room for it. If the push would've caused a
    /// reallocation of the buffer, returns the value wrapped
    /// on an [Err] variant.
    ///
    /// This operation has O(1) time complexity in all cases.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::from(&[1, 2, 3, 4]);
    ///
    /// assert!(vec.push_within_capacity(5).is_ok());
    ///
    /// // No room left, the value is returned
    /// assert_eq!(vec.push_within_capacity(6), Err(6));
    /// ```
    pub fn push_within_capacity(&mut self, val: T) -> Result<(),T> {
        if self.len.get() < self.capacity() {
            unsafe { self.push_unchecked(val); }
            Ok(())
        } else {
            Err(val)
        }
    }
    /// Removes the last element of this vector (if present)
    pub const fn pop(&mut self) -> Option<T> {
        if self.len.get() == 0 {
            None
        } else {
            self.len.sub(1);
            let val = unsafe {
                self.as_ptr()
                    .add(self.len.get())
                    .read()
            };
            Some(val)
        }
    }

    /// Inserts an element in the given index position
    ///
    /// This operation has a worst case time complexity of O(n),
    /// since it needs to move elements on range [index, len) one
    /// position to the right.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 10>::from(&[1, 2, 3, 4]);
    ///
    /// vec.insert(2, -1);
    /// assert_eq!(vec.as_slice(), &[1, 2, -1, 3, 4]);
    ///
    /// // An insert on vec.len() behaves like a push
    /// vec.insert(vec.len(), 5);
    /// assert_eq!(vec.as_slice(), &[1, 2, -1, 3, 4, 5]);
    /// ```
    pub fn insert(&mut self, index: usize, elem: T) -> Result<(),T> {
        if index > self.len.get() {
            return Err(elem)
        }
        unsafe { self.insert_unckecked(index, elem); }
        Ok(())
    }

    /// Like [insert](Self::insert), but without bounds checking
    ///
    /// # Safety
    /// The index should be <= self.len
    pub unsafe fn insert_unckecked(&mut self, index: usize, elem: T) {
        self.reserve(1);
        unsafe {
            let ptr = self.as_mut_ptr();
            ptr::copy(
                ptr.add(index),
                ptr.add(index + 1),
                self.len.get() - index,
            );
            ptr.add(index).write(elem);
        }
        self.len.add(1);
    }

    /// Inserts all the elements of the given slice into the
    /// vector, at the given index
    ///
    /// This function clones the elements in the slice.
    ///
    /// If the type T is [Copy], the [insert_slice_copied]
    /// function is a more optimized alternative
    ///
    /// # Errors
    /// If the index is out of bounds, returns the slice as an [Err] variant
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from(["abc".to_string(), "ghi".to_string()]);
    /// vec.insert_slice(1, &[
    ///     "__".to_string(),
    ///     "def".to_string(),
    ///     "__".to_string(),
    /// ]);
    ///
    /// assert_eq!(vec.as_slice(), &["abc", "__", "def", "__", "ghi"]);
    /// ```
    /// [insert_slice_copied]: Self::insert_slice_copied
    pub fn insert_slice<'a>(&mut self, index: usize, elems: &'a [T]) -> Result<(), &'a [T]>
    where
        T: Clone
    {
        self.insert_iter(index, elems.iter().cloned()).map_err(|_| elems)
    }

    /// Inserts all the elements of the given slice into the
    /// vector, at the given index
    ///
    /// This function copies the slice into the buffer, which
    /// is faster that calling [clone]
    /// That's why it requires T to implement [Copy].
    ///
    /// For a cloning alternative, use [insert_slice]
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4]);
    /// vec.insert_slice_copied(2, &[-1, -2, -3]);
    /// assert_eq!(vec.as_slice(), &[1, 2, -1, -2, -3, 3, 4]);
    /// ```
    /// [clone]: Clone::clone
    /// [insert_slice]: Self::insert_slice
    pub fn insert_slice_copied<'a>(&mut self, index: usize, elems: &'a [T]) -> Result<(), &'a [T]>
    where
        T: Copy
    {
        if index > self.len() {
            return Err(elems)
        }

        let len = elems.len();
        self.reserve(len);
        unsafe {
            let ptr = self.as_mut_ptr();
            ptr::copy(
                ptr.add(index),
                ptr.add(index + len),
                self.len.get() - index,
            );
            ptr::copy_nonoverlapping(
                elems.as_ptr(),
                ptr.add(index),
                len
            );
        }
        self.len.add(len);

        Ok(())
    }

    /// Inserts all the elements on the given iterator at the given index
    ///
    /// # Errors
    /// If the index is out of bounds, returns the passed iterator, wrapped
    /// on an [Err] variant.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4]);
    ///
    /// vec.insert_iter(2, (-3..-1));
    /// assert_eq!(vec.as_slice(), &[1, 2, -3, -2, 3, 4]);
    /// ```
    pub fn insert_iter<I>(&mut self, index: usize, it: I) -> Result<(), I>
    where
        I: IntoIterator<Item = T>,
        <I as IntoIterator>::IntoIter: ExactSizeIterator,
    {
        if index > self.len() {
            return Err(it);
        }

        let it = it.into_iter();
        let len = it.len();
        self.reserve(len);
        unsafe {
            let ptr = self.as_mut_ptr();
            ptr::copy(
                ptr.add(index),
                ptr.add(index + len),
                self.len.get() - index,
            );
            let mut ptr = ptr.add(index);
            for elem in it {
                ptr.write(elem);
                ptr = ptr.add(1);
                self.len.add(1);
            }
        }
        Ok(())
    }

    /// Resizes the vector, cloning elem to fill any possible new slots
    ///
    /// If new_len < self.len, behaves like [truncate](Self::truncate)
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::new();
    ///
    /// vec.resize(5, 0);
    /// assert_eq!(vec.len(), 5);
    /// assert_eq!(vec.as_slice(), &[0, 0, 0, 0, 0]);
    /// ```
    pub fn resize(&mut self, new_len: usize, elem: T)
    where
        T: Clone
    {
        if new_len < self.len() {
            self.truncate(new_len);
        } else {
            let n = new_len - self.len();
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
    /// to fill any possible new slots
    ///
    /// If new_len < self.len, behaves like [truncate](Self::truncate)
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

    /// Resizes the vector, initializing the new memory to 0
    ///
    /// # Safety
    /// The caller must ensure that an all-zero byte representation
    /// is valid for T.
    ///
    /// If [mem::zeroed] is valid for T, this function is valid too.
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

    /// Like [remove](Self::remove), but without bounds checking
    ///
    /// # Safety
    /// index must be within bounds (less than self.len)
    pub const unsafe fn remove_unchecked(&mut self, index: usize) -> T {
        debug_assert!(index < self.len());

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

    /// Removes the element at the given index.
    /// If the index is out of bounds, returns [None]
    #[inline]
    pub const fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len.get() { return None }
        /* SAFETY: We've just checked that index is < self.len */
        Some(unsafe { self.remove_unchecked(index) })
    }

    /// Swaps the elements on index a and b
    ///
    /// # Errors
    /// If an index is out of bounds for [0, len),
    /// returns that index inside an [Err] variant.
    pub const fn swap_checked(&mut self, a: usize, b: usize) -> Result<(),usize> {
        if a >= self.len.get() {
            return Err(a)
        };
        if b >= self.len.get() {
            return Err(b)
        };
        /* SAFETY: a and b are in bounds */
        unsafe { self.swap_unchecked(a, b); }
        Ok(())
    }
    /// Swaps the elements on index a and b, without checking bounds
    ///
    /// # Safety
    /// The caller must ensure that both `a` and `b` are in bounds [0, len)
    /// For a checked version of this function, check [swap_checked](Self::swap_checked)
    #[cfg(not(feature = "use-nightly-features"))]
    pub const unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        unsafe {
            let ptr = self.as_mut_ptr();
            let ap = ptr.add(a);
            let bp = ptr.add(b);
            ptr::swap(ap, bp);
        }
    }

    #[cfg(feature = "use-nightly-features")]
    #[inline(always)]
    const unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        unsafe { self.as_mut_slice().swap_unchecked(a, b); }
    }

    /// Removes the element at the given index by swaping it with the last one
    pub const fn swap_remove(&mut self, index: usize) -> Option<T> {
        if index >= self.len.get() {
            None
        } else if index == self.len.get() - 1 {
            self.pop()
        } else {
            /* SAFETY: index in < self.len */
            unsafe { self.swap_unchecked(index, self.len.get() - 1) }
            self.pop()
        }
    }

    /// Shrinks the capacity of the vector to fit exactly it's length
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        if self.len.is_stack() { return }

        /* SAFETY: It's safe to assume that we are on the heap,
         * because of the check above */
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
    ///
    /// If the new_len is >= old_len, this function does nothing.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4, 5]);
    /// vec.truncate(3);
    /// assert_eq!(vec.as_slice(), &[1, 2, 3]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if len < self.len.get() {
            for e in &mut self[len..] {
                unsafe { ptr::drop_in_place(e) }
            }
            unsafe { self.set_len(len); }
        }
    }

    /// Copies all the elements of the given slice into the vector
    ///
    /// This function clones the elements in the slice.
    ///
    /// If the type T is [Copy], the [extend_from_slice_copied]
    /// function is a more optimized alternative
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<String, 5>::new();
    /// vec.extend_from_slice(&[
    ///     "abc".to_string(),
    ///     "def".to_string(),
    ///     "__".to_string(),
    /// ]);
    ///
    /// assert_eq!(vec.as_slice(), &["abc", "def", "__"]);
    /// ```
    /// [extend_from_slice_copied]: Self::extend_from_slice_copied
    pub fn extend_from_slice(&mut self, s: &[T])
    where
        T: Clone
    {
        self.extend(s.iter().cloned());
    }

    /// Copies all the elements of the given slice into the vector
    ///
    /// This function copies the slice into the buffer, which
    /// is faster that calling [clone]
    /// That's why it requires T to implement [Copy].
    ///
    /// For a cloning alternative, use [extend_from_slice]
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 5>::new();
    /// vec.extend_from_slice_copied(&[1, 2, 3, 4]);
    ///
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    /// ```
    /// [clone]: Clone::clone
    /// [extend_from_slice]: Self::extend_from_slice
    pub fn extend_from_slice_copied(&mut self, s: &[T])
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

    /// Converts this [TinyVec] into a boxed slice
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut v = TinyVec::<_, 10>::from(&[1, 2, 3, 4]);
    /// let b = v.into_boxed_slice();
    ///
    /// assert_eq!(&b[..], [1, 2, 3, 4]);
    /// ```
    pub fn into_boxed_slice(self) -> Box<[T]> {
        let mut vec = ManuallyDrop::new(self);

        if vec.lives_on_stack() {
            unsafe { vec.switch_to_heap(0, true) };
        }
        debug_assert!(!vec.lives_on_stack());

        let len = vec.len();
        unsafe { vec.inner.raw.shrink_to_fit(len); }
        debug_assert_eq!(len, vec.capacity());

        let ptr = vec.as_mut_ptr();
        unsafe {
            let slice = slice::from_raw_parts_mut(ptr, len);
            Box::from_raw(slice)
        }
    }

    /// Converts this [TinyVec] into a standard [Vec]
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut v = TinyVec::from([1, 2, 3, 4]);
    /// let b = v.into_vec();
    ///
    /// assert_eq!(&b[..], &[1, 2, 3, 4]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        let mut vec = ManuallyDrop::new(self);

        if vec.lives_on_stack() {
            unsafe { vec.switch_to_heap(0, false) };
        }

        let ptr = vec.as_mut_ptr();
        let len = vec.len();
        let cap = vec.capacity();

        unsafe { Vec::from_raw_parts(ptr, len, cap) }
    }
}

impl<T, const N: usize> Extend<T> for TinyVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();

        let (min, max) = iter.size_hint();
        let reserve = match max {
            Some(max) => max,
            None => min,
        };

        if reserve > 0 {
            self.reserve(reserve);
        }

        for elem in iter {
            unsafe { self.push_unchecked(elem); }
        }
    }
}

#[cfg(feature = "use-nightly-features")]
macro_rules! maybe_default {
    ($($t:tt)*) => {
        default $($t)*
    };
}

#[cfg(not(feature = "use-nightly-features"))]
macro_rules! maybe_default {
    ($($t:tt)*) => {
        $($t)*
    };
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

impl<T: PartialEq, const N: usize, S> PartialEq<S> for TinyVec<T, N>
where
    S: AsRef<[T]>,
{
    fn eq(&self, other: &S) -> bool {
        self.as_slice() == other.as_ref()
    }
}

impl<T: PartialEq, const N: usize> Eq for TinyVec<T, N> {}

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

macro_rules! impl_from_call {
    ($( $({$($im:tt)*})? $t:ty => $c:ident ),* $(,)?) => {
       $(
            impl<T, const N: usize, $($($im)*)?> From<$t> for TinyVec<T, N> {
                fn from(value: $t) -> Self {
                    Self:: $c (value)
                }
            }
       )*
    };
}

impl_from_call! {
    Vec<T> => from_vec,
    Box<[T]> => from_boxed_slice,
    [T; N] => from_array_eq_size,
}

macro_rules! impl_from_call_w_copy_spec {
    ( $( $({$($im:tt)*})? $t:ty => $def_call:ident, $copy_call:ident ;)* ) => {
       $(
            impl<T: Clone, const N: usize, $( $($im)* )? > From<$t> for TinyVec<T, N> {
                maybe_default!(
                    fn from(value: $t) -> Self {
                        Self:: $def_call (value)
                    }
                );
            }

            #[cfg(feature = "use-nightly-features")]
            impl<T: Clone + Copy, const N: usize, $( $($im)* )? > From<$t> for TinyVec<T, N> {
                fn from(value: $t) -> Self {
                    Self:: $copy_call (value)
                }
            }
       )*
    };
}

impl_from_call_w_copy_spec! {
    &[T] => from_slice, from_slice_copied;
    &mut [T] => from_slice, from_slice_copied;

    { const M: usize } &[T; M] => from_slice, from_slice_copied;
    { const M: usize } &mut [T; M] => from_slice, from_slice_copied;
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

impl<T, const N: usize> From<TinyVec<T, N>> for Vec<T> {
    fn from(value: TinyVec<T, N>) -> Self {
        value.into_vec()
    }
}

impl<T, const N: usize> AsRef<[T]> for TinyVec<T, N> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> AsMut<[T]> for TinyVec<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T: Clone, const N: usize> Clone for TinyVec<T, N> {
    maybe_default!(
        fn clone(&self) -> Self {
            Self::from_slice(self.as_slice())
        }
    );
}

#[cfg(feature = "use-nightly-features")]
impl<T: Clone + Copy, const N: usize> Clone for TinyVec<T, N> {
    fn clone(&self) -> Self {
        Self::from_slice_copied(self.as_slice())
    }
}

#[cfg(test)]
mod test;
