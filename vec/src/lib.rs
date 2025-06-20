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
#![cfg_attr(not(feature = "alloc"), doc = "
# WARNING
The `alloc` feature is disabled. This means that a `TinyVec` won't be able to
grow over it's stack capacity.

The following functions from [TinyVec] can cause the program to panic if the vector exceeds its
capacity.
- [with_capacity]
- [from_array](TinyVec::from_array)
- [from_tiny_vec](TinyVec::from_tiny_vec)
- [from_slice_copied](TinyVec::from_slice_copied)
- [repeat](TinyVec::repeat)
- [reserve]
- [reserve_exact]
- [push]
- [push_unchecked](TinyVec::push_unchecked)
- [insert](TinyVec::insert)
- [insert_unchecked](TinyVec::insert_unchecked)
- [insert_slice](TinyVec::insert_slice)
- [insert_slice_copied](TinyVec::insert_slice_copied)
- [insert_iter](TinyVec::insert_iter)
- [resize](TinyVec::resize)
- [reserve](TinyVec::reserve)
- [resize_with](TinyVec::resize_with)
- [resize_zeroed](TinyVec::resize_zeroed)
- [extend_from_slice](TinyVec::extend_from_slice)
- [extend_from_slice_copied](TinyVec::extend_from_slice_copied)
- [extend_from_within](TinyVec::extend_from_within)
- [extend_from_within_copied](TinyVec::extend_from_within_copied)
- [append](TinyVec::append)

## Alternatives
| May Panic | No Panic |
| --------- | -------- |
|  [push]   | [push_within_capacity](TinyVec::push_within_capacity) |
|  [reserve]   | [try_reserve](TinyVec::try_reserve) |
|  [reserve_exact]   | [try_reserve_exact](TinyVec::try_reserve) |
| [with_capacity] | [try_with_capacity](TinyVec::try_with_capacity) |

[push]: TinyVec::push
[reserve]: TinyVec::reserve
[reserve_exact]: TinyVec::reserve_exact
[with_capacity]: TinyVec::with_capacity
")]
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
#![cfg_attr(feature = "use-nightly-features", feature(extend_one, extend_one_unchecked))]
#![cfg_attr(feature = "use-nightly-features", feature(iter_advance_by))]

#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
use alloc::{
    vec::Vec,
    boxed::Box
};
use drain::Drain;
use extract_if::ExtractIf;

use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Bound, Deref, DerefMut, Range, RangeBounds};
use core::ptr::NonNull;
use core::{fmt, ptr};
use core::slice;

mod raw;
use raw::RawVec;
pub use raw::ResizeError;

mod cow;
pub use cow::Cow;

pub mod iter;
pub mod drain;
pub mod extract_if;

union TinyVecInner<T, const N: usize> {
    stack: ManuallyDrop<[MaybeUninit<T>; N]>,
    raw: RawVec<T>,
}

impl<T, const N: usize> TinyVecInner<T, N> {
    #[inline(always)]
    const unsafe fn as_ptr_stack(&self) -> *const T {
        unsafe { &raw const self.stack as *const T }
    }

    #[inline(always)]
    const unsafe fn as_ptr_stack_mut(&mut self) -> *mut T {
        unsafe { &raw mut self.stack as *mut T }
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
    #[cfg(feature = "alloc")]
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
    #[cfg(feature = "alloc")]
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
    (@one $e:expr) => { 1 };
    () => {
        $crate::TinyVec::new()
    };
    ($elem:expr; $n:expr) => ({
        let mut tv = $crate::TinyVec::new();
        tv.resize($n, $elem);
        tv
    });
    ($($x:expr),+ $(,)?) => ({
        let n = const {
            0 $( + $crate::tinyvec!(@one $x) )+
        };
        let mut vec = $crate::TinyVec::with_capacity(n);
        $(vec.push($x);)+
        vec
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
    n_elements_for_bytes::<T>(mem::size_of::<RawVec<T>>())
}

/// The maximun number of elements of type T, that can be stored on
/// the given byte size
///
/// # Examples
/// ```
/// use tiny_vec::n_elements_for_bytes;
///
/// assert_eq!(n_elements_for_bytes::<u8>(2), 2);
/// assert_eq!(n_elements_for_bytes::<u16>(4), 2);
/// assert_eq!(n_elements_for_bytes::<i32>(17), 4);
/// ```
pub const fn n_elements_for_bytes<T>(n: usize) -> usize {
    let size = mem::size_of::<T>();
    if size == 0 {
        isize::MAX as usize
    } else {
        n / size
    }
}

fn slice_range<R>(range: R, len: usize) -> Range<usize>
where
    R: RangeBounds<usize>
{
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

    Range { start, end }
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

    unsafe fn switch_to_heap(&mut self, n: usize, exact: bool) -> Result<(), ResizeError> {
        debug_assert!(self.lives_on_stack());
        debug_assert_ne!(mem::size_of::<T>(), 0);

        let mut vec = RawVec::new();
        if exact {
            vec.try_expand_if_needed_exact(0, self.len.get() + n)?;
        } else {
            vec.try_expand_if_needed(0, self.len.get() + n)?;
        }
        unsafe {
            let src = self.inner.as_ptr_stack();
            let dst = vec.ptr.as_ptr();
            ptr::copy_nonoverlapping(src, dst, self.len());
            self.inner.raw = vec;
        }
        self.len.set_heap();

        Ok(())
    }

    #[cfg(feature = "alloc")]
    unsafe fn switch_to_stack(&mut self) {
        debug_assert!(!self.lives_on_stack());
        debug_assert_ne!(mem::size_of::<T>(), 0,
            "We shouldn't call switch_to_stack, since T is a ZST, and\
            shouldn't be moved to the heap in the first place");

        let mut rv = unsafe { self.inner.raw };

        let stack = [const { MaybeUninit::uninit() }; N];

        unsafe {
            let src = rv.ptr.as_ptr();
            let dst = stack.as_ptr() as *mut T;
            ptr::copy_nonoverlapping(src,dst,self.len());
            rv.destroy();
        }

        self.inner.stack =  ManuallyDrop::new(stack);
        self.len.set_stack();
    }

    const unsafe fn split_at_spare_mut_with_len(&mut self) -> (&mut [T], &mut [MaybeUninit<T>], &mut Length) {
        unsafe {
            let len = self.len();
            let ptr = self.as_mut_ptr();

            let spare_ptr = ptr.add(len).cast::<MaybeUninit<T>>();
            let spare_len = self.capacity() - len;

            let slice = slice::from_raw_parts_mut(ptr, len);
            let spare_slice = slice::from_raw_parts_mut(spare_ptr, spare_len);

            (slice, spare_slice, &mut self.len)
        }
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
        Self::try_with_capacity(cap).unwrap_or_else(|err| err.handle())
    }

    /// Like [with_capacity](Self::with_capacity), but it returns a [Result].
    ///
    /// If an allocation error hapens when reserving the memory, returns
    /// a [ResizeError] unlike [with_capacity](Self::with_capacity), which
    /// panics in such case.
    pub fn try_with_capacity(cap: usize) -> Result<Self,ResizeError> {
        let mut len = Length(0);
        let inner = if cap <= N {
            let s = [const { MaybeUninit::uninit() }; N];
            TinyVecInner {
                stack: ManuallyDrop::new(s)
            }
        } else {
            len.set_heap();
            TinyVecInner {
                raw: RawVec::try_with_capacity(cap)?
            }
        };

        Ok(Self { inner, len })
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
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let vec = vec![1, 2, 3, 4, 5];
    ///
    /// let tv = TinyVec::<i32, 10>::from_vec(vec);
    ///
    /// assert_eq!(tv, &[1, 2, 3, 4, 5]);
    /// ```
    #[cfg(feature = "alloc")]
    pub fn from_vec(vec: Vec<T>) -> Self {
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
    #[cfg(feature = "alloc")]
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
    /// ```
    pub fn from_tiny_vec<const M: usize>(mut vec: TinyVec<T, M>) -> Self {
        let len = vec.len();
        if len > N && len > M {
            #[cfg(feature = "alloc")] {
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
            #[cfg(not(feature = "alloc"))]
            unreachable!("The length of vec won't be higher that it's capacity, \
                so this branch will NEVER be reached");
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
        v.extend_from_slice_impl(slice);
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

    /// Creates a new [TinyVec] by copying the given
    /// `slice` `n` times.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let vec = TinyVec::<i32, 10>::repeat(
    ///     &[1, 2, 3, 4],
    ///     3
    /// );
    ///
    /// assert_eq!(vec, &[1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4]);
    /// ```
    pub fn repeat(slice: &[T], n: usize) -> Self
    where
        T: Copy
    {
        let mut s = Self::with_capacity(slice.len() * n);
        let mut dst = s.as_mut_ptr();
        let src = slice.as_ptr();
        let len = slice.len();
        for _ in 0..n {
            unsafe {
                ptr::copy(src, dst, len);
                dst = dst.add(len);
            }
        }
        s.len.set(len * n);
        s
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
        if mem::size_of::<T>() == 0 {
            return isize::MAX as usize
        }
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
    /// # Panics
    /// If an allocation error happens. For a non-panicking version
    /// see [try_reserve](Self::try_reserve)
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
    #[inline]
    pub fn reserve(&mut self, n: usize) {
        self.try_reserve(n).unwrap_or_else(|err| err.handle());
    }

    /// Like [reserve](Self::reserve), but on failure returns an [Err] variant
    /// with a [ResizeError], instead of panicking.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::{TinyVec, ResizeError};
    ///
    /// let mut tv = TinyVec::<u64, 10>::new();
    ///
    /// assert_eq!(
    ///     tv.try_reserve(isize::MAX as usize),
    ///     Err(ResizeError::AllocationExceedsMaximun)
    /// );
    /// ```
    pub fn try_reserve(&mut self, n: usize) -> Result<(), ResizeError> {
        if self.len.is_stack() {
            if self.len.get() + n > self.capacity() {
                unsafe { self.switch_to_heap(n, false)?; }
            }
        } else {
            unsafe {
                self.inner.raw.try_expand_if_needed(self.len.get(), n)?;
            }
        }
        Ok(())
    }

    /// Reserves space for n more elements, but unline
    /// [reserve](Self::reserve), this function doesn't over-allocate.
    ///
    /// # Panics
    /// If an allocation error happens. For a non-panicking version
    /// see [try_reserve_exact](Self::try_reserve_exact)
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
        self.try_reserve_exact(n).unwrap_or_else(|err| err.handle())
    }

    /// Like [resize](Self::resize), but on failure returns an [Err] variant
    /// with a [ResizeError], instead of panicking.
    pub fn try_reserve_exact(&mut self, n: usize) -> Result<(), ResizeError> {
        if self.len.is_stack() {
            if self.len.get() + n > self.capacity() {
                unsafe { self.switch_to_heap(n, true)?; }
            }
        } else {
            let vec = unsafe { &mut self.inner.raw };
            let len = self.len.get();
            let new_cap = vec.cap.max(len + n);
            vec.try_expand_if_needed_exact(len, new_cap)?;
        }
        Ok(())
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

    /// Removes and returns the last element from a vector if the `predicate`
    /// returns true, or [None] if the predicate returns false or the vector
    /// is empty (the predicate will not be called in that case).
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4]);
    /// let pred = |x: &mut i32| *x % 2 == 0;
    ///
    /// assert_eq!(vec.pop_if(pred), Some(4));
    /// assert_eq!(vec, [1, 2, 3]);
    /// assert_eq!(vec.pop_if(pred), None);
    /// ```
    pub fn pop_if<F>(&mut self, predicate: F) -> Option<T>
    where
        F: FnOnce(&mut T) -> bool
    {
        let len = self.len();
        if len == 0 { return None }

        unsafe {
            let last = self.as_mut_ptr().add(len - 1);
            predicate(&mut *last).then(|| {
                self.len.sub(1);
                last.read()
            })
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
        unsafe { self.insert_unchecked(index, elem); }
        Ok(())
    }

    /// Like [insert](Self::insert), but without bounds checking
    ///
    /// # Safety
    /// The index should be <= self.len
    pub unsafe fn insert_unchecked(&mut self, index: usize, elem: T) {
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
    #[inline]
    pub fn insert_slice<'a>(&mut self, index: usize, elems: &'a [T]) -> Result<(), &'a [T]>
    where
        T: Clone
    {
        self.insert_slice_impl(index, elems)
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
            self.resize_impl(new_len, elem);
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

    /// Removes and returns the element at the given `index` from a `self`
    /// if the `predicate` returns true, or [None] if the predicate returns
    /// false or the `index` is out of bounds (the predicate will not be called
    /// in that case).
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4]);
    /// let pred = |x: &mut i32| *x % 2 == 0;
    ///
    /// assert_eq!(vec.remove_if(1, pred), Some(2));
    /// assert_eq!(vec, [1, 3, 4]);
    /// assert_eq!(vec.remove_if(0, pred), None);
    /// ```
    pub fn remove_if<F>(&mut self, index: usize, predicate: F) -> Option<T>
    where
        F: FnOnce(&mut T) -> bool
    {
        let len = self.len.get();
        if index >= len { return None }

        unsafe {
            let ptr = self.as_mut_ptr().add(index);
            predicate(&mut *ptr).then(|| {
                let elem = ptr.read();
                ptr::copy(
                    ptr.add(1),
                    ptr,
                    len - index - 1
                );
                self.len.sub(1);
                elem
            })
        }
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

    /// Removes consecutive repeated elements in `self` according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    /// ```
    /// use tiny_vec::TinyVec;
    /// let mut vec = TinyVec::from([1, 2, 2, 3, 2]);
    /// vec.dedup();
    /// assert_eq!(vec, [1, 2, 3, 2]);
    /// ```
    #[inline]
    pub fn dedup(&mut self)
    where
        T: PartialEq
    {
        self.dedup_by(|a, b| a == b);
    }

    /// Removes all but the first of consecutive elements in the
    /// vector that resolve to the same key.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    /// ```
    /// use tiny_vec::TinyVec;
    /// let mut vec = TinyVec::from([10, 20, 21, 30, 20]);
    ///
    /// vec.dedup_by_key(|i| *i / 10);
    /// assert_eq!(vec, [10, 20, 30, 20]);
    /// ```
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq
    {
        self.dedup_by(|a, b| key(a) == key(b));
    }

    /// Removes all but the first of consecutive elements in `self` satisfying
    /// a given equality relation.
    ///
    /// The `are_equal` function is passed references to two elements from the vector and
    /// must determine if the elements compare equal. The elements are passed in opposite order
    /// from their order in the slice, so if `same_bucket(a, b)` returns `true`, `a` is removed.
    ///
    /// If the vector is sorted, this removes all duplicates.
    ///
    /// # Examples
    /// ```
    /// use tiny_vec::TinyVec;
    /// let mut vec = TinyVec::from(["foo", "bar", "Bar", "baz", "bar"]);
    ///
    /// vec.dedup_by(|a, b| a.eq_ignore_ascii_case(b));
    ///
    /// assert_eq!(vec, ["foo", "bar", "baz", "bar"]);
    /// ```
    pub fn dedup_by<F>(&mut self, mut are_equal: F)
    where
        F: FnMut(&mut T, &mut T) -> bool
    {
        let (ptr, _, len) = unsafe { self.split_at_spare_mut_with_len() };
        let ptr = ptr.as_mut_ptr();

        if len.get() <= 1 {
            return
        }

        let mut first_dup = 1;
        while first_dup != len.get() {
           let is_dup = unsafe {
                let a = ptr.add(first_dup - 1);
                let b = ptr.add(first_dup);
                are_equal(&mut *b, &mut *a)
           };
           if is_dup {
               break
           }
           first_dup += 1;
        }
        if first_dup == len.get() {
            return;
        }

        struct DropGuard<'a, T> {
            len: &'a mut Length,
            ptr: *mut T,
            right: usize,
            left: usize,
        }

        impl<T> Drop for DropGuard<'_, T> {
            fn drop(&mut self) {
                unsafe {
                    let len = self.len.get();

                    let shift = len - self.right;
                    let src = self.ptr.add(self.right);
                    let dst = self.ptr.add(self.left);
                    ptr::copy(src, dst, shift);

                    let deleted = self.right - self.left;
                    self.len.sub(deleted);
                }
            }
        }

        let mut guard = DropGuard { right: first_dup + 1, left: first_dup, ptr, len };
        unsafe { ptr::drop_in_place(ptr.add(first_dup)); }
        while guard.right < guard.len.get() {
            unsafe {
                let a = ptr.add(guard.left - 1);
                let b = ptr.add(guard.right);

                if are_equal(&mut *b, &mut *a) {
                    guard.right += 1;
                    ptr::drop_in_place(b);
                } else {
                    let dst = ptr.add(guard.left);
                    ptr::copy_nonoverlapping(b, dst, 1);
                    guard.left += 1;
                    guard.right += 1;
                }
            }
        }

        guard.len.set(guard.left);
        mem::forget(guard);
    }

    /// Shrinks the capacity of the vector to fit exactly it's length
    ///
    /// If the vector lives on the heap, but it's length fits inside the
    /// stack-allocated buffer `self.len <= N`, it deallocates the heap
    /// buffer and moves the contents to the stack.
    ///
    /// If you need a function that doesn't move the buffer to the stack,
    /// use the [shrink_to_fit_heap_only](Self::shrink_to_fit_heap_only) function.
    #[cfg(feature = "alloc")]
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

    /// Moves this `TinyVec` to the heap
    #[cfg(feature = "alloc")]
    pub fn move_to_heap(&mut self) {
        self.try_move_to_heap().unwrap_or_else(|err| err.handle());
    }

    /// Like [move_to_heap](Self::move_to_heap), but returns a result
    /// in case the allocation fail
    #[cfg(feature = "alloc")]
    pub fn try_move_to_heap(&mut self) -> Result<(), ResizeError> {
        if self.lives_on_stack() {
            unsafe { self.switch_to_heap(0, false)? };
        }
        Ok(())
    }

    /// Moves this `TinyVec` to the heap, without allocating more
    /// than `self.len` elements
    #[cfg(feature = "alloc")]
    pub fn move_to_heap_exact(&mut self) {
        self.try_move_to_heap_exact().unwrap_or_else(|err| err.handle());
    }

    /// Like [move_to_heap_exact](Self::move_to_heap_exact), but returns a result
    /// in case the allocation fail
    #[cfg(feature = "alloc")]
    pub fn try_move_to_heap_exact(&mut self) -> Result<(), ResizeError> {
        if self.lives_on_stack() {
            unsafe { self.switch_to_heap(0, true)? };
        }
        Ok(())
    }

    /// Shrinks the capacity of the vector to fit exactly it's length.
    ///
    /// Unlike [shrink_to_fit](Self::shrink_to_fit), this function doesn't
    /// move the buffer to the stack, even if the length of `self`, could
    /// fit on the stack space.
    #[cfg(feature = "alloc")]
    pub fn shrink_to_fit_heap_only(&mut self) {
        if !self.len.is_stack() {
            unsafe { self.inner.raw.shrink_to_fit(self.len.get()); };
        }
    }

    /// Clears all the elements of this vector
    ///
    /// # Example
    /// ```
    /// use tiny_vec::{TinyVec, tinyvec};
    ///
    /// let mut vec: TinyVec<_, 5> = tinyvec![1, 2, 3, 4, 5];
    /// vec.clear();
    ///
    /// assert!(vec.is_empty());
    /// assert_eq!(vec.as_slice(), &[]);
    /// ```
    pub fn clear(&mut self) {
        let ptr = self.as_mut_slice() as *mut [T];
        unsafe {
            self.len.set(0);
            ptr::drop_in_place(ptr);
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

    /// Updates the length of the vector using the given closure.
    ///
    /// This is just the same as getting the len using [Self::len], and
    /// then using [Self::set_len].
    ///
    /// *This is a low level api*. Use it only if you know what you're doing.
    ///
    /// # Safety
    /// Just like [Self::set_len], you need to make sure that changing the
    /// vector length doesn't leave the vector in an inconsistent state, or
    /// leaks memory.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::<i32, 10>::with_capacity(10);
    ///
    /// unsafe {
    ///     let mut dst = vec.as_mut_ptr();
    ///     let src = &[1, 2, 3, 4] as *const i32;
    ///     core::ptr::copy(src, dst, 4);
    ///     vec.update_len(|len| *len += 4);
    ///     // Same as:
    ///     // let len = vec.len();
    ///     // len.set_len(len + 4);
    /// }
    /// ```
    pub unsafe fn update_len<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut usize)
    {
        let mut len = self.len.get();
        f(&mut len);
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
    #[inline]
    pub fn extend_from_slice(&mut self, s: &[T])
    where
        T: Clone
    {
        self.extend_from_slice_impl(s);
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
    #[inline]
    pub fn extend_from_slice_copied(&mut self, s: &[T])
    where
        T: Copy
    {
        let len = s.len();
        self.reserve(len);

        unsafe {
            /* SAFETY: We've just reserved space for `len` elements */
            ptr::copy(
                s.as_ptr(),
                self.as_mut_ptr().add(self.len.get()),
                len
            )
        }

        self.len.add(len);
    }

    /// Copies the slice from the given range to the back
    /// of this vector.
    ///
    /// # Panics
    /// Panics if the range is invalid for [0, self.len)
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
    ///
    /// vec.extend_from_within(3..=5);
    ///
    /// assert_eq!(vec, &[1, 2, 3, 4, 5, 6, 7, 8, 4, 5, 6]);
    /// ```
    #[inline]
    pub fn extend_from_within<R>(&mut self, range: R)
    where
        T: Clone,
        R: RangeBounds<usize>,
    {
        self.extend_from_within_impl(range);
    }

    /// Like [extend_from_within](Self::extend_from_within),
    /// but optimized for [Copy] types
    pub fn extend_from_within_copied<R>(&mut self, range: R)
    where
        T: Copy,
        R: RangeBounds<usize>,
    {
        let len = self.len();
        let Range { start, end } = slice_range(range, len);

        let new_len = end - start;
        self.reserve(new_len);

        let ptr = self.as_mut_ptr();
        unsafe {
            let src = ptr.add(start);
            let dst = ptr.add(len);
            ptr::copy(src, dst, new_len);
        }
        self.len.add(new_len);
    }

    /// Retains in this vector only the elements that match
    /// the given predicate
    ///
    /// This is the same as calling
    /// `self.extract_if(.., |e| !pred(e)).for_each(|e| drop(e))`
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
    /// vec.retain(|&n| n % 2 == 0);
    /// assert_eq!(vec, &[2, 4, 6, 8]);
    /// ```
    pub fn retain<F>(&mut self, mut pred: F)
    where
        F: FnMut(&T) -> bool
    {
        self.retain_mut(|e| pred(e));
    }

    /// Like [retain](Self::retain), but the predicate receives a
    /// mutable reference to the element.
    ///
    /// # Example
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3, 4, 5, 6, 7, 8]);
    /// vec.retain_mut(|n| {
    ///     let is_even = *n % 2 == 0;
    ///     *n *= 2;
    ///     is_even
    /// });
    /// assert_eq!(vec, &[4, 8, 12, 16]);
    /// ```
    pub fn retain_mut<F>(&mut self, mut pred: F)
    where
        F: FnMut(&mut T) -> bool
    {
        /* TODO: We can probably optimize this */
        for e in self.extract_if(.., |e| !pred(e)) {
            drop(e)
        }
    }

    /// Returns vector content as a slice of `T`, along with the remaining spare
    /// capacity of the vector as a slice of `MaybeUninit<T>`.
    ///
    /// The returned spare capacity slice can be used to fill the vector with data
    /// (e.g. by reading from a file) before marking the data as initialized using
    /// the [`set_len`], or [`update_len`] methods.
    ///
    /// [`set_len`]: TinyVec::set_len
    /// [`update_len`]: TinyVec::update_len
    ///
    /// Note that this is a low-level API, which should be used with care for
    /// optimization purposes. If you need to append data to a `Vec`
    /// you can use [`push`], [`extend`], [`extend_from_slice`],
    /// [`extend_from_within`], [`insert`], [`append`], [`resize`] or
    /// [`resize_with`], depending on your exact needs.
    ///
    /// [`push`]: TinyVec::push
    /// [`extend`]: TinyVec::extend
    /// [`extend_from_slice`]: TinyVec::extend_from_slice
    /// [`extend_from_within`]: TinyVec::extend_from_within
    /// [`insert`]: TinyVec::insert
    /// [`append`]: TinyVec::append
    /// [`resize`]: TinyVec::resize
    /// [`resize_with`]: TinyVec::resize_with
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut v = TinyVec::from([1, 1, 2]);
    ///
    /// // Reserve additional space big enough for 10 elements.
    /// v.reserve(10);
    ///
    /// let (init, uninit) = v.split_at_spare_mut();
    /// let sum = init.iter().copied().sum::<u32>();
    ///
    /// // Fill in the next 4 elements.
    /// uninit[0].write(sum);
    /// uninit[1].write(sum * 2);
    /// uninit[2].write(sum * 3);
    /// uninit[3].write(sum * 4);
    ///
    /// // Mark the 4 elements of the vector as being initialized.
    /// unsafe {
    ///     let len = v.len();
    ///     v.set_len(len + 4);
    /// }
    ///
    /// assert_eq!(&v, &[1, 1, 2, 4, 8, 12, 16]);
    /// ```
    pub const fn split_at_spare_mut(&mut self) -> (&mut [T], &mut [MaybeUninit<T>]) {
        let (init, uninit, _) = unsafe { self.split_at_spare_mut_with_len() };
        (init, uninit)
    }

    /// Splits the collection into two at the given index.
    ///
    /// Returns a newly allocated vector containing the elements in the range
    /// `[at, len)`. After the call, the original vector will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// - If you want to take ownership of the entire contents and capacity of
    ///   the vector, see [`mem::take`] or [`mem::replace`].
    /// - If you don't need the returned vector at all, see [`TinyVec::truncate`].
    /// - If you want to take ownership of an arbitrary subslice, or you don't
    ///   necessarily want to store the removed items in a vector, see [`TinyVec::drain`].
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from(['a', 'b', 'c']);
    /// let vec2 = vec.split_off(1);
    /// assert_eq!(vec, ['a']);
    /// assert_eq!(vec2, ['b', 'c']);
    /// ```
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> TinyVec<T , N>  {
        if at >= self.len() {
            panic!("Index out of bounds");
        }
        let other_len = self.len() - at;
        let mut other = TinyVec::<T, N>::with_capacity(other_len);

        unsafe {
            let src = self.as_ptr().add(at);
            let dst = other.as_mut_ptr();
            ptr::copy_nonoverlapping(src, dst, other_len);
            other.set_len(other_len);
            self.len.sub(other_len);
        }
        other
    }

    /// Consumes and leaks the `TinyVec`, returning a mutable reference to the contents,
    /// `&'a mut [T]`.
    ///
    /// Note that the type `T` must outlive the chosen lifetime `'a`. If the type
    /// has only static references, or none at all, then this may be chosen to be
    /// `'static`.
    ///
    /// This method shrinks the buffer, and moves it to the heap in case it lived
    /// on the stack.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak.
    ///
    /// # Examples
    ///
    /// ```
    /// let x = tiny_vec::TinyVec::from([1, 2, 3]);
    ///
    /// let static_ref: &'static mut [usize] = x.leak();
    /// static_ref[0] += 1;
    ///
    /// assert_eq!(static_ref, &[2, 2, 3]);
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe { Box::from_raw(static_ref) });
    /// ```
    #[cfg(feature = "alloc")]
    pub fn leak<'a>(self) -> &'a mut [T]
    where
        T: 'a
    {
        let mut slf = ManuallyDrop::new(self);
        unsafe {
            let len = slf.len();
            slf.shrink_to_fit_heap_only();
            slf.move_to_heap_exact();
            let ptr = slf.as_mut_ptr();
            slice::from_raw_parts_mut(ptr, len)
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_vec::TinyVec;
    ///
    /// let mut vec = TinyVec::from([1, 2, 3]);
    /// let mut vec2 = TinyVec::from([4, 5, 6]);
    /// vec.append(&mut vec2);
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6]);
    /// assert_eq!(vec2, []);
    /// ```
    pub fn append<const M: usize>(&mut self, other: &mut TinyVec<T, M>) {
       unsafe {
           let other_len = other.len();
           self.reserve(other_len);

           let src = other.as_slice().as_ptr();
           let dst = self.as_mut_ptr().add(self.len());
           ptr::copy(src, dst, other_len);

           other.set_len(0);
           self.len.add(other_len);
       }
    }

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
        let Range { start, end } = slice_range(range, len);

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
    #[cfg(feature = "alloc")]
    pub fn into_boxed_slice(self) -> Box<[T]> {
        let mut slf = ManuallyDrop::new(self);

        if slf.lives_on_stack() {
            unsafe { slf.switch_to_heap(0, true).unwrap_or_else(|err| err.handle()) };
        }
        debug_assert!(!slf.lives_on_stack());

        let len = slf.len();
        slf.shrink_to_fit_heap_only();
        debug_assert_eq!(len, slf.capacity());

        let ptr = slf.as_mut_ptr();
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
    #[cfg(feature = "alloc")]
    pub fn into_vec(self) -> Vec<T> {
        let mut vec = ManuallyDrop::new(self);
        vec.move_to_heap();

        let ptr = vec.as_mut_ptr();
        let len = vec.len();
        let cap = vec.capacity();

        unsafe { Vec::from_raw_parts(ptr, len, cap) }
    }
}

impl<T, const N: usize> Extend<T> for TinyVec<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iter = iter.into_iter();

        let (lower, _) = iter.size_hint();
        self.reserve(lower);

        for elem in iter {
            unsafe { self.push_unchecked(elem); }
        }
    }

    #[cfg(feature = "use-nightly-features")]
    fn extend_one(&mut self, item: T) {
        self.push(item);
    }

    #[cfg(feature = "use-nightly-features")]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }

    #[cfg(feature = "use-nightly-features")]
    unsafe fn extend_one_unchecked(&mut self, item: T) {
        /* SAFETY: The caller guarantees that self.len < self.capacity */
        unsafe { self.push_unchecked(item); }
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

trait CopyOptimization<T> {
    fn extend_from_slice_impl(&mut self, s: &[T]);
    fn insert_slice_impl<'a>(&mut self, index: usize, elems: &'a [T]) -> Result<(), &'a [T]>;
    fn resize_impl(&mut self, new_len: usize, elem: T);
    fn extend_from_within_impl<R>(&mut self, range: R)
    where
        R: RangeBounds<usize>;
}

impl<T: Clone, const N: usize> CopyOptimization<T> for TinyVec<T, N> {
    maybe_default! {
        fn extend_from_slice_impl(&mut self, s: &[T]) {
            self.extend(s.iter().cloned());
        }
    }

    maybe_default! {
        fn insert_slice_impl<'a>(&mut self, index: usize, elems: &'a [T]) -> Result<(), &'a [T]> {
            self.insert_iter(index, elems.iter().cloned()).map_err(|_| elems)
        }
    }

    maybe_default! {
        fn extend_from_within_impl<R>(&mut self, range: R)
        where
            R: RangeBounds<usize>
        {
            let len = self.len();
            let Range { start, end } = slice_range(range, len);

            self.reserve(end - start);

            let (slice, spare, len) = unsafe { self.split_at_spare_mut_with_len() };
            let slice = &slice[start..end];

            for (src, dst) in slice.iter().zip(spare.iter_mut()) {
                dst.write(src.clone());
                len.add(1);
            }
        }
    }

    maybe_default! {
        fn resize_impl(&mut self, new_len: usize, elem: T) {
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

}

#[cfg(feature = "use-nightly-features")]
impl<T: Copy, const N: usize> CopyOptimization<T> for TinyVec<T, N> {

    #[inline]
    fn extend_from_slice_impl(&mut self, s: &[T]) {
        self.extend_from_slice_copied(s);
    }

    #[inline]
    fn insert_slice_impl<'a>(&mut self, index: usize, elems: &'a [T]) -> Result<(), &'a [T]> {
        self.insert_slice_copied(index, elems)
    }

    #[inline]
    fn extend_from_within_impl<R>(&mut self, range: R)
    where
        R: RangeBounds<usize>
    {
        self.extend_from_within_copied(range);
    }

    #[inline]
    fn resize_impl(&mut self, new_len: usize, elem: T) {
        let n = new_len - self.len();
        self.reserve(n);

        unsafe {
            let mut ptr = self.as_mut_ptr().add(self.len());

            for _ in 0..n {
                ptr::write(ptr, elem);
                ptr = ptr.add(1);
            }

            self.len.add(n);
        }
    }
}

impl<T, const N: usize> Default for TinyVec<T, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug, const N: usize> fmt::Debug for TinyVec<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)
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

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> DerefMut for TinyVec<T, N> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> Drop for TinyVec<T, N> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            for e in self.as_mut_slice() {
                unsafe { ptr::drop_in_place(e) };
            }
        }
        if !self.len.is_stack() {
            unsafe { self.inner.raw.destroy(); }
        }
    }
}

macro_rules! impl_from_call {
    ($( $({$($im:tt)*})? $(where { $($w:tt)* })? $t:ty => $c:ident ),* $(,)?) => {
       $(
            impl<T, const N: usize, $($($im)*)?> From<$t> for TinyVec<T, N>
            $(where $($w)* )?
            {
                fn from(value: $t) -> Self {
                    Self:: $c (value)
                }
            }
       )*
    };
}

#[cfg(feature = "alloc")]
impl_from_call! {
    Vec<T> => from_vec,
    Box<[T]> => from_boxed_slice,
}

impl_from_call! {
    [T; N] => from_array_eq_size,

    where { T: Clone } &[T] => from_slice,
    where { T: Clone } &mut [T] => from_slice,

    { const M: usize } where { T: Clone } &[T; M] => from_slice,
    { const M: usize } where { T: Clone } &mut [T; M] => from_slice,
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

#[cfg(feature = "alloc")]
impl<T, const N: usize> From<TinyVec<T, N>> for Vec<T> {
    #[inline]
    fn from(value: TinyVec<T, N>) -> Self {
        value.into_vec()
    }
}

impl<T, const N: usize> AsRef<[T]> for TinyVec<T, N> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> AsMut<[T]> for TinyVec<T, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T: Clone, const N: usize> Clone for TinyVec<T, N> {
    fn clone(&self) -> Self {
        Self::from_slice(self.as_slice())
    }
}

#[cfg(test)]
mod test;
