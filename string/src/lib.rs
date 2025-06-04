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

//! Tiny string
//!
//! A string that can store a small amount of bytes on the stack.
//!
//! This struct provides a string-like API, but performs SSO (Small String Optimization)
//! This means that a `TinyString<N>` stores up to N bytes on the stack.
//! If the string grows bigger than that, it moves the contents to the heap.
//!
//! # Example
//! ```
//! use tiny_str::TinyString;
//!
//! let mut s = TinyString::<10>::new();
//!
//! for (i, c) in (b'0'..=b'9').enumerate() {
//!     s.push(c as char);
//!     assert_eq!(s.len(), i + 1);
//! }
//!
//! // Up to this point, no heap allocations are needed.
//! // The string is stored on the stack.
//!
//! s.push_str("abc"); // This moves the string to the heap
//!
//! assert_eq!(&s[..], "0123456789abc")
//! ```
//!
//! # Memory layout
//! TinyString is based on [TinyVec], just like [alloc::string::String] if based
//! on [alloc::vec::Vec].
//!
//! You can read the [tiny_vec] crate documentation to learn about the internal
//! representation of the data.

#![no_std]

#![cfg_attr(feature = "use-nightly-features", feature(extend_one))]

use core::fmt::{self, Display};
use core::ops::{Bound, Deref, DerefMut, Range, RangeBounds};
use core::str::{self, FromStr, Utf8Error};

extern crate alloc;
use alloc::vec::Vec;
use alloc::boxed::Box;

use tiny_vec::TinyVec;
pub mod iter;

pub mod drain;

const MAX_N_STACK_ELEMENTS: usize = tiny_vec::n_elements_for_stack::<u8>();

/// A string that can store a small amount of bytes on the stack.
pub struct TinyString<const N: usize = MAX_N_STACK_ELEMENTS> {
    buf: TinyVec<u8, N>,
}

impl<const N: usize> TinyString<N> {
    fn slice_range<R>(&self, range: R, len: usize) -> Range<usize>
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
        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        Range { start, end }
    }
}

impl<const N: usize> TinyString<N> {

    /// Creates a new [TinyString]
    #[inline]
    pub const fn new() -> Self {
        Self { buf: TinyVec::new() }
    }

    /// Creates a new [TinyString] with the given capacity
    pub fn with_capacity(cap: usize) -> Self {
        Self { buf: TinyVec::with_capacity(cap) }
    }

    /// Creates a new [TinyString] from the given utf8 buffer.
    ///
    /// # Errors
    /// If the byte buffer contains invalid uft8
    pub fn from_utf8(utf8: TinyVec<u8, N>) -> Result<Self,Utf8Error> {
        str::from_utf8(utf8.as_slice())?;
        Ok(Self { buf: utf8 })
    }

    /// Creates a new [TinyString] from the given utf8 buffer.
    ///
    /// # Safety
    /// The caller must ensure that the given contains valid utf8
    #[inline(always)]
    pub const unsafe fn from_utf8_unchecked(utf8: TinyVec<u8, N>) -> Self {
        Self { buf: utf8 }
    }

    /// Returns the number of elements inside this string
    #[inline]
    pub const fn len(&self) -> usize { self.buf.len() }

    /// Returns true if the string is empty
    #[inline]
    pub const fn is_empty(&self) -> bool { self.buf.is_empty() }

    /// Returns the allocated capacity for this string
    #[inline]
    pub const fn capacity(&self) -> usize { self.buf.capacity() }

    /// Returns a str slice
    #[inline]
    pub const fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.buf.as_slice()) }
    }

    /// Returns a mutable str slice
    #[inline]
    pub const fn as_mut_str(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.buf.as_mut_slice()) }
    }

    /// Returns a const pointer to the buffer
    ///
    /// This method shadows [str::as_ptr], to avoid a deref
    #[inline]
    pub const fn as_ptr(&self) -> *const u8 {
        self.buf.as_ptr()
    }

    /// Returns a mutable pointer to the buffer
    ///
    /// This method shadows [str::as_mut_ptr], to avoid a deref
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut u8 {
        self.buf.as_mut_ptr()
    }

    /// Returns the string as a byte slice
    #[inline]
    pub const fn as_bytes(&self) -> &[u8] {
        self.buf.as_slice()
    }

    /// Pushes a character into the string
    pub fn push(&mut self, c: char) {
        let len = c.len_utf8();
        if len == 1 {
            self.buf.push(c as u8);
        } else {
            let mut buf = [0_u8; 4];
            c.encode_utf8(&mut buf);
            self.buf.extend_from_slice(&buf[..len]);
        }
    }

    /// Returns the last char of this string, if present
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let mut s = TinyString::<10>::new();
    ///
    /// s.push_str("abcd");
    ///
    /// assert_eq!(s.pop(), Some('d'));
    /// assert_eq!(s, "abc");
    /// ```
    pub fn pop(&mut self) -> Option<char> {
        let c = self.chars().next_back()?;
        let new_len = self.len() - c.len_utf8();
        unsafe {
            self.buf.set_len(new_len);
        }
        Some(c)
    }

    /// Pushes a str slice into this string
    #[inline]
    pub fn push_str(&mut self, s: &str) {
        self.buf.extend_from_slice_copied(s.as_bytes());
    }

    /// Shrinks the capacity of this string to fit exactly it's length
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.buf.shrink_to_fit();
    }

    /// Clears the string
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let mut s: TinyString<5> = TinyString::from("Hello");
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(s.as_str(), "");
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.buf.clear();
    }

    /// Reserves space for, at least, n bytes
    #[inline]
    pub fn reserve(&mut self, n: usize) {
        self.buf.reserve(n);
    }

    /// Reserves space for exactly n more bytes
    #[inline]
    pub fn reserve_exact(&mut self, n: usize) {
        self.buf.reserve_exact(n);
    }

    /// Converts this TinyString into a boxed str
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let mut s = TinyString::<10>::new();
    /// s.push_str("abc");
    ///
    /// let b = s.into_boxed_str();
    /// assert_eq!(&*b, "abc");
    /// ```
    pub fn into_boxed_str(self) -> Box<str> {
        let b = self.buf.into_boxed_slice();
        unsafe { alloc::str::from_boxed_utf8_unchecked(b) }
    }

    /// Copies the slice from the given range to the back
    /// of this string.
    ///
    /// # Panics
    /// - If the range is invalid for [0, self.len)
    /// - If either the start or the end of the range fall
    ///   outside a char boundary
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let mut s = TinyString::<10>::from("abcdefg");
    ///
    /// s.extend_from_within(3..=5);
    ///
    /// assert_eq!(s, "abcdefgdef");
    /// ```
    pub fn extend_from_within<R>(&mut self, range: R)
    where
        R: RangeBounds<usize>
    {
        let Range { start, end } = self.slice_range(range, self.len());
        self.buf.extend_from_within_copied(start..end);
    }

    /// Consumes and leaks the `TinyString`, returning a mutable reference to the contents,
    /// `&'a mut str`.
    ///
    /// This method shrinks the buffer, and moves it to the heap in case it lived
    /// on the stack.
    ///
    /// This function is mainly useful for data that lives for the remainder of
    /// the program's life. Dropping the returned reference will cause a memory
    /// leak.
    ///
    /// # Example
    /// ```
    /// let x = tiny_str::TinyString::<10>::from("ABCDEFG");
    ///
    /// let static_ref: &'static mut str = x.leak();
    /// static_ref.make_ascii_lowercase();
    ///
    /// assert_eq!(static_ref, "abcdefg");
    /// # // FIXME(https://github.com/rust-lang/miri/issues/3670):
    /// # // use -Zmiri-disable-leak-check instead of unleaking in tests meant to leak.
    /// # drop(unsafe{Box::from_raw(static_ref)})
    /// ```
    pub fn leak<'a>(mut self) -> &'a mut str {
        self.buf.move_to_heap_exact();
        self.buf.shrink_to_fit_heap_only();
        unsafe {
            let bytes = self.buf.leak();
            str::from_utf8_unchecked_mut(bytes)
        }
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a newly allocated `String`. `self` contains bytes `[0, at)`, and
    /// the returned `String` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    /// ```
    /// let mut hello = tiny_str::TinyString::<8>::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// ```
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> TinyString<N> {
        assert!(self.is_char_boundary(at));
        let other = self.buf.split_off(at);
        unsafe { TinyString::from_utf8_unchecked(other) }
    }

    /// Shortens this `TinyString` to the specified length.
    ///
    /// If `new_len` is greater than or equal to the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Example
    /// ```
    /// let mut s = tiny_str::TinyString::<6>::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!(s, "he");
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        assert!(self.is_char_boundary(new_len));
        self.buf.truncate(new_len);
    }
}

impl<const N: usize> Default for TinyString<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deref for TinyString<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> DerefMut for TinyString<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_str()
    }
}

impl<const N: usize> From<&str> for TinyString<N> {
    fn from(value: &str) -> Self {
        let mut s = Self::with_capacity(value.len());
        s.push_str(value);
        s
    }
}

impl<const N: usize> TryFrom<&[u8]> for TinyString<N> {
    type Error = Utf8Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        str::from_utf8(value)?;
        Ok(unsafe { Self::from_utf8_unchecked(TinyVec::from_slice_copied(value)) })
    }
}

impl<const N: usize> TryFrom<TinyVec<u8, N>> for TinyString<N> {
    type Error = Utf8Error;

    fn try_from(value: TinyVec<u8, N>) -> Result<Self, Self::Error> {
        Self::from_utf8(value)
    }
}

impl<const N: usize> TryFrom<Vec<u8>> for TinyString<N> {
    type Error = Utf8Error;

    fn try_from(value: Vec<u8>) -> Result<Self, Self::Error> {
        str::from_utf8(value.as_slice())?;
        Ok(unsafe { Self::from_utf8_unchecked(TinyVec::from_vec(value)) })
    }
}

impl<const N: usize> From<TinyString<N>> for TinyVec<u8, N> {
    fn from(value: TinyString<N>) -> Self {
        value.buf
    }
}

impl<const N: usize> From<TinyString<N>> for Vec<u8> {
    fn from(value: TinyString<N>) -> Self {
        value.buf.into_vec()
    }
}

impl<const N: usize> From<TinyString<N>> for Box<str> {
    fn from(value: TinyString<N>) -> Self {
        value.into_boxed_str()
    }
}

impl<const N: usize> FromIterator<char> for TinyString<N> {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

impl<const N: usize> Extend<char> for TinyString<N> {
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let cap = match iter.size_hint() {
            (_, Some(n)) => n,
            (n, _) => n,
        };
        self.reserve(cap);
        for c in iter {
            self.push(c);
        }
    }

    #[cfg(feature = "use-nightly-features")]
    fn extend_one(&mut self, item: char) {
        self.push(item);
    }
}

impl<const N: usize, S> PartialEq<S> for TinyString<N>
where
    S: AsRef<[u8]>
{
    fn eq(&self, other: &S) -> bool {
        self.as_bytes() == other.as_ref()
    }
}

impl<const N: usize> Eq for TinyString<N> { }

impl<const N: usize> AsRef<[u8]> for TinyString<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> AsRef<str> for TinyString<N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsMut<str> for TinyString<N> {
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> fmt::Debug for TinyString<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:?}", self.bytes())
    }
}

impl<const N: usize> Display for TinyString<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<const N: usize> FromStr for TinyString<N> {
    type Err = core::convert::Infallible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self::from(s))
    }
}

#[cfg(test)]
mod test;
