//! Cow implementation for TinyVec

use core::fmt::Debug;
use core::ops::{Add, AddAssign, Deref};

#[cfg(feature = "alloc")]
use alloc::{
    boxed::Box,
    string::String,
};

use crate::{TinyString, TinyVec};

/// A Copy-on-Write struct for a TinyVec
///
/// This struct contains either a borrowed reference of `[T]`,
/// or an owned TinyVec
///
/// # Example
/// ```
/// use tiny_str::{TinyString, Cow};
///
/// let string = TinyString::<5>::from("Hello, wo");
/// let string = Cow::from(string);
/// assert_eq!(&string, "Hello, wo");
/// assert!(string.is_owned());
///
/// let mut borrowed_cow = Cow::from(&string);
/// assert_eq!(borrowed_cow.as_str(), "Hello, wo");
/// assert!(borrowed_cow.is_borrowed());
///
/// borrowed_cow.to_mut().push_str("rld!");
/// assert_eq!(&string, "Hello, wo");
/// assert_eq!(borrowed_cow.as_str(), "Hello, world!");
/// assert!(borrowed_cow.is_owned());
/// ```
pub enum Cow<'borrow, const N: usize> {
    Borrowed(&'borrow str),
    Owned(TinyString<N>),
}

impl<'borrow, const N: usize> Cow<'borrow, N> {
    /// Converts this [Cow] into an [Owned](Cow::Owned) variant
    pub fn to_owned(&mut self) {
        if let Cow::Borrowed(b) = self {
            unsafe {
                let utf8 = TinyVec::from_slice_copied(b.as_bytes());
                let tv = TinyString::<N>::from_utf8_unchecked(utf8);
                *self = Cow::Owned(tv)
            }
        }
    }

    /// Consumes this [Cow] and returns an [Owned](Cow::Owned) variant
    pub fn into_owned(mut self) -> TinyString<N> {
        self.to_owned();
        match self {
            Cow::Owned(w) => w,
            Cow::Borrowed(_) => unreachable!("Self::to_owned must've turn self into an Owned variant"),
        }
    }

    /// Gets a mutable reference to the [Owned] variant.
    /// If this `Cow` is borrowed, it turns it into an [Owned]
    /// variant first
    ///
    /// [Owned]: Cow::Owned
    pub fn to_mut(&mut self) -> &mut TinyString<N> {
        self.to_owned();
        match self {
            Cow::Owned(w) => w,
            Cow::Borrowed(_) => unreachable!("Self::to_owned must've turn self into an Owned variant"),
        }
    }

    /// Returns true if `self` is a [Borrowed](Cow::Borrowed) variant
    pub const fn is_borrowed(&self) -> bool {
        matches!(self, Cow::Borrowed(_))
    }

    /// Returns true if `self` is an [Owned](Cow::Owned) variant
    pub const fn is_owned(&self) -> bool {
        matches!(self, Cow::Owned(_))
    }

    /// Returns true if this [Cow] lives on the stack.
    /// This is:
    /// - It is a [Borrowed](Cow::Borrowed) variant
    /// - It is an [Owned](Cow::Owned) variant that lives on the stack
    pub const fn lives_on_stack(&self) -> bool {
        match self {
            Cow::Borrowed(_) => true,
            Cow::Owned(v) => v.lives_on_stack(),
        }
    }

    /// Returns `self` as a string reference
    pub const fn as_str(&self) -> &str {
        match self {
            Cow::Borrowed(items) => items,
            Cow::Owned(tiny_string) => tiny_string.as_str()
        }
    }

    /// Returns `self` as a byte slice
    pub const fn as_bytes(&self) -> &[u8] {
        match self {
            Cow::Borrowed(b) => b.as_bytes(),
            Cow::Owned(s) => s.as_bytes(),
        }
    }
}

impl<'borrow, const N: usize> Deref for Cow<'borrow, N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<'borrow, const N: usize> From<&'borrow str> for Cow<'borrow, N> {
    fn from(value: &'borrow str) -> Self {
        Self::Borrowed(value)
    }
}

impl<'borrow, 'b2, const N: usize> From<&'b2 Cow<'borrow, N>> for Cow<'b2, N> {
    fn from(value: &'b2 Cow<'borrow, N>) -> Self {
        Cow::Borrowed(value.as_str())
    }
}

impl<'borrow, const N: usize> From<TinyString<N>> for Cow<'borrow, N> {
    fn from(value: TinyString<N>) -> Self {
        Self::Owned(value)
    }
}

impl<'borrow, const N: usize> From<&'borrow TinyString<N>> for Cow<'borrow, N> {
    fn from(value: &'borrow TinyString<N>) -> Self {
        Self::Borrowed(value)
    }
}

#[cfg(feature = "alloc")]
impl<'borrow, const N: usize> From<String> for Cow<'borrow, N> {
    fn from(value: String) -> Self {
        Self::Owned(TinyString::from(value))
    }
}

#[cfg(feature = "alloc")]
impl<'borrow, const N: usize> From<Box<str>> for Cow<'borrow, N> {
    fn from(value: Box<str>) -> Self {
        Self::Owned(TinyString::from(value))
    }
}

impl<'borrow, const N: usize> Debug for Cow<'borrow, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Borrowed(arg0) => f.debug_tuple("Borrowed").field(arg0).finish(),
            Self::Owned(arg0) => f.debug_tuple("Owned").field(arg0).finish(),
        }
    }
}

impl<'borrow, const N: usize> Eq for Cow<'borrow, N> {}
impl<'borrow, const N: usize> Ord for Cow<'borrow, N> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_bytes().cmp(other.as_bytes())
    }
}

impl<'borrow, const N: usize> PartialEq<Cow<'borrow, N>> for Cow<'borrow, N> {
    fn eq(&self, other: &Cow<'borrow, N>) -> bool {
        other.as_bytes() == self.as_bytes()
    }
}

impl<'borrow, const N: usize> PartialOrd<Cow<'borrow, N>> for Cow<'borrow, N> {
    fn partial_cmp(&self, other: &Cow<'borrow, N>) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'borrow, const N: usize> PartialEq<str> for Cow<'borrow, N> {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl<'borrow, const N: usize> PartialEq<Cow<'borrow, N>> for str {
    fn eq(&self, other: &Cow<'borrow, N>) -> bool {
        other.as_str() == self
    }
}

impl<'borrow, const N: usize> PartialEq<&str> for Cow<'borrow, N> {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl<'borrow, const N: usize> PartialEq<Cow<'borrow, N>> for &str {
    fn eq(&self, other: &Cow<'borrow, N>) -> bool {
        other.as_str() == *self
    }
}

impl<'borrow, const N: usize> PartialEq<[u8]> for Cow<'borrow, N> {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_bytes() == other
    }
}

impl<'borrow, const N: usize> PartialEq<Cow<'borrow, N>> for [u8]{
    fn eq(&self, other: &Cow<'borrow, N>) -> bool {
        other.as_bytes() == self
    }
}

impl<'borrow, const N: usize> PartialOrd<[u8]> for Cow<'borrow, N> {
    fn partial_cmp(&self, other: &[u8]) -> Option<core::cmp::Ordering> {
        self.as_bytes().partial_cmp(other)
    }
}

impl<'borrow, const N: usize> PartialOrd<Cow<'borrow, N>> for [u8]{
    fn partial_cmp(&self, other: &Cow<'borrow, N>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(other.as_bytes())
    }
}

impl<'borrow, const N: usize> PartialOrd<str> for Cow<'borrow, N> {
    fn partial_cmp(&self, other: &str) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl<'borrow, const N: usize> PartialOrd<Cow<'borrow, N>> for str {
    fn partial_cmp(&self, other: &Cow<'borrow, N>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl<'borrow, const N: usize> PartialOrd<&str> for Cow<'borrow, N> {
    fn partial_cmp(&self, other: &&str) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(*other)
    }
}

impl<'borrow, const N: usize> PartialOrd<Cow<'borrow, N>> for &str {
    fn partial_cmp(&self, other: &Cow<'borrow, N>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(&other.as_str())
    }
}

impl<'borrow, const N: usize> Clone for Cow<'borrow, N> {
    fn clone(&self) -> Self {
        match self {
            Self::Borrowed(arg0) => Self::Borrowed(arg0),
            Self::Owned(arg0) => Self::Owned(arg0.clone()),
        }
    }
}

impl<'borrow, const N: usize> Default for Cow<'borrow, N> {
    fn default() -> Self {
        Self::Borrowed("")
    }
}

impl<'borrow, const N: usize> Add for Cow<'borrow, N> {
    type Output = Cow<'borrow, N>;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'borrow, const N: usize> Add<&'borrow str> for Cow<'borrow, N> {
    type Output = Cow<'borrow, N>;

    fn add(mut self, rhs: &'borrow str) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'borrow, const N: usize> AddAssign<&'borrow str> for Cow<'borrow, N> {
    fn add_assign(&mut self, rhs: &'borrow str) {
        if self.is_empty() {
            *self = Cow::Borrowed(rhs)
        } else if !rhs.is_empty() {
            if let Cow::Borrowed(b) = self {
                let mut s = TinyString::with_capacity(b.len() + rhs.len());
                s.push_str(b);
                *self = Cow::Owned(s);
            }
            self.to_mut().push_str(rhs);
        }
    }
}

impl<'borrow, const N: usize> AddAssign<Cow<'borrow, N>> for Cow<'borrow, N> {
    fn add_assign(&mut self, rhs: Cow<'borrow, N>) {
        if self.is_empty() {
            *self = rhs;
        } else if !rhs.is_empty() {
            if let Cow::Borrowed(b) = self {
                let mut s = TinyString::with_capacity(b.len() + rhs.len());
                s.push_str(b);
                *self = Cow::Owned(s);
            }
            self.to_mut().push_str(&rhs);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn partial_eq() {
        let s = TinyString::<10>::from("ABCDEF");
        let cow = Cow::from(s);

        assert_eq!("ABCDEF", cow);
    }
}
