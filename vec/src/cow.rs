//! Cow implementation for TinyVec

use core::fmt::Debug;
use core::ops::Deref;

#[cfg(feature = "alloc")]
use alloc::{
    boxed::Box,
    vec::Vec
};

use crate::TinyVec;

/// A Copy-on-Write struct for a TinyVec
///
/// This struct contains either a borrowed reference of [T],
/// or an owned TinyVec
///
/// # Example
/// ```
/// use tiny_vec::{TinyVec, Cow};
///
/// let vec = TinyVec::<i32, 5>::from([1, 2, 3, 4, 5]);
/// let vec = Cow::from(vec);
///
/// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
///
/// let mut borrowed_cow = Cow::from(&vec);
/// assert_eq!(borrowed_cow.as_slice(), &[1, 2, 3, 4, 5]);
/// assert!(borrowed_cow.is_borrowed());
///
/// borrowed_cow.to_mut().push(6);
/// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
/// assert_eq!(borrowed_cow.as_slice(), &[1, 2, 3, 4, 5, 6]);
/// assert!(borrowed_cow.is_owned());
/// ```
pub enum Cow<'borrow, T, const N: usize> {
    Borrowed(&'borrow [T]),
    Owned(TinyVec<T, N>),
}

impl<'borrow, T, const N: usize> Cow<'borrow, T, N> {
    /// Converts this [Cow] into an [Owned](Cow::Owned) variant
    pub fn to_owned(&mut self)
    where
        T: Clone
    {
        if let Cow::Borrowed(b) = self {
            let tv = TinyVec::<T, N>::from_slice(b);
            *self = Cow::Owned(tv)
        }
    }

    /// Consumes this [Cow] and returns an [Owned](Cow::Owned) variant
    pub fn into_owned(mut self) -> TinyVec<T, N>
    where
        T: Clone
    {
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
    pub fn to_mut(&mut self) -> &mut TinyVec<T, N>
    where
        T: Clone
    {
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

    /// Returns `self` as a slice of T
    pub const fn as_slice(&self) -> &[T] {
        match self {
            Cow::Borrowed(items) => items,
            Cow::Owned(tiny_vec) => tiny_vec.as_slice()
        }
    }
}

impl<'borrow, T, const N: usize> Deref for Cow<'borrow, T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<'borrow, T, const N: usize> From<&'borrow [T]> for Cow<'borrow, T, N> {
    fn from(value: &'borrow [T]) -> Self {
        Self::Borrowed(value)
    }
}

impl<'borrow, 'b2, T, const N: usize> From<&'b2 Cow<'borrow, T, N>> for Cow<'b2 , T, N> {
    fn from(value: &'b2 Cow<'borrow, T, N>) -> Self {
        Self::Borrowed(value.as_slice())
    }
}

impl<'borrow, T, const N: usize, const M: usize> From<&'borrow [T; M]> for Cow<'borrow, T, N> {
    fn from(value: &'borrow [T; M]) -> Self {
        Self::Borrowed(value)
    }
}

impl<'borrow, T, const N: usize> From<TinyVec<T, N>> for Cow<'borrow, T, N> {
    fn from(value: TinyVec<T, N>) -> Self {
        Self::Owned(value)
    }
}

#[cfg(feature = "alloc")]
impl<'borrow, T, const N: usize> From<Vec<T>> for Cow<'borrow, T, N> {
    fn from(value: Vec<T>) -> Self {
        Self::Owned(TinyVec::from(value))
    }
}

#[cfg(feature = "alloc")]
impl<'borrow, T, const N: usize> From<Box<[T]>> for Cow<'borrow, T, N> {
    fn from(value: Box<[T]>) -> Self {
        Self::Owned(TinyVec::from(value))
    }
}

#[cfg(feature = "alloc")]
impl<'borrow, T, const N: usize> From<&'borrow Vec<T>> for Cow<'borrow, T, N> {
    fn from(value: &'borrow Vec<T>) -> Self {
        Self::Borrowed(value)
    }
}

#[cfg(feature = "alloc")]
impl<'borrow, T, const N: usize> From<&'borrow Box<[T]>> for Cow<'borrow, T, N> {
    fn from(value: &'borrow Box<[T]>) -> Self {
        Self::Borrowed(value)
    }
}

impl<'borrow, T: Debug, const N: usize> Debug for Cow<'borrow, T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Borrowed(arg0) => f.debug_tuple("Borrowed").field(arg0).finish(),
            Self::Owned(arg0) => f.debug_tuple("Owned").field(arg0).finish(),
        }
    }
}

impl<'borrow, T: PartialEq, const N: usize> PartialEq for Cow<'borrow, T, N> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Borrowed(l0), Self::Borrowed(r0)) => l0 == r0,
            (Self::Owned(l0), Self::Owned(r0)) => l0 == r0,
            _ => false,
        }
    }
}

impl<'borrow, T: Clone, const N: usize> Clone for Cow<'borrow, T, N> {
    fn clone(&self) -> Self {
        match self {
            Self::Borrowed(arg0) => Self::Borrowed(arg0),
            Self::Owned(arg0) => Self::Owned(arg0.clone()),
        }
    }
}

impl<'borrow, T, const N: usize> Default for Cow<'borrow, T, N> {
    fn default() -> Self {
        Self::Borrowed(&[])
    }
}
