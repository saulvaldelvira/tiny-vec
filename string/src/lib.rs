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

use core::ops::{Deref, DerefMut};
use core::str::Utf8Error;

use tiny_vec::TinyVec;

pub struct TinyString<const N: usize>(TinyVec<u8, N>);

impl<const N: usize> TinyString<N> {
    #[inline]
    pub const fn new() -> Self {
        Self(TinyVec::new())
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self(TinyVec::with_capacity(cap))

    }

    pub fn from_utf8(utf8: Vec<u8>) -> Result<Self,Utf8Error> {
        str::from_utf8(&utf8)?;
        Ok(Self(utf8.into()))
    }

    /// # Safety
    /// The caller must ensure that the given buffer is valid utf8
    #[inline(always)]
    pub const unsafe fn from_utf8_unchecked(utf8: TinyVec<u8, N>) -> Self {
        Self(utf8)
    }

    pub fn push(&mut self, c: char) {
        let len = c.len_utf8();
        let mut buf = [0_u8; 4];
        c.encode_utf8(&mut buf);
        self.0.push_slice(&buf[..len]);
    }

    pub fn push_str(&mut self, s: &str) {
        self.0.push_slice(s.as_bytes());
    }

    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }

    pub const fn capacity(&self) -> usize { self.0.capacity() }
}

impl<const N: usize> Default for TinyString<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deref for TinyString<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        unsafe {
            str::from_utf8_unchecked(&self.0)
        }
    }
}

impl<const N: usize> DerefMut for TinyString<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            str::from_utf8_unchecked_mut(&mut self.0)
        }
    }
}

impl<S, const N: usize> From<S> for TinyString<N>
where
    S: AsRef<str>,
{
    fn from(value: S) -> Self {
        let value = value.as_ref();
        let mut s = Self::with_capacity(value.len());
        s.push_str(value);
        s
    }
}

#[cfg(test)]
mod test;
