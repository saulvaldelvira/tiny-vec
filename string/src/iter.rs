//! Iterators for the TinyString

use core::iter::FusedIterator;
use core::str::Chars;

use crate::TinyString;

/// Iterator over the characers of a [TinyString]
///
/// This struct is built from the [TinyString::into_chars] function
pub struct TinyStringChars<const N: usize> {
    buf: tiny_vec::iter::TinyVecIter<u8, N>,
}

impl<const N: usize> TinyStringChars<N> {
    /// Casts the remaining portion of this iterator as a str
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.buf.as_slice()) }
    }

    /// Casts the remaining portion of this iterator as a mutable str
    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.buf.as_mut_slice()) }
    }

    fn iter(&self) -> Chars<'_> {
        self.as_str().chars()
    }
}

impl<const N: usize> Iterator for TinyStringChars<N> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        let c = self.iter().next()?;
        for _ in 0..c.len_utf8() {
            self.buf.next();
        }
        Some(c)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter().size_hint()
    }
}

impl<const N: usize> DoubleEndedIterator for TinyStringChars<N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let c = self.iter().next_back()?;
        for _ in 0..c.len_utf8() {
            self.buf.next_back();
        }
        Some(c)
    }
}

impl<const N: usize> FusedIterator for TinyStringChars<N> {}

/// Iterator over the bytes of a [TinyString]
///
/// This struct is built from the [TinyString::into_bytes] function
pub struct TinyStringBytes<const N: usize>(tiny_vec::iter::TinyVecIter<u8, N>);

impl<const N: usize> Iterator for TinyStringBytes<N> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<const N: usize> DoubleEndedIterator for TinyStringBytes<N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

impl<const N: usize> FusedIterator for TinyStringBytes<N> {}
impl<const N: usize> ExactSizeIterator for TinyStringBytes<N> {}

impl<const N: usize> TinyString<N> {
    /// Converts this [TinyString] into an iterator over it's chars
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let v = TinyString::<10>::from("Hello :)");
    ///
    /// let chars = ['H', 'e', 'l', 'l', 'o', ' ', ':', ')'];
    /// let collected: Vec<char> = v.into_chars().collect();
    ///
    /// assert_eq!(&chars[..], &collected[..]);
    /// ```
    pub fn into_chars(self) -> TinyStringChars<N> {
        TinyStringChars {
            buf: self.0.into_iter()
        }
    }

    /// Converts this [TinyString] into an iterator over it's bytes
    ///
    /// # Example
    /// ```
    /// use tiny_str::TinyString;
    ///
    /// let v = TinyString::<10>::from("bytes");
    ///
    /// let bytes = [b'b', b'y', b't', b'e', b's'];
    /// let collected: Vec<u8> = v.into_bytes().collect();
    ///
    /// assert_eq!(&bytes[..], &collected[..]);
    /// ```
    pub fn into_bytes(self) -> TinyStringBytes<N> {
        TinyStringBytes(self.0.into_iter())
    }
}

impl<const N: usize> IntoIterator for  TinyString<N> {
    type Item = char;

    type IntoIter = TinyStringChars<N>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_chars()
    }
}
