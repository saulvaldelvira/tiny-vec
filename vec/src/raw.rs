#[cfg(feature = "alloc")]
extern crate alloc as _alloc;
#[cfg(feature = "alloc")]
use _alloc::alloc::{self,Layout};

use core::mem;
use core::ptr::NonNull;

pub struct RawVec<T> {
    pub ptr: NonNull<T>,
    pub cap: usize,
}

/// Returns the next capacity value
#[inline(always)]
#[cfg(feature = "alloc")]
const fn next_cap(cap: usize) -> usize {
    if cap == 0 { 1 } else { cap * 2 }
}

impl<T: Sized> RawVec<T> {
    pub fn new() -> Self {
        let cap = if mem::size_of::<T>() == 0 { isize::MAX } else { 0 };
        Self {
            ptr: NonNull::dangling(),
            cap: cap as usize,
        }
    }
}

/// Represents an error when trying to allocate memory
#[derive(Debug,Clone,Copy,PartialEq)]
pub enum ResizeError {
    #[cfg(feature = "alloc")]
    AllocationError(Layout),
    #[cfg(not(feature = "alloc"))]
    AllocNotSupported,
    CapacityOverflow,
    AllocationExceedsMaximun,
}

impl ResizeError {
    pub (crate) fn handle(&self) -> ! {
        #[cfg(feature = "alloc")]
        if let Self::AllocationError(layout) = self {
            alloc::handle_alloc_error(*layout)
        }
        #[cfg(not(feature = "alloc"))]
        if let Self::AllocNotSupported = self {
            panic!("Alloc is not enabled. Can't switch the buffer to the heap")
        }
        panic!("Fatal error: {self:?}");
    }
}

#[cfg(feature = "alloc")]
impl<T: Sized> RawVec<T> {
    pub fn with_capacity(cap: usize) -> Self {
        let mut vec = Self::new();
        if mem::size_of::<T>() != 0 {
            vec.resize_buffer(cap).unwrap_or_else(|err| err.handle());
        }
        vec
    }
    fn resize_buffer(&mut self, new_cap: usize) -> Result<(), ResizeError> {
        // since we set the capacity to usize::MAX when T has size 0,
        // getting to here necessarily means the Vec is overfull.
        if mem::size_of::<T>() == 0 {
            return Err(ResizeError::CapacityOverflow)
        }

        let Ok(new_layout) = Layout::array::<T>(new_cap) else {
            return Err(ResizeError::AllocationExceedsMaximun);
        };
        if new_layout.size() > isize::MAX as usize {
            return Err(ResizeError::AllocationExceedsMaximun);
        }

        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            let ptr = self.ptr.as_ptr() as *mut u8;
            unsafe { alloc::realloc(ptr, old_layout, new_layout.size()) }
        };
        if new_ptr.is_null() {
            return Err(ResizeError::AllocationError(new_layout))
        }

        self.cap = new_cap;
        self.ptr = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };

        Ok(())
    }
    pub fn try_expand_if_needed(&mut self, len: usize, n: usize) -> Result<(), ResizeError> {
        if len == self.cap {
            let mut new_cap = self.cap;
            while new_cap - len < n {
                new_cap = next_cap(new_cap);
            }
            self.resize_buffer(new_cap)?;
        }
        Ok(())
    }
    #[inline]
    pub fn try_expand_if_needed_exact(&mut self, len: usize, n: usize) -> Result<(), ResizeError> {
        if len == self.cap {
            self.resize_buffer(n)?;
        }
        Ok(())
    }

    pub fn shrink_to_fit(&mut self, len: usize) {
        self.resize_buffer(len).unwrap_or_else(|err| err.handle());
    }
    pub unsafe fn destroy(&mut self) {
        if self.cap != 0 && mem::size_of::<T>() != 0 {
            let layout = Layout::array::<T>(self.cap).unwrap();
            unsafe {
                let ptr = self.ptr.as_ptr() as *mut u8;
                alloc::dealloc(ptr, layout);
            }
        }
    }
}

#[cfg(not(feature = "alloc"))]
#[allow(unused)]
impl<T: Sized> RawVec<T> {
    pub fn with_capacity(cap: usize) -> Self {
        panic!("Alloc is not enabled. Can't switch the buffer to the heap")
    }
    fn resize_buffer(&mut self, new_cap: usize) {
        panic!("Alloc is not enabled. Can't switch the buffer to the heap")
    }

    pub fn try_expand_if_needed(&mut self, len: usize, n: usize) -> Result<(), ResizeError> {
        Err(ResizeError::AllocNotSupported)
    }
    #[inline]
    pub fn try_expand_if_needed_exact(&mut self, len: usize, n: usize) -> Result<(), ResizeError> {
        Err(ResizeError::AllocNotSupported)
    }

    pub fn shrink_to_fit(&mut self, len: usize) {
        panic!("Alloc is not enabled. Can't switch the buffer to the heap")
    }
    pub unsafe fn destroy(&mut self) {
        panic!("Alloc is not enabled. Can't switch the buffer to the heap")
    }
}

impl<T: Sized> Clone for RawVec<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Sized> Copy for RawVec<T> { }

impl<T> Default for RawVec<T> {
    fn default() -> Self {
        Self::new()
    }
}
