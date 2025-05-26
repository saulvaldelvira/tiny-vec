extern crate alloc as _alloc;
use _alloc::alloc::{self,Layout};

use core::mem;
use core::ptr::NonNull;

pub struct RawVec<T> {
    pub ptr: NonNull<T>,
    pub cap: usize,
}

/// Returns the next capacity value
#[inline(always)]
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
    pub fn with_capacity(cap: usize) -> Self {
        let mut vec = Self::new();
        if mem::size_of::<T>() != 0 {
            vec.resize_buffer(cap);
        }
        vec
    }
    fn resize_buffer(&mut self, new_cap: usize) {
        // since we set the capacity to usize::MAX when T has size 0,
        // getting to here necessarily means the Vec is overfull.
        assert!(mem::size_of::<T>() != 0, "capacity overflow");

        let new_layout = Layout::array::<T>(new_cap).unwrap();
        assert!(new_layout.size() <= isize::MAX as usize, "Allocation exceeds maximun");

        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            let ptr = self.ptr.as_ptr() as *mut u8;
            unsafe { alloc::realloc(ptr, old_layout, new_layout.size()) }
        };
        if new_ptr.is_null() {
            alloc::handle_alloc_error(new_layout);
        }

        self.cap = new_cap;
        self.ptr = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };
    }
    pub fn expand_if_needed(&mut self, len: usize, n: usize) {
        if len == self.cap {
            let mut new_cap = self.cap;
            while new_cap - len < n {
                new_cap = next_cap(new_cap);
            }
            self.resize_buffer(new_cap);
        }
    }
    #[inline]
    pub fn expand_if_needed_exact(&mut self, len: usize, n: usize) {
        if len == self.cap {
            self.resize_buffer(n);
        }
    }
    pub fn shrink_to_fit(&mut self, len: usize) {
        self.resize_buffer(len);
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
