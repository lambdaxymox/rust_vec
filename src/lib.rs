#![feature(ptr_internals)]
#![feature(allocator_api)]
#![feature(alloc_layout_extra)]
use std::alloc::{
    Allocator,
    Global,
    GlobalAlloc,
    Layout,
    handle_alloc_error,
};
use std::cmp::{
    Ord,
    Ordering,
};
use std::fmt;
use std::marker::{
    PhantomData,
};
use std::mem;
use std::ops::{
    Deref, 
    DerefMut,
    Index,
};
use std::ptr::{
    Unique, 
    NonNull,
    self,
};


struct RawVec<T> {
    ptr: Unique<T>,
    capacity: usize,
}

impl<T> RawVec<T> {
    fn new() -> Self {
        // !0 is usize::MAX. This branch should be stripped at compile time.
        let capacity = if mem::size_of::<T>() == 0 { !0 } else { 0 };

        // Unique::dangling() doubles as "unallocated" and "zero-sized allocation".
        RawVec { 
            ptr: Unique::dangling(), 
            capacity
        }
    }

    fn grow(&mut self) {
        unsafe {
            let elem_size = mem::size_of::<T>();

            // Since we set the capacity to usize::MAX when elem_size is
            // 0, getting to here necessarily means the Vec is overfilled.
            assert!(elem_size != 0, "capacity overflow");

            let (new_capacity, ptr) = if self.capacity == 0 {
                let ptr = Global.allocate(Layout::array::<T>(1).unwrap());
                
                (1, ptr)
            } else {
                let new_capacity = 2 * self.capacity;
                let c: NonNull<T> = self.ptr.into();
                let ptr = Global.grow(
                    c.cast(),
                    Layout::array::<T>(self.capacity).unwrap(),
                    Layout::array::<T>(new_capacity).unwrap()
                );

                (new_capacity, ptr)
            };

            // If allocate or reallocate fail, oom
            if ptr.is_err() {
                handle_alloc_error(Layout::from_size_align_unchecked(
                    new_capacity * elem_size,
                    mem::align_of::<T>(),
                ))
            }
            let ptr = ptr.unwrap();

            self.ptr = Unique::new_unchecked(ptr.as_ptr() as *mut _);
            self.capacity = new_capacity;
        }
    }

    #[inline]
    fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr() as *const T
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.capacity
    }
}

impl<T> Drop for RawVec<T> {
    fn drop(&mut self) {
        let elem_size = mem::size_of::<T>();
        if self.capacity != 0 && elem_size != 0 {
            unsafe {
                let c: NonNull<T> = self.ptr.into();
                Global.deallocate(
                    c.cast(),
                    Layout::array::<T>(self.capacity).unwrap()
                );
            }
        }
    }
}

pub struct Vec<T> {
    buf: RawVec<T>,
    len: usize,
}

impl<T> Vec<T> {
    pub fn new() -> Vec<T> {
        Vec { 
            buf: RawVec::new(), 
            len: 0 
        }
    }

    pub fn as_mut_ptr(&mut self) -> *mut T { 
        self.buf.as_mut_ptr() 
    }

    pub fn as_ptr(&self) -> *const T {
        self.buf.as_ptr()
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    #[inline]
    pub fn capacity(&self) -> usize { 
        self.buf.capacity()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn push(&mut self, elem: T) {
        if self.len == self.capacity() { 
            self.buf.grow(); 
        }

        unsafe {
            ptr::write(self.as_mut_ptr().offset(self.len as isize), elem);
        }

        // This cannot fail, we'll trigger OOM first.
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe {
                Some(ptr::read(self.as_mut_ptr().offset(self.len as isize)))
            }
        }
    }
 
    pub fn insert(&mut self, index: usize, elem: T) {
        assert!(index <= self.len, "index out of bounds");
        if self.capacity() == self.len { 
            self.buf.grow(); 
        }

        unsafe {
            if index < self.len {
                ptr::copy(
                    self.as_mut_ptr().offset(index as isize),      
                    self.as_mut_ptr().offset(index as isize + 1),
                    self.len - index
                );
            }
            ptr::write(self.as_mut_ptr().offset(index as isize), elem);
            self.len += 1;
        }
    }

    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");
        unsafe {
            self.len -= 1;
            let result = ptr::read(self.as_mut_ptr().offset(index as isize));
            ptr::copy(
                self.as_mut_ptr().offset(index as isize + 1),
                self.as_mut_ptr().offset(index as isize),
                self.len - index
            );

            result
        }
    }

    pub fn truncate(&mut self, len: usize) {
        unsafe {
            while len < self.len {
                self.len -= 1;
                let len = self.len;
                ptr::drop_in_place(self.get_unchecked_mut(len));
            }
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0)
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    pub fn drain(&mut self) -> Drain<T> {
        unsafe {
            let iter = RawValIter::new(&self);

            // This is a mem::forget safety thing. If Drain is forgotten, we just
            // leak the whole Vec's contents. Also we need to do this *eventually*
            // anyway, so why not do it now?
            self.len = 0;

            Drain {
                iter: iter,
                vec: PhantomData,
            }
        }
    }
}

impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        // Deallocation is handled by RawVec.
        while let Some(_) = self.pop() {}
    }
}

impl<T> Deref for Vec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(self.as_ptr(), self.len)
        }
    }
}

impl<T> DerefMut for Vec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len)
        }
    }
}

impl<T> AsRef<[T]> for Vec<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsRef<Vec<T>> for Vec<T> {
    fn as_ref(&self) -> &Vec<T> {
        self
    }
}

impl<T> AsMut<[T]> for Vec<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T> AsMut<Vec<T>> for Vec<T> {
    fn as_mut(&mut self) -> &mut Vec<T> {
        self
    }
}

impl<T: fmt::Debug> fmt::Debug for Vec<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, formatter)
    }
}

impl<T: Clone> Clone for Vec<T> {
    fn clone(&self) -> Vec<T> {
        let mut vec = Vec::new();
        for item in self.iter() {
            vec.push(item.clone());
        }

        vec
    }
}

impl<T> Default for Vec<T> {
    fn default() -> Vec<T> {
        Vec::new()
    }
}

impl<T> Index<usize> for Vec<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        // Built-in indexing via the slice `&[T]`
        &(**self)[index]
    }
}

impl<A, B> PartialEq<Vec<A>> for Vec<B> where A: PartialEq<B> {
    #[inline]
    fn eq(&self, other: &Vec<A>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        if self.is_empty() {
            // At this point we know that both vectors have the same length, so
            // if one of them is empty, we know that the other one is empty.
            return true;
        }

        for i in 0..self.len() {
            if other[i] != self[i] {
                return false;
            } 
        }

        true
    }
}

impl<T: Eq> Eq for Vec<T> {}

impl<T: PartialOrd> PartialOrd for Vec<T> {
    #[inline]
    fn partial_cmp(&self, other: &Vec<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: Ord> Ord for Vec<T> {
    #[inline]
    fn cmp(&self, other: &Vec<T>) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

pub struct Iter<'a, T>{
    ptr: NonNull<T>,
    end: *const T,
    _marker: PhantomData<&'a T>,
}

unsafe impl<T: Sync> Sync for Iter<'_, T> {}
unsafe impl<T: Sync> Send for Iter<'_, T> {}

impl<'a, T> Iter<'a, T> {
    #[inline]
    fn new(slice: &'a [T]) -> Self {
        let ptr = slice.as_ptr();
        unsafe {
            assert!(!ptr.is_null());
            let end = if mem::size_of::<T>() == 0 {
                (ptr as *const u8).wrapping_add(slice.len()) as *const T
            } else {
                ptr.add(slice.len())
            };

            Self { 
                ptr: NonNull::new_unchecked(ptr as *mut T), 
                end,
                _marker: PhantomData, 
            }
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let ptr = self.ptr.as_ptr();
            if (ptr as *const T) < self.end {
                let new_ptr = if mem::size_of::<T>() == 0 {
                    (ptr as *const u8).wrapping_add(1) as *mut T
                } else {
                    ptr.add(1)
                };
                self.ptr = NonNull::new_unchecked(new_ptr);

                Some(&*(ptr as *const T))
            } else {
                None
            }
        }
    } 
}

struct RawValIter<T> {
    start: *const T,
    end: *const T,
}

impl<T> RawValIter<T> {
    unsafe fn new(slice: &[T]) -> Self {
        RawValIter {
            start: slice.as_ptr(),
            end: if mem::size_of::<T>() == 0 {
                ((slice.as_ptr() as usize) + slice.len()) as *const _
            } else if slice.len() == 0 {
                slice.as_ptr()
            } else {
                slice.as_ptr().offset(slice.len() as isize)
            },
        }
    }
}

impl<T> Iterator for RawValIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                let result = ptr::read(self.start);
                self.start = if mem::size_of::<T>() == 0 {
                    (self.start as usize + 1) as *const _
                } else {
                    self.start.offset(1)
                };

                Some(result)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let elem_size = mem::size_of::<T>();
        let len = (self.end as usize - self.start as usize)
                  / if elem_size == 0 { 1 } else { elem_size };

        (len, Some(len))
    }
}

impl<T> DoubleEndedIterator for RawValIter<T> {
    fn next_back(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                self.end = if mem::size_of::<T>() == 0 {
                    (self.end as usize - 1) as *const _
                } else {
                    self.end.offset(-1)
                };
                Some(ptr::read(self.end))
            }
        }
    }
}

pub struct IntoIter<T> {
    // we don't actually care about this. We just need it to live.
    _buf: RawVec<T>,
    iter: RawValIter<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> { 
        self.iter.next() 
    }

    fn size_hint(&self) -> (usize, Option<usize>) { 
        self.iter.size_hint() 
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> { 
        self.iter.next_back() 
    }
}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        for _ in &mut *self {}
    }
}

impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        unsafe {
            let iter = RawValIter::new(&self);
            let buf = ptr::read(&self.buf);
            mem::forget(self);
    
            IntoIter {
                _buf: buf,
                iter: iter,
            }
        }
    }
}


pub struct Drain<'a, T: 'a> {
    vec: PhantomData<&'a mut Vec<T>>,
    iter: RawValIter<T>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    fn next_back(&mut self) -> Option<T> { self.iter.next_back() }
}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        // Pre-drain the iterator.
        for _ in &mut *self {}
    }
}


#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    fn test_create_push_pop() {
        let mut v = Vec::new();
        v.push(1);

        assert_eq!(1, v.len());
        assert_eq!(1, v[0]);

        for i in v.iter_mut() {
            *i += 1;
        }
        v.insert(0, 5);
        let x = v.pop();

        assert_eq!(Some(2), x);
        assert_eq!(1, v.len());

        v.push(10);
        let x = v.remove(0);

        assert_eq!(5, x);
        assert_eq!(1, v.len());
    }

    #[test]
    fn test_pushing_multiple_elements_and_popping_all_of_them_should_empty_vec() {
        let mut vec = Vec::new();
        let length = 100;
        for elem in 0..length {
            vec.push(elem);
        }

        assert!(!vec.is_empty());

        for _ in 0..length {
            vec.pop();
        }

        assert!(vec.is_empty());
    }

    #[test]
    fn test_into_iter() {
        let mut v = Vec::new();
        for i in 0..10 {
            v.push(Box::new(i))
        }

        let mut iter = v.into_iter();
        let first = iter.next().unwrap();
        let last = iter.next_back().unwrap();
        drop(iter);

        assert_eq!(0, *first);
        assert_eq!(9, *last);
    }

    #[test]
    fn test_len() {
        let mut v = Vec::new();
        let length = 100;
        for i in 0..length {
            v.push(i);
        }

        assert_eq!(v.len(), length);
    }

    #[test]
    fn test_is_empty_no_elements() {
        let vec: Vec<isize> = Vec::new();

        assert!(vec.is_empty());
    }

    #[test]
    fn test_iter() {
        let mut vec = Vec::new();
        let length = 10;
        for elem in 0..length {
            vec.push(elem);
        }

        let mut it = vec.iter();
        for expected in 0..length {
            let result = it.next();
            
            assert_eq!(result, Some(&expected));
        }
    }

    #[test]
    fn test_empty_iterator_should_always_return_none() {
        let vec: Vec<isize> = Vec::new();
        let mut it = vec.iter();
        for _ in 0..100 {
            let result = it.next();
            assert!(result.is_none());
        }
    }

    #[test]
    fn test_drain() {
        let mut v = Vec::new();
        for i in 0..10 {
            v.push(Box::new(i))
        }
        {
            let mut drain = v.drain();
            let first = drain.next().unwrap();
            let last = drain.next_back().unwrap();

            assert_eq!(0, *first);
            assert_eq!(9, *last);
        }

        assert_eq!(0, v.len());

        v.push(Box::new(1));

        assert_eq!(1, *v.pop().unwrap());
    }

    #[test]
    fn test_zero_sized_type_into_iter() {
        let mut vec = Vec::new();
        let length = 10;
        for _i in 0..length {
            vec.push(());
        }

        let mut count = 0;
        for _ in vec.into_iter() {
            count += 1;
        }

        assert_eq!(length, count);
    }

    #[test]
    fn test_zero_sized_type_iter() {
        let mut vec = Vec::new();
        let length = 10;
        for _i in 0..length {
            vec.push(());
        }

        let mut count = 0;
        for _ in vec.iter() {
            count += 1;
        }

        assert_eq!(length, count);
    }

    #[test]
    fn test_clone() {
        let mut vec = Vec::new();
        let length = 100;
        for elem in 0..length {
            vec.push(elem);
        }

        let cloned = vec.clone();

        assert_eq!(vec, cloned);
    }

    #[test]
    fn test_clear() {
        let mut vec = Vec::new();
        let length = 100;
        for elem in 0..length {
            vec.push(elem);
        }

        assert!(!vec.is_empty());

        vec.clear();

        assert!(vec.is_empty());
    }


}

