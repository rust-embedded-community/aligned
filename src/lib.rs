//! A newtype with alignment of at least `A` bytes
//!
//! # Examples
//!
//! ```
//! use std::mem;
//!
//! use aligned::{Aligned, A2, A4, A16};
//!
//! // Array aligned to a 2 byte boundary
//! static X: Aligned<A2, [u8; 3]> = Aligned([0; 3]);
//!
//! // Array aligned to a 4 byte boundary
//! static Y: Aligned<A4, [u8; 3]> = Aligned([0; 3]);
//!
//! // Unaligned array
//! static Z: [u8; 3] = [0; 3];
//!
//! // You can allocate the aligned arrays on the stack too
//! let w: Aligned<A16, _> = Aligned([0u8; 3]);
//!
//! assert_eq!(mem::align_of_val(&X), 2);
//! assert_eq!(mem::align_of_val(&Y), 4);
//! assert_eq!(mem::align_of_val(&Z), 1);
//! assert_eq!(mem::align_of_val(&w), 16);
//! ```

#![deny(missing_docs)]
#![deny(warnings)]
#![cfg_attr(not(test), no_std)]

use core::{
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    iter::{FromIterator, IntoIterator},
    ops,
};

use as_slice::{AsMutSlice, AsSlice};
use generic_array::{typenum, ArrayLength, GenericArray};
use typenum::{Diff, IsGreaterOrEqual, IsLessOrEqual, PartialDiv, Unsigned, B1, U8};

mod sealed;

/// 2-byte alignment
#[repr(C, align(2))]
pub struct A2;

/// 4-byte alignment
#[repr(C, align(4))]
pub struct A4;

/// 8-byte alignment
#[repr(C, align(8))]
pub struct A8;

/// 16-byte alignment
#[repr(C, align(16))]
pub struct A16;

/// 32-byte alignment
#[repr(C, align(32))]
pub struct A32;

/// 64-byte alignment
#[repr(C, align(64))]
pub struct A64;

/// A newtype with alignment of at least `A` bytes
#[repr(C)]
pub struct Aligned<A, T>
where
    T: ?Sized,
{
    _alignment: [A; 0],
    value: T,
}

/// Changes the alignment of `value` to be at least `A` bytes
#[allow(non_snake_case)]
pub const fn Aligned<A, T>(value: T) -> Aligned<A, T> {
    Aligned {
        _alignment: [],
        value,
    }
}

impl<A, T> ops::Deref for Aligned<A, T>
where
    A: sealed::Alignment,
    T: ?Sized,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.value
    }
}

impl<A, T> ops::DerefMut for Aligned<A, T>
where
    A: sealed::Alignment,
    T: ?Sized,
{
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<A, T> ops::Index<ops::RangeTo<usize>> for Aligned<A, [T]>
where
    A: sealed::Alignment,
{
    type Output = Aligned<A, [T]>;

    fn index(&self, range: ops::RangeTo<usize>) -> &Aligned<A, [T]> {
        unsafe { &*(&self.value[range] as *const [T] as *const Aligned<A, [T]>) }
    }
}

impl<A, T> AsSlice for Aligned<A, T>
where
    A: sealed::Alignment,
    T: AsSlice,
{
    type Element = T::Element;

    #[inline]
    fn as_slice(&self) -> &[T::Element] {
        T::as_slice(&**self)
    }
}

impl<A, T> AsMutSlice for Aligned<A, T>
where
    A: sealed::Alignment,
    T: AsMutSlice,
{
    #[inline]
    fn as_mut_slice(&mut self) -> &mut [T::Element] {
        T::as_mut_slice(&mut **self)
    }
}

impl<A, T> Clone for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            _alignment: [],
            value: self.value.clone(),
        }
    }
}

impl<A, T> Default for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Default,
{
    #[inline]
    fn default() -> Self {
        Self {
            _alignment: [],
            value: Default::default(),
        }
    }
}

impl<A, T> Debug for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Debug,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<A, T> Display for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Display,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.value.fmt(f)
    }
}

impl<A, T> PartialEq for Aligned<A, T>
where
    A: sealed::Alignment,
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<A, T> Eq for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Eq,
{
}

impl<A, T> Hash for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<A, T> Ord for Aligned<A, T>
where
    A: sealed::Alignment,
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.value.cmp(&other.value)
    }
}

impl<A, T> PartialOrd for Aligned<A, T>
where
    A: sealed::Alignment,
    T: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.value.partial_cmp(&other.value)
    }
}

impl<A, T, V> FromIterator<V> for Aligned<A, T>
where
    A: sealed::Alignment,
    T: FromIterator<V>,
{
    fn from_iter<U: IntoIterator<Item = V>>(iter: U) -> Self {
        Aligned(T::from_iter(iter))
    }
}

impl<A, T> IntoIterator for Aligned<A, T>
where
    A: sealed::Alignment,
    T: IntoIterator,
{
    type Item = T::Item;
    type IntoIter = T::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.value.into_iter()
    }
}

impl<'a, A, T> IntoIterator for &'a Aligned<A, T>
where
    A: sealed::Alignment,
    &'a T: IntoIterator,
{
    type Item = <&'a T as IntoIterator>::Item;
    type IntoIter = <&'a T as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.value.into_iter()
    }
}

impl<'a, A, T> IntoIterator for &'a mut Aligned<A, T>
where
    A: sealed::Alignment,
    &'a mut T: IntoIterator,
{
    type Item = <&'a mut T as IntoIterator>::Item;
    type IntoIter = <&'a mut T as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.value.into_iter()
    }
}

// Allow AsRef and AsMut for Aligned<A, T> when it is only making A smaller
impl<'a, A, A2, T> AsRef<Aligned<A, T>> for &'a Aligned<A2, T>
where
    A: sealed::Alignment,
    A2: sealed::Alignment,
    A::Num: IsLessOrEqual<A2::Num, Output = B1>,
{
    #[inline]
    fn as_ref(&self) -> &Aligned<A, T> {
        assert_aligned(*self)
    }
}

// Allow AsRef and AsMut for Aligned<A, T> when it is only making A smaller
impl<'a, A, A2, T> AsMut<Aligned<A, T>> for &'a mut Aligned<A2, T>
where
    A: sealed::Alignment,
    A2: sealed::Alignment,
    A::Num: IsLessOrEqual<A2::Num, Output = B1>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut Aligned<A, T> {
        assert_aligned_mut(*self)
    }
}

/// Implement generic_array::GenericSequence for Aligned sequences
unsafe impl<A, T, N> generic_array::sequence::GenericSequence<T> for Aligned<A, GenericArray<T, N>>
where
    N: ArrayLength<T>,
    A: sealed::Alignment,
{
    type Length = N;
    type Sequence = Self;

    #[inline]
    fn generate<F>(f: F) -> Self::Sequence
    where
        F: FnMut(usize) -> T,
    {
        Aligned(GenericArray::generate(f))
    }
}

/// Implement generic_array::Split api for aligned bytes in a way that preserves aligment info
/// TODO: This could be more generic, but we didn't need it yet.
/// Instead of u8, a generic value T?
unsafe impl<'a, A, N, K> generic_array::sequence::Split<u8, K>
    for &'a Aligned<A, GenericArray<u8, N>>
where
    A: sealed::Alignment,
    N: ArrayLength<u8> + ops::Sub<K>,
    K: ArrayLength<u8> + PartialDiv<A::Num> + 'static,
    Diff<N, K>: ArrayLength<u8>,
{
    type First = &'a Aligned<A, GenericArray<u8, K>>;
    type Second = &'a Aligned<A, GenericArray<u8, Diff<N, K>>>;
    #[inline]
    fn split(self) -> (Self::First, Self::Second) {
        // Correctness notes:
        // If self is aligned to A-byte boundary, and K is a multiple of A,
        // then `first`, the first K items of the array, is also aligned,
        // since its address is &self,
        // and `second`, the remaining items, are also aligned, since their
        // address differs from &self by a multiple of A.
        // This is true even if A does not divide N.
        let (first, second): (&GenericArray<u8, K>, &GenericArray<u8, Diff<N, K>>) =
            (&self.value).split();
        (assert_aligned(first), assert_aligned(second))
    }
}

/// Implement generic_array::Split API for aligned bytes in a way that preserves aligment info
/// TODO: This could be more generic, but we didn't need it yet.
/// Instead of u8, a generic value T?
unsafe impl<'a, A, N, K> generic_array::sequence::Split<u8, K>
    for &'a mut Aligned<A, GenericArray<u8, N>>
where
    A: sealed::Alignment,
    N: ArrayLength<u8> + ops::Sub<K>,
    K: ArrayLength<u8> + PartialDiv<A::Num> + 'static,
    Diff<N, K>: ArrayLength<u8>,
{
    type First = &'a mut Aligned<A, GenericArray<u8, K>>;
    type Second = &'a mut Aligned<A, GenericArray<u8, Diff<N, K>>>;
    #[inline]
    fn split(self) -> (Self::First, Self::Second) {
        // Correctness notes:
        // If self is aligned to A-byte boundary, and K is a multiple of A,
        // then `first`, the first K items of the array, is also aligned,
        // since its address is &self,
        // and `second`, the remaining items, are also aligned, since their
        // address differs from &self by a multiple of A.
        // This is true even if A does not divide N.
        let (first, second): (&mut GenericArray<u8, K>, &mut GenericArray<u8, Diff<N, K>>) =
            (&mut self.value).split();
        (assert_aligned_mut(first), assert_aligned_mut(second))
    }
}

// Internal helper: Given &T, cast to &Aligned<A, T>.
// In debug builds assert that the alignment claim is correct.
#[inline]
fn assert_aligned<A: sealed::Alignment, T>(t: &T) -> &Aligned<A, T> {
    unsafe {
        let ptr: *const T = t;
        debug_assert!(ptr.align_offset(A::Num::USIZE) == 0);
        &*(ptr as *const Aligned<A, T>)
    }
}

// Internal helper: Given &mut T, cast to &mut Aligned<A, T>.
// In debug builds assert that the alignment claim is correct.
#[inline]
fn assert_aligned_mut<A: sealed::Alignment, T>(t: &mut T) -> &mut Aligned<A, T> {
    unsafe {
        let ptr: *mut T = t;
        debug_assert!(ptr.align_offset(A::Num::USIZE) == 0);
        &mut *(ptr as *mut Aligned<A, T>)
    }
}

/// Trait for types which can be viewed as native-endian integer slices
/// This should generally just be, aligned slices of dumb bytes or similar.
/// (Indeed the only intended implementor is Aligned<A8, GenericArray<u8, N>>)
///
/// This should only be implemented when all the bytes in the underlying object
/// can be accessed this way. So, the number of bytes should be divisible by 8
/// and aligned to an 8 byte boundary.
///
/// TODO: This could be 3 traits instead, one for each integer type,
/// but we didn't need that yet.
pub trait AsNeSlice {
    /// Represent the value as native-endian u16's
    fn as_ne_u16_slice(&self) -> &[u16];
    /// Represent the value as mutable native-endian u16's
    fn as_mut_ne_u16_slice(&mut self) -> &mut [u16];
    /// Represent the value as native-endian u32's
    fn as_ne_u32_slice(&self) -> &[u32];
    /// Represent the value as mutable native-endian u32's
    fn as_mut_ne_u32_slice(&mut self) -> &mut [u32];
    /// Represent the value as native-endian u64's
    fn as_ne_u64_slice(&self) -> &[u64];
    /// Represent the value as mutable native-endian u64's
    fn as_mut_ne_u64_slice(&mut self) -> &mut [u64];
}

// Implement AsNeSlice for aligned bytes aligned at 8 bytes or larger
impl<A, N> AsNeSlice for Aligned<A, GenericArray<u8, N>>
where
    A: sealed::Alignment,
    A::Num: IsGreaterOrEqual<U8, Output = B1>,
    N: ArrayLength<u8> + PartialDiv<U8>,
{
    #[inline]
    fn as_ne_u16_slice(&self) -> &[u16] {
        let (l, result, r) = unsafe { self.as_slice().align_to::<u16>() };
        debug_assert!(l.is_empty());
        debug_assert!(r.is_empty());
        result
    }

    #[inline]
    fn as_mut_ne_u16_slice(&mut self) -> &mut [u16] {
        let (l, result, r) = unsafe { self.as_mut_slice().align_to_mut::<u16>() };
        debug_assert!(l.is_empty());
        debug_assert!(r.is_empty());
        result
    }

    #[inline]
    fn as_ne_u32_slice(&self) -> &[u32] {
        let (l, result, r) = unsafe { self.as_slice().align_to::<u32>() };
        debug_assert!(l.is_empty());
        debug_assert!(r.is_empty());
        result
    }

    #[inline]
    fn as_mut_ne_u32_slice(&mut self) -> &mut [u32] {
        let (l, result, r) = unsafe { self.as_mut_slice().align_to_mut::<u32>() };
        debug_assert!(l.is_empty());
        debug_assert!(r.is_empty());
        result
    }

    #[inline]
    fn as_ne_u64_slice(&self) -> &[u64] {
        let (l, result, r) = unsafe { self.as_slice().align_to::<u64>() };
        debug_assert!(l.is_empty());
        debug_assert!(r.is_empty());
        result
    }

    #[inline]
    fn as_mut_ne_u64_slice(&mut self) -> &mut [u64] {
        let (l, result, r) = unsafe { self.as_mut_slice().align_to_mut::<u64>() };
        debug_assert!(l.is_empty());
        debug_assert!(r.is_empty());
        result
    }
}

/// Implement ct_eq for Aligned bytes implementing AsNeSlice
///
/// Typically to invoke ct_eq on `Aligned<T>` you can `*` it to remove the aligned
/// wrapper and then invoke `ct_eq`, there is no special implementation.
///
/// In some cases, like aligned bytes, CtEq can be made faster by operating on 8
/// bytes at once, and it's nice to take advantage of that.
///
/// Ideally this kind of code would live in `subtle` crate and not this crate eventually
#[cfg(feature = "subtle")]
impl<A, N> subtle::ConstantTimeEq for Aligned<A, GenericArray<u8, N>>
where
    A: sealed::Alignment,
    A::Num: IsGreaterOrEqual<U8, Output = B1>,
    N: ArrayLength<u8> + PartialDiv<U8>,
{
    #[inline]
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        self.as_ne_u64_slice().ct_eq(&other.as_ne_u64_slice())
    }
}

/// Trait for types which can be viewed as aligned chunks of bytes
/// This should generally just be, larger chunks of dumb bytes or similar.
pub trait AsAlignedChunks<A: sealed::Alignment, M: ArrayLength<u8> + PartialDiv<A::Num>> {
    /// Break self into aligned chunks of size M.
    /// This is not required to cover all the bytes of Self,
    /// trailing bytes that don't fit may be left off.
    fn as_aligned_chunks(&self) -> &[Aligned<A, GenericArray<u8, M>>];
    /// Break self into mutable aligned chunks of size M.
    /// This is not required to cover all the bytes of Self, but must agree with
    /// as_aligned_chunks.
    fn as_mut_aligned_chunks(&mut self) -> &mut [Aligned<A, GenericArray<u8, M>>];
}

// Implement AsAlignedChunks for Aligned GenericArray<u8, N>
//
// Note: If M does not divide N, then some of the bytes of Self won't be part
// of any of the chunks. But this doesn't pose a problem for implementation,
// and is helpful to some of the use-cases.
impl<A, A2, N, M> AsAlignedChunks<A2, M> for Aligned<A, GenericArray<u8, N>>
where
    A: sealed::Alignment,
    A2: sealed::Alignment,
    A2::Num: IsLessOrEqual<A::Num, Output = B1>,
    N: ArrayLength<u8>,
    M: ArrayLength<u8> + PartialDiv<A2::Num>,
{
    #[inline]
    fn as_aligned_chunks(&self) -> &[Aligned<A2, GenericArray<u8, M>>] {
        unsafe {
            let ptr = self as *const Aligned<A, GenericArray<u8, N>>
                as *const Aligned<A2, GenericArray<u8, M>>;
            // Correctness notes:
            // - Alignment of ptr is A, which exceeds A2 as required
            // - A2 divides M, so Aligned<A2, GenericArray<u8, M>> has no padding, and has size M.
            // - Size of buffer is at least N, which exceeds (N / M) * M.
            core::slice::from_raw_parts(ptr, N::USIZE / M::USIZE)
        }
    }
    #[inline]
    fn as_mut_aligned_chunks(&mut self) -> &mut [Aligned<A2, GenericArray<u8, M>>] {
        unsafe {
            let ptr = self as *mut Aligned<A, GenericArray<u8, N>>
                as *mut Aligned<A2, GenericArray<u8, M>>;
            // Correctness notes:
            // - Alignment of ptr is A, which exceeds A2 as required
            // - A2 divides M, so Aligned<A2, GenericArray<u8, M>> has no padding, and has size M.
            // - Size of buffer is at least N, which exceeds (N / M) * M.
            core::slice::from_raw_parts_mut(ptr, N::USIZE / M::USIZE)
        }
    }
}

#[cfg(test)]
mod testing {
    use super::*;
    use generic_array::arr;

    use core::mem;
    use generic_array::{
        sequence::Split,
        typenum::{U128, U16, U192, U24, U32, U64, U8, U96},
    };

    // shorthand aliases to make it easier to write tests
    type A8Bytes<N> = Aligned<A8, GenericArray<u8, N>>;
    type A64Bytes<N> = Aligned<A64, GenericArray<u8, N>>;

    #[test]
    fn sanity() {
        let x: Aligned<A2, _> = Aligned([0u8; 3]);
        let y: Aligned<A4, _> = Aligned([0u8; 3]);
        let z: Aligned<A8, _> = Aligned([0u8; 3]);
        let w: Aligned<A16, _> = Aligned([0u8; 3]);

        // check alignment
        assert_eq!(mem::align_of_val(&x), 2);
        assert_eq!(mem::align_of_val(&y), 4);
        assert_eq!(mem::align_of_val(&z), 8);
        assert_eq!(mem::align_of_val(&w), 16);

        assert!(x.as_ptr() as usize % 2 == 0);
        assert!(y.as_ptr() as usize % 4 == 0);
        assert!(z.as_ptr() as usize % 8 == 0);
        assert!(w.as_ptr() as usize % 16 == 0);

        // test `deref`
        assert_eq!(x.len(), 3);
        assert_eq!(y.len(), 3);
        assert_eq!(z.len(), 3);
        assert_eq!(w.len(), 3);

        // alignment should be preserved after slicing
        let x: &Aligned<_, [_]> = &x;
        let y: &Aligned<_, [_]> = &y;
        let z: &Aligned<_, [_]> = &z;
        let w: &Aligned<_, [_]> = &w;

        let x: &Aligned<_, _> = &x[..2];
        let y: &Aligned<_, _> = &y[..2];
        let z: &Aligned<_, _> = &z[..2];
        let w: &Aligned<_, _> = &w[..2];

        assert!(x.as_ptr() as usize % 2 == 0);
        assert!(y.as_ptr() as usize % 4 == 0);
        assert!(z.as_ptr() as usize % 8 == 0);
        assert!(w.as_ptr() as usize % 16 == 0);

        // alignment should be preserved after boxing
        let x: Box<Aligned<A2, [u8]>> = Box::new(Aligned([0u8; 3]));
        let y: Box<Aligned<A4, [u8]>> = Box::new(Aligned([0u8; 3]));
        let z: Box<Aligned<A8, [u8]>> = Box::new(Aligned([0u8; 3]));
        let w: Box<Aligned<A16, [u8]>> = Box::new(Aligned([0u8; 3]));

        assert_eq!(mem::align_of_val(&*x), 2);
        assert_eq!(mem::align_of_val(&*y), 4);
        assert_eq!(mem::align_of_val(&*z), 8);
        assert_eq!(mem::align_of_val(&*w), 16);

        // test coercions
        let x: Aligned<A2, _> = Aligned([0u8; 3]);
        let y: &Aligned<A2, [u8]> = &x;
        let _: &[u8] = y;
    }

    #[test]
    fn aligned_split() {
        let x: A8Bytes<U24> = Aligned(
            arr![u8; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
        );

        let (y, z) = <&A8Bytes<U24> as Split<u8, U8>>::split(&x);
        assert_eq!(y, &Aligned(arr![u8; 0, 1, 2, 3, 4, 5, 6, 7]));
        assert_eq!(
            z,
            &Aligned(arr![u8; 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23])
        );

        let (v, w) = <&A8Bytes<U24> as Split<u8, U16>>::split(&x);
        assert_eq!(
            v,
            &Aligned(arr![u8; 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])
        );
        assert_eq!(w, &Aligned(arr![u8; 16, 17, 18, 19, 20, 21, 22, 23]));
    }

    #[test]
    fn aligned_split_64() {
        let mut x = A64Bytes::<U192>::default();
        for (idx, byte) in x.iter_mut().enumerate() {
            *byte = idx as u8;
        }

        let (y, z) = <&A64Bytes<U192> as Split<u8, U64>>::split(&x);
        for (idx, byte) in y.iter().enumerate() {
            assert_eq!(*byte, idx as u8);
        }
        for (idx, byte) in z.iter().enumerate() {
            assert_eq!(*byte, 64 + idx as u8);
        }

        let (v, w) = <&A64Bytes<U192> as Split<u8, U128>>::split(&x);
        for (idx, byte) in v.iter().enumerate() {
            assert_eq!(*byte, idx as u8);
        }
        for (idx, byte) in w.iter().enumerate() {
            assert_eq!(*byte, 128 + idx as u8);
        }
    }

    #[test]
    fn test_aligned_chunks() {
        let buff = A8Bytes::<U32>::default();
        let chunks = AsAlignedChunks::<A8, U16>::as_aligned_chunks(&buff);
        assert_eq!(chunks.len(), 2);

        let buff = A8Bytes::<U64>::default();
        let chunks = AsAlignedChunks::<A8, U16>::as_aligned_chunks(&buff);
        assert_eq!(chunks.len(), 4);

        let buff = A8Bytes::<U96>::default();
        let chunks = AsAlignedChunks::<A8, U8>::as_aligned_chunks(&buff);
        assert_eq!(chunks.len(), 12);
    }

    #[test]
    fn test_aligned_chunks_64() {
        let buff = A64Bytes::<U128>::default();
        let chunks = AsAlignedChunks::<A64, U64>::as_aligned_chunks(&buff);
        assert_eq!(chunks.len(), 2);

        let buff = A64Bytes::<U64>::default();
        let chunks = AsAlignedChunks::<A8, U8>::as_aligned_chunks(&buff);
        assert_eq!(chunks.len(), 8);

        let buff = A64Bytes::<U96>::default();
        let chunks = AsAlignedChunks::<A32, U32>::as_aligned_chunks(&buff);
        assert_eq!(chunks.len(), 3);
    }

    // This test will only work on a little-endian machine
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn test_as_ne_slice() {
        let mut buff = A8Bytes::<U32>::default();
        {
            let u16s = buff.as_ne_u16_slice();
            assert_eq!(u16s.len(), 16);
            for num in u16s.iter() {
                assert_eq!(*num, 0u16);
            }
        }

        {
            let u32s = buff.as_ne_u32_slice();
            assert_eq!(u32s.len(), 8);
            for num in u32s.iter() {
                assert_eq!(*num, 0u32);
            }
        }

        {
            let u64s = buff.as_mut_ne_u64_slice();
            assert_eq!(u64s.len(), 4);
            for num in u64s.iter() {
                assert_eq!(*num, 0u64);
            }

            u64s[2] = !7;
        }

        {
            let u64s = buff.as_ne_u64_slice();
            assert_eq!(u64s.len(), 4);
            assert_eq!(u64s[0], 0u64);
            assert_eq!(u64s[1], 0u64);
            assert_eq!(u64s[2], !7u64);
            assert_eq!(u64s[3], 0u64);
        }

        {
            let u32s = buff.as_ne_u32_slice();
            assert_eq!(u32s.len(), 8);
            assert_eq!(u32s[0], 0u32);
            assert_eq!(u32s[1], 0u32);
            assert_eq!(u32s[2], 0u32);
            assert_eq!(u32s[3], 0u32);
            assert_eq!(u32s[4], !7u32);
            assert_eq!(u32s[5], !0u32);
            assert_eq!(u32s[6], 0u32);
            assert_eq!(u32s[7], 0u32);
        }

        {
            let u16s = buff.as_ne_u16_slice();
            assert_eq!(u16s.len(), 16);
            assert_eq!(u16s[0], 0u16);
            assert_eq!(u16s[1], 0u16);
            assert_eq!(u16s[2], 0u16);
            assert_eq!(u16s[3], 0u16);
            assert_eq!(u16s[4], 0u16);
            assert_eq!(u16s[5], 0u16);
            assert_eq!(u16s[6], 0u16);
            assert_eq!(u16s[7], 0u16);
            assert_eq!(u16s[8], !7u16);
            assert_eq!(u16s[9], !0u16);
            assert_eq!(u16s[10], !0u16);
            assert_eq!(u16s[11], !0u16);
            assert_eq!(u16s[12], 0u16);
            assert_eq!(u16s[13], 0u16);
            assert_eq!(u16s[14], 0u16);
            assert_eq!(u16s[15], 0u16);
        }

        {
            let u16s = buff.as_mut_ne_u16_slice();
            u16s[2] = !5u16;
        }

        {
            let u32s = buff.as_ne_u32_slice();
            assert_eq!(u32s.len(), 8);
            assert_eq!(u32s[0], 0u32);
            assert_eq!(u32s[1], !5u16 as u32);
            assert_eq!(u32s[2], 0u32);
            assert_eq!(u32s[3], 0u32);
            assert_eq!(u32s[4], !7u32);
            assert_eq!(u32s[5], !0u32);
            assert_eq!(u32s[6], 0u32);
            assert_eq!(u32s[7], 0u32);
        }

        {
            let u64s = buff.as_ne_u64_slice();
            assert_eq!(u64s.len(), 4);
            assert_eq!(u64s[0], (!5u16 as u64) << 32);
            assert_eq!(u64s[1], 0u64);
            assert_eq!(u64s[2], !7u64);
            assert_eq!(u64s[3], 0u64);
        }
    }
}
