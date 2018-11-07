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

use core::ops;

use as_slice::{AsMutSlice, AsSlice};

mod sealed;

/// 2-byte alignment
#[repr(align(2))]
pub struct A2;

/// 4-byte alignment
#[repr(align(4))]
pub struct A4;

/// 8-byte alignment
#[repr(align(8))]
pub struct A8;

/// 16-byte alignment
#[repr(align(16))]
pub struct A16;

/// A newtype with alignment of at least `A` bytes
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

    fn deref(&self) -> &T {
        &self.value
    }
}

impl<A, T> ops::DerefMut for Aligned<A, T>
where
    A: sealed::Alignment,
    T: ?Sized,
{
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<A, T> AsSlice for Aligned<A, T>
where
    A: sealed::Alignment,
    T: AsSlice,
{
    type Element = T::Element;

    fn as_slice(&self) -> &[T::Element] {
        T::as_slice(&**self)
    }
}

impl<A, T> AsMutSlice for Aligned<A, T>
where
    A: sealed::Alignment,
    T: AsMutSlice,
{
    fn as_mut_slice(&mut self) -> &mut [T::Element] {
        T::as_mut_slice(&mut **self)
    }
}

#[test]
fn sanity() {
    use core::mem;

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

    // alignment should be preserved after boxing
    let x: Box<Aligned<A2, [u8]>> = Box::new(Aligned([0u8; 3]));
    let y: Box<Aligned<A4, [u8]>> = Box::new(Aligned([0u8; 3]));
    let z: Box<Aligned<A8, [u8]>> = Box::new(Aligned([0u8; 3]));
    let w: Box<Aligned<A16, [u8]>> = Box::new(Aligned([0u8; 3]));

    assert_eq!(mem::align_of_val(&*x), 2);
    assert_eq!(mem::align_of_val(&*y), 4);
    assert_eq!(mem::align_of_val(&*z), 8);
    assert_eq!(mem::align_of_val(&*w), 16);

    // test deref-ing
    let x: Aligned<A2, _> = Aligned([0u8; 3]);
    let y: &Aligned<A2, [u8]> = &x;
    let _: &[u8] = y;
}
