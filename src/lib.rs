//! Statically allocated arrays with guaranteed memory alignments
//!
//! # Examples
//!
//! ```
//! #![feature(const_fn)]
//!
//! use std::mem;
//!
//! use aligned::Aligned;
//!
//! // Array aligned to a 2 byte boundary
//! static X: Aligned<u16, [u8; 3]> = Aligned([0; 3]);
//!
//! // Array aligned to a 4 byte boundary
//! static Y: Aligned<u32, [u8; 3]> = Aligned([0; 3]);
//!
//! // Unaligned array
//! static Z: [u8; 3] = [0; 3];
//!
//! // You can allocate the aligned arrays on the stack too
//! let w: Aligned<u64, _> = Aligned([0u8; 3]);
//!
//! assert_eq!(mem::align_of_val(&X), 2);
//! assert_eq!(mem::align_of_val(&Y), 4);
//! assert_eq!(mem::align_of_val(&Z), 1);
//! assert_eq!(mem::align_of_val(&w), 8);
//! ```

#![deny(missing_docs)]
#![deny(warnings)]
#![feature(const_fn)]
#![no_std]

use core::ops;

/// An `ARRAY` aligned to `mem::align_of::<ALIGNMENT>`
pub struct Aligned<ALIGNMENT, ARRAY> {
    _alignment: [ALIGNMENT; 0],
    array: ARRAY,
}

impl<ALIGNMENT, ARRAY> ops::Deref for Aligned<ALIGNMENT, ARRAY> {
    type Target = ARRAY;

    fn deref(&self) -> &ARRAY {
        &self.array
    }
}

impl<ALIGNMENT, ARRAY> ops::DerefMut for Aligned<ALIGNMENT, ARRAY> {
    fn deref_mut(&mut self) -> &mut ARRAY {
        &mut self.array
    }
}

/// IMPLEMENTATION DETAIL
pub unsafe trait Alignment {}

/// 16 bit alignment
unsafe impl Alignment for u16 {}

/// 32 bit alignment
unsafe impl Alignment for u32 {}

/// 64 bit alignment
unsafe impl Alignment for u64 {}

/// `Aligned` constructor
#[allow(non_snake_case)]
pub const fn Aligned<ALIGNMENT, ARRAY>(
    array: ARRAY,
) -> Aligned<ALIGNMENT, ARRAY>
where
    ALIGNMENT: Alignment,
{
    Aligned {
        _alignment: [],
        array: array,
    }
}

#[test]
fn sanity() {
    use core::mem;

    let x: Aligned<u16, _> = Aligned([0u8; 3]);
    let y: Aligned<u32, _> = Aligned([0u8; 3]);
    let z: Aligned<u64, _> = Aligned([0u8; 3]);

    assert_eq!(mem::align_of_val(&x), 2);
    assert_eq!(mem::align_of_val(&y), 4);
    assert_eq!(mem::align_of_val(&z), 8);

    assert!(x.as_ptr() as usize % 2 == 0);
    assert!(y.as_ptr() as usize % 4 == 0);
    assert!(z.as_ptr() as usize % 8 == 0);
}
