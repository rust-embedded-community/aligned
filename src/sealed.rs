use generic_array::typenum::{PowerOfTwo, Unsigned, U16, U2, U32, U4, U64, U8};

pub trait Alignment {
    type Num: Unsigned + PowerOfTwo;
}

impl Alignment for super::A2 {
    type Num = U2;
}
impl Alignment for super::A4 {
    type Num = U4;
}
impl Alignment for super::A8 {
    type Num = U8;
}
impl Alignment for super::A16 {
    type Num = U16;
}
impl Alignment for super::A32 {
    type Num = U32;
}
impl Alignment for super::A64 {
    type Num = U64;
}
