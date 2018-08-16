// -*- mode: rust; -*-
//
// To the extent possible under law, the authors have waived all copyright and
// related or neighboring rights to subtle, using the Creative Commons "CC0"
// public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/.0/> for full details.
//
// Authors:
// - Isis Agora Lovecruft <isis@patternsinthevoid.net>
// - Henry de Valence <hdevalence@hdevalence.ca>

#![no_std]
#![cfg_attr(feature = "nightly", feature(asm))]
#![cfg_attr(feature = "nightly", feature(external_doc))]
#![cfg_attr(feature = "nightly", doc(include = "../README.md"))]
#![cfg_attr(feature = "nightly", deny(missing_docs))]
#![doc(html_logo_url = "https://doc.dalek.rs/assets/dalek-logo-clear.png")]

//! Note that docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

#[cfg(feature = "std")]
extern crate std;

use core::ops::{BitAnd, BitOr, BitXor, Not};

/// The `Choice` struct represents a choice for use in conditional
/// assignment.
///
/// It is a wrapper around a `u8`, which should have the value either
/// `1` (true) or `0` (false).
///
/// With the `nightly` feature enabled, the conversion from `u8` to
/// `Choice` passes the value through an optimization barrier, as a
/// best-effort attempt to prevent the compiler from inferring that the
/// `Choice` value is a boolean.  This strategy is based on Tim
/// Maclean's [work on `rust-timing-shield`][rust-timing-shield],
/// which attempts to provide a more comprehensive approach for
/// preventing software side-channels in Rust code.
///
/// The `Choice` struct implements operators for AND, OR, XOR, and
/// NOT, to allow combining `Choice` values.
/// These operations do not short-circuit.
///
/// [rust-timing-shield]: https://www.chosenplaintext.ca/open-source/rust-timing-shield/security
#[derive(Copy, Clone, Debug)]
pub struct Choice(u8);

impl Choice {
    /// The constant `Choice(1)`.
    pub const TRUE: Self = Choice(1);

    /// The constant `Choice(0)`.
    pub const FALSE: Self = Choice(0);

    /// Unwrap the `Choice` wrapper to reveal the underlying `u8`.
    ///
    /// # Note
    ///
    /// This function only exists as an escape hatch for the rare case
    /// where it's not possible to use one of the `subtle`-provided
    /// trait impls.
    #[inline]
    pub fn unwrap_u8(&self) -> u8 {
        self.0
    }
}

impl BitAnd for Choice {
    type Output = Choice;
    #[inline]
    fn bitand(self, rhs: Choice) -> Choice {
        (self.0 & rhs.0).into()
    }
}

impl BitOr for Choice {
    type Output = Choice;
    #[inline]
    fn bitor(self, rhs: Choice) -> Choice {
        (self.0 | rhs.0).into()
    }
}

impl BitXor for Choice {
    type Output = Choice;
    #[inline]
    fn bitxor(self, rhs: Choice) -> Choice {
        (self.0 ^ rhs.0).into()
    }
}

impl Not for Choice {
    type Output = Choice;
    #[inline]
    fn not(self) -> Choice {
        (1u8 & (!self.0)).into()
    }
}

/// This function is a best-effort attempt to prevent the compiler
/// from knowing anything about the value of the returned `u8`, other
/// than its type.
///
/// Uses inline asm when available, otherwise it's a no-op.
#[cfg(all(feature = "nightly", not(any(target_arch = "asmjs", target_arch = "wasm32"))))]
fn black_box(input: u8) -> u8 {
    debug_assert!(input == 0u8 || input == 1u8);

    // Pretend to access a register containing the input.  We "volatile" here
    // because some optimisers treat assembly templates without output operands
    // as "volatile" while others do not.
    unsafe { asm!("" :: "r"(&input) :: "volatile") }

    input
}

#[cfg(any(target_arch = "asmjs", target_arch = "wasm32", not(feature = "nightly")))]
#[inline(never)]
fn black_box(input: u8) -> u8 {
    debug_assert!(input == 0u8 || input == 1u8);
    // We don't have access to inline assembly or test::black_box or ...
    //
    // Bailing out, hopefully the compiler doesn't use the fact that `input` is 0 or 1.
    input
}

impl From<u8> for Choice {
    #[inline]
    fn from(input: u8) -> Choice {
        // Our goal is to prevent the compiler from inferring that the value held inside the
        // resulting `Choice` struct is really an `i1` instead of an `i8`.
        Choice(black_box(input))
    }
}

impl From<bool> for Choice {
    #[inline]
    fn from(input: bool) -> Choice {
        // Our goal is to prevent the compiler from inferring that the value held inside the
        // resulting `Choice` struct is really an `i1` instead of an `i8`.
        Choice(black_box(input as u8))
    }
}

/// An `Eq`-like trait that produces a `Choice` instead of a `bool`.
///
/// # Example
///
/// ```
/// use subtle::ConstantTimeEq;
/// let x: u8 = 5;
/// let y: u8 = 13;
///
/// assert_eq!(x.ct_eq(&y).unwrap_u8(), 0);
/// assert_eq!(x.ct_eq(&x).unwrap_u8(), 1);
/// ```
pub trait ConstantTimeEq {
    /// Determine if two items are equal.
    ///
    /// The `ct_eq` function should execute in constant time.
    ///
    /// # Returns
    ///
    /// * `Choice(1u8)` if `self == other`;
    /// * `Choice(0u8)` if `self != other`.
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice;
}

/// Select one of two inputs according to a `Choice` in constant time.
///
/// # Examples
///
/// ```
/// # use subtle;
/// use subtle::ConditionallySelectable;
/// use subtle::Choice;
/// let a: i32 = 5;
/// let b: i32 = 13;
///
/// assert_eq!(i32::conditional_select(&a, &b, Choice::from(0)), a);
/// assert_eq!(i32::conditional_select(&a, &b, Choice::from(1)), b);
/// ```
pub trait ConditionallySelectable {
    /// Select `a` or `b` according to `choice`.
    ///
    /// # Returns
    ///
    /// * `a` if `choice == Choice(0)`;
    /// * `b` if `choice == Choice(1)`.
    ///
    /// This function should execute in constant time.
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self;
}

/// A type which can be conditionally negated in constant time.
pub trait ConditionallyNegatable {
    /// Negate `self` if `choice == Choice(1)`; otherwise, leave it
    /// unchanged.
    ///
    /// This function should execute in constant time.
    #[inline]
    fn conditional_negate(&mut self, choice: Choice);
}

/// A type which can be conditionally assigned in constant time.
pub trait ConditionallyAssignable {
    /// Conditionally assign `other` to `self`, according to `choice`.
    ///
    /// This function should execute in constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate subtle;
    /// use subtle::ConditionallyAssignable;
    /// # fn main() {
    /// let mut x: u8 = 13;
    /// let y:     u8 = 42;
    ///
    /// x.conditional_assign(&y, 0.into());
    /// assert_eq!(x, 13);
    /// x.conditional_assign(&y, 1.into());
    /// assert_eq!(x, 42);
    /// # }
    /// ```
    ///
    #[inline]
    fn conditional_assign(&mut self, other: &Self, choice: Choice);
}

/// A type which is conditionally swappable in constant time.
pub trait ConditionallySwappable {
    /// Conditionally swap `self` and `other` if `choice == 1`; otherwise,
    /// reassign both unto themselves.
    ///
    /// This function should execute in constant time.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate subtle;
    /// use subtle::ConditionallySwappable;
    /// # fn main() {
    /// let mut x: u8 = 13;
    /// let mut y: u8 = 42;
    ///
    /// x.conditional_swap(&mut y, 0.into());
    /// assert_eq!(x, 13);
    /// assert_eq!(y, 42);
    /// x.conditional_swap(&mut y, 1.into());
    /// assert_eq!(x, 42);
    /// assert_eq!(y, 13);
    /// # }
    /// ```
    ///
    #[inline]
    fn conditional_swap(&mut self, other: &mut Self, choice: Choice);
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////// Trait Impls /////////////////////////////////
//////////////////////////////////////////////////////////////////////////////


macro_rules! to_signed_int {
    (u8) => {
        i8
    };
    (u16) => {
        i16
    };
    (u32) => {
        i32
    };
    (u64) => {
        i64
    };
    (u128) => {
        i128
    };
    (i8) => {
        i8
    };
    (i16) => {
        i16
    };
    (i32) => {
        i32
    };
    (i64) => {
        i64
    };
    (i128) => {
        i128
    };
}




/// Given the bit-width `$bit_width` and the corresponding primitive
/// unsigned and signed types `$t_u` and `$t_i` respectively, generate
/// a `ConstantTimeEq` implementation.
macro_rules! generate_integer_equal {
    ($t_u:ty, $t_i:ty, $bit_width:expr) => {
        impl ConstantTimeEq for $t_u {
            #[inline]
            fn ct_eq(&self, other: &$t_u) -> Choice {
                // Faster implementation compared to the old one.
                let l = *self;
                let r = *other;
                let bit_diff = l ^ r;
                let msb_iff_zero_diff = bit_diff.wrapping_sub(1) & !bit_diff;
                let unsigned_msb_iff_zero_diff = msb_iff_zero_diff as $t_u;
                Choice::from((unsigned_msb_iff_zero_diff >> ($bit_width - 1)) as u8)
            }
        }
        impl ConstantTimeEq for $t_i {
            #[inline]
            fn ct_eq(&self, other: &$t_i) -> Choice {
                // Bitcast to unsigned and call that implementation.
                (*self as $t_u).ct_eq(&(*other as $t_u))
            }
        }
    };
}

macro_rules! generate_integer_conditional_select_assign_swap {
    ($($t:tt)*) => ($(
            impl ConditionallySelectable for $t {
                #[inline]
                fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                    // if choice = 0, mask = (-0) = 0000...0000
                    // if choice = 1, mask = (-1) = 1111...1111
                    let mask = -(choice.unwrap_u8() as to_signed_int!($t)) as $t;
                    a ^ ((mask) & (a ^ b))
                }
            }
            impl ConditionallyAssignable for $t {
                #[inline]
                fn conditional_assign(&mut self, other: &Self, choice: Choice) {
                    *self = Self::conditional_select(self, other, choice);
                }
            }
            impl ConditionallySwappable for $t {
                #[inline]
                fn conditional_swap(&mut self, other: &mut Self, choice: Choice) {
                    let temp = *self;
                    self.conditional_assign(&other, choice);
                    other.conditional_assign(&temp, choice);
                }
            }
     )*)
}

macro_rules! generate_integer_conditional_negate {
    ($($t:tt)*) => ($(
        impl ConditionallyNegatable for $t {
            #[inline]
            fn conditional_negate(&mut self, choice: Choice) {
                let self_neg = -(self as &Self);
                *self = Self::conditional_select(self, &self_neg, choice);
            }
         }
    )*)
}

#[cfg(all(feature = "nightly", target_arch = "x86_64"))]
mod x86_64_cmov_impls {
    use super::*;
    macro_rules! to_nearest_cmovable_int {
        (u8) => {
            u16
        };
        (u16) => {
            u16
        };
        (u32) => {
            u32
        };
        (u64) => {
            u64
        };
        (i8) => {
            u16
        };
        (i16) => {
            u16
        };
        (i32) => {
            u32
        };
        (i64) => {
            u64
        };
    }

    macro_rules! generate_cmov_integer_conditional_select_assign_swap {
        ($($t:tt)*) => ($(
                impl ConditionallySelectable for $t {
                    #[inline]
                    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
                        let flag = choice.unwrap_u8();
                        let result: to_nearest_cmovable_int!($t);
                        let a = (*a) as to_nearest_cmovable_int!($t);
                        let b = (*b) as to_nearest_cmovable_int!($t);
                        unsafe {
                            asm!("cmp $1, $$1
                                  cmove $2, $3
                                  mov $0, $2"
                                : "=r"(result)
                                : "r"(flag), "r"(a), "r"(b) // inputs
                                : "cc"
                                : "intel"
                            );
                        }
                        result as $t
                    }
                }

                impl ConditionallyAssignable for $t {
                    #[inline]
                    fn conditional_assign(&mut self, other: &Self, choice: Choice) {
                        let flag = choice.unwrap_u8();
                        let mut a_copy = (*self) as to_nearest_cmovable_int!($t);
                        let b_copy = (*other) as to_nearest_cmovable_int!($t);
                        unsafe {
                            asm!("cmp $1, $$0
                                  cmove $2, $1
                                  mov [$3], $2"
                                :
                                : "r"(flag), "r"(a_copy), "r"(b_copy), "r"(&mut a_copy) // inputs
                                : "cc"
                                : "intel"
                            );
                        }
                        *self = a_copy as $t;
                    }
                }

                impl ConditionallySwappable for $t {
                    #[inline]
                    fn conditional_swap(&mut self, other: &mut Self, choice: Choice) {
                        let temp = *self;
                        self.conditional_assign(&other, choice);
                        other.conditional_assign(&temp, choice);
                    }
                }
         )*)
    }
    generate_cmov_integer_conditional_select_assign_swap!(  u8   i8);
    generate_cmov_integer_conditional_select_assign_swap!( u16  i16);
    generate_cmov_integer_conditional_select_assign_swap!( u32  i32);
    generate_cmov_integer_conditional_select_assign_swap!( u64  i64);

}

#[cfg(not(all(feature = "nightly", target_arch = "x86_64")))]
mod non_cmov_impls {
    use super::*;

    generate_integer_conditional_select_assign_swap!(  u8   i8);
    generate_integer_conditional_select_assign_swap!( u16  i16);
    generate_integer_conditional_select_assign_swap!( u32  i32);
    generate_integer_conditional_select_assign_swap!( u64  i64);

}



generate_integer_equal!(u8, i8, 8);
generate_integer_equal!(u16, i16, 16);
generate_integer_equal!(u32, i32, 32);
generate_integer_equal!(u64, i64, 64);
generate_integer_equal!(u128, i128, 128);


generate_integer_conditional_select_assign_swap!(u128 i128);

generate_integer_conditional_negate!(  i8);
generate_integer_conditional_negate!( i16);
generate_integer_conditional_negate!( i32);
generate_integer_conditional_negate!( i64);
generate_integer_conditional_negate!(i128);

impl ConstantTimeEq for Choice {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

///////////////////////////////////////
///////////////////////////////////////

macro_rules! generate_generic_conditional_assign_swap {
    ($($t:tt)*) => ($(
        impl ConditionallyAssignable for $t {
            #[inline]
            fn conditional_assign(&mut self, other: &Self, choice: Choice) {
                *self = Self::conditional_select(self, other, choice);
            }
        }
        impl ConditionallySwappable for $t {
            #[inline]
            fn conditional_swap(&mut self, other: &mut Self, choice: Choice) {
                let temp = *self;
                self.conditional_assign(&other, choice);
                other.conditional_assign(&temp, choice);
            }
        }
    )*)
}

///////////////////////////////////////

impl ConstantTimeEq for bool {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        (*self as u8).ct_eq(&(*other as u8))
    }
}

impl ConditionallySelectable for bool {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        // if choice = 0, mask = (-0) = 0000...0000
        // if choice = 1, mask = (-1) = 1111...1111
        let a = *a as u8;
        let b = *b as u8;
        
        let mask = -(choice.unwrap_u8() as i8) as u8;
        let result = a ^ ((mask) & (a ^ b));
        let output;
        #[cfg(feature="nightly")]
        unsafe {
            asm!("" : "=r"(output) : "0"(result));
        }
        #[cfg(not(feature="nightly"))]
        unsafe { output = core::mem::transmute(result); }
        output
    }
}
generate_generic_conditional_assign_swap!(bool);

impl ConditionallySelectable for Choice {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        u8::conditional_select(&a.0, &b.0, choice).into()
    }
}
generate_generic_conditional_assign_swap!(Choice);

///////////////////////////////////////
///////////////////////////////////////

impl<T: ConstantTimeEq> ConstantTimeEq for  [T] {
    /// Check whether two slices of `ConstantTimeEq` types are equal.
    ///
    /// # Note
    ///
    /// This function short-circuits if the lengths of the input slices
    /// are different.  Otherwise, it should execute in time independent
    /// of the slice contents.
    ///
    /// Since arrays coerce to slices, this function works with fixed-size arrays:
    ///
    /// ```
    /// # use subtle::ConstantTimeEq;
    /// #
    /// let a: [u8; 8] = [0,1,2,3,4,5,6,7];
    /// let b: [u8; 8] = [0,1,2,3,0,1,2,3];
    ///
    /// let a_eq_a = a.ct_eq(&a);
    /// let a_eq_b = a.ct_eq(&b);
    ///
    /// assert_eq!(a_eq_a.unwrap_u8(), 1);
    /// assert_eq!(a_eq_b.unwrap_u8(), 0);
    /// ```
    #[inline]
    fn ct_eq(&self, _rhs: &[T]) -> Choice {
        let len = self.len();

        // Short-circuit on the *lengths* of the slices, not their
        // contents.
        if len != _rhs.len() {
            return Choice::from(0);
        }

        // This loop shouldn't be shortcircuitable, since the compiler
        // shouldn't be able to reason about the value of the `u8`
        // unwrapped from the `ct_eq` result.
        let mut x = 1u8;
        for (ai, bi) in self.iter().zip(_rhs.iter()) {
            x &= ai.ct_eq(bi).unwrap_u8();
        }

        x.into()
    }
}

impl<T: ConditionallyAssignable> ConditionallyAssignable for [T] {
    /// Conditionally assign the contents of `other` to `self` if `choice == 1`;
    /// otherwise, reassign the contents of `self` to `self`.
    ///
    /// # Note
    ///
    /// In `debug` mode, this function panics if the lengths of the input slices
    /// are different. In `release` mode, it conditionally assigns the contents of
    /// the shorter slice to the equivalent locations in the longer slice.
    /// It does this in time independent of the slice contents.
    ///
    /// Since arrays coerce to slices, this function works with fixed-size arrays:
    ///
    /// ```
    /// # extern crate subtle;
    /// use subtle::ConditionallyAssignable;
    /// #
    /// # fn main() {
    ///
    /// let mut a: [u8; 8] = [0,1,2,3,4,5,6,7];
    /// let b: [u8; 8] = [0,1,2,3,0,1,2,3];
    ///
    /// a.conditional_assign(&b, 0.into());
    /// assert_eq!(a, [0,1,2,3,4,5,6,7]);
    /// a.conditional_assign(&b, 1.into());
    /// assert_eq!(a, b);
    /// # }
    /// ```
    #[inline]
    fn conditional_assign(&mut self, other: &Self, choice: Choice) {
        debug_assert_eq!(self.len(), other.len());
        for (a, b) in self.iter_mut().zip(other.iter()) {
            a.conditional_assign(b, choice);
        }
    }
}

impl<T: ConditionallySwappable> ConditionallySwappable for [T] {
    /// Conditionally swap the contents of `self` and `other` if `choice == 1`;
    /// otherwise, reassign both unto themselves.
    ///
    /// # Note
    ///
    /// In `debug` mode, this function panics if the lengths of the input slices
    /// are different. In `release` mode, it conditionally swaps the contents of
    /// the shorter slice into the equivalent locations in the longer slice.
    /// It does this in time independent of the slice contents.
    ///
    /// Since arrays coerce to slices, this function works with fixed-size arrays:
    ///
    /// ```
    /// # extern crate subtle;
    /// use subtle::ConditionallySwappable;
    /// #
    /// # fn main() {
    /// let mut a: [u8; 8] = [0,1,2,3,4,5,6,7];
    /// let mut b: [u8; 8] = [0,1,2,3,0,1,2,3];
    ///
    /// a.conditional_swap(&mut b, 0.into());
    /// assert_eq!(a, [0,1,2,3,4,5,6,7]);
    /// assert_eq!(b, [0,1,2,3,0,1,2,3]);
    ///
    /// a.conditional_swap(&mut b, 1.into());
    /// assert_eq!(a, [0,1,2,3,0,1,2,3]);
    /// assert_eq!(b, [0,1,2,3,4,5,6,7]);
    /// # }
    /// ```
    #[inline]
    fn conditional_swap(&mut self, other: &mut Self, choice: Choice) {
        debug_assert_eq!(self.len(), other.len());
        for (a, b) in self.iter_mut().zip(other.iter_mut()) {
            T::conditional_swap(a, b, choice);
        }
    }
}

///////////////////////////////////////
///////////////////////////////////////

impl ConstantTimeEq for () {
    #[inline]
    fn ct_eq(&self, _other: &Self) -> Choice {
        1.into()
    }
}

impl ConditionallySelectable for () {
    #[inline]
    fn conditional_select(_a: &Self, _b: &Self, _choice: Choice) -> Self {
        ()
    }
}

impl ConditionallyAssignable for () {
    #[inline]
    fn conditional_assign(&mut self, _other: &Self, _choice: Choice) {
    }
}

impl ConditionallySwappable for () {
    #[inline]
    fn conditional_swap(&mut self, _other: &mut Self, _choice: Choice) {}
}

// Modified from `serde`'s impl of `Serialize` for tuples.
macro_rules! generate_tuple_impls {
    ($(($($n:tt $name:ident)+))+) => {
        $(
            impl<$($name),+> ConstantTimeEq for ($($name,)+)
            where
                $($name: ConstantTimeEq,)+
            {
                #[inline]
                fn ct_eq(&self, other: &Self) -> Choice {
                    let mut all_equal = 1.into();

                    $(all_equal = all_equal & self.$n.ct_eq(&other.$n);)+
                    all_equal
                }
            }
            impl<$($name),+> ConditionallySelectable for ($($name,)+)
            where
                $($name: ConditionallySelectable,)+
            {
                #[inline]
                fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {

                    ($(
                        $name::conditional_select(&a.$n, &b.$n, choice),
                    )+)
                }
            }
            impl<$($name),+> ConditionallyAssignable for ($($name,)+)
            where
                $($name: ConditionallyAssignable,)+
            {
                #[inline]
                fn conditional_assign(&mut self, b: &Self, choice: Choice) {

                    $(
                        self.$n.conditional_assign(&b.$n, choice);
                    )+
                }
            }
            impl<$($name),+> ConditionallySwappable for ($($name,)+)
            where
                $($name: ConditionallySwappable,)+
            {
                #[inline]
                fn conditional_swap(&mut self, b: &mut Self, choice: Choice) {
                    $(
                        self.$n.conditional_swap(&mut b.$n, choice);
                    )+
                }
            }
        )+
    }
}

generate_tuple_impls! {
    (0 T0)
    (0 T0 1 T1)
    (0 T0 1 T1 2 T2)
    (0 T0 1 T1 2 T2 3 T3)
    (0 T0 1 T1 2 T2 3 T3 4 T4)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10)
    (0 T0 1 T1 2 T2 3 T3 4 T4 5 T5 6 T6 7 T7 8 T8 9 T9 10 T10 11 T11)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[should_panic]
    fn slices_equal_different_lengths() {
        let a: [u8; 3] = [0, 0, 0];
        let b: [u8; 4] = [0, 0, 0, 0];

        assert_eq!((&a).ct_eq(&b).unwrap_u8(), 1);
    }

    #[test]
    fn conditional_select_i8() {
        for i in ::std::i8::MIN..=::std::i8::MAX {
            for j in ::std::i8::MIN..=::std::i8::MAX {
                assert_eq!(i, i8::conditional_select(&i, &j, 0.into()));
                assert_eq!(j, i8::conditional_select(&i, &j, 1.into()));
            }
        }
    }

    #[test]
    fn conditional_swap_i8() {
        for i in ::std::i8::MIN..=::std::i8::MAX {
            for j in ::std::i8::MIN..=::std::i8::MAX {
                let mut i_copy = i;
                let mut j_copy = j;

                i_copy.conditional_swap(&mut j_copy, 0.into());
                assert_eq!((i, j), (i_copy, j_copy));

                i_copy.conditional_swap(&mut j_copy, 1.into());
                assert_eq!((i, j), (j_copy, i_copy));
            }
        }
    }

    #[test]
    fn conditional_assign_i8() {
        for i in ::std::i8::MIN..=::std::i8::MAX {
            for j in ::std::i8::MIN..=::std::i8::MAX {
                let mut i_copy = i;

                i_copy.conditional_assign(&j, 0.into());
                assert_eq!(i_copy, i);

                i_copy.conditional_assign(&j, 1.into());
                assert_eq!(i_copy, j);
            }
        }
    }

    #[test]
    fn conditional_select_u8() {
        for i in 0..=::std::u8::MAX {
            for j in 0..=::std::u8::MAX {
                assert_eq!(i, u8::conditional_select(&i, &j, 0.into()));
                assert_eq!(j, u8::conditional_select(&i, &j, 1.into()));
            }
        }
    }

    #[test]
    fn conditional_swap_u8() {
        for i in 0..=::std::u8::MAX {
            for j in 0..=::std::u8::MAX {
                let mut i_copy = i;
                let mut j_copy = j;

                i_copy.conditional_swap(&mut j_copy, 0.into());
                assert_eq!((i, j), (i_copy, j_copy));

                i_copy.conditional_swap(&mut j_copy, 1.into());
                assert_eq!((i, j), (j_copy, i_copy));
            }
        }
    }

    #[test]
    fn conditional_assign_u8() {
        for i in 0..=::std::u8::MAX {
            for j in 0..=::std::u8::MAX {
                let mut i_copy = i;

                i_copy.conditional_assign(&j, 0.into());
                assert_eq!(i_copy, i);

                i_copy.conditional_assign(&j, 1.into());
                assert_eq!(i_copy, j);
            }
        }
    }

    #[test]
    fn conditional_select_u16() {
        for i in 0..=::std::u16::MAX {
            for j in 0..=::std::u16::MAX {
                assert_eq!(i, u16::conditional_select(&i, &j, 0.into()));
                assert_eq!(j, u16::conditional_select(&i, &j, 1.into()));
            }
        }
    }

    #[test]
    fn conditional_swap_u16() {
        for i in 0..=::std::u16::MAX {
            for j in 0..=::std::u16::MAX {
                let mut i_copy = i;
                let mut j_copy = j;

                i_copy.conditional_swap(&mut j_copy, 0.into());
                assert_eq!((i, j), (i_copy, j_copy));

                i_copy.conditional_swap(&mut j_copy, 1.into());
                assert_eq!((i, j), (j_copy, i_copy));
            }
        }
    }

    #[test]
    fn conditional_assign_u16() {
        for i in 0..=::std::u16::MAX {
            for j in 0..=::std::u16::MAX {
                let mut i_copy = i;

                i_copy.conditional_assign(&j, 0.into());
                assert_eq!(i_copy, i);

                i_copy.conditional_assign(&j, 1.into());
                assert_eq!(i_copy, j);
            }
        }
    }

    #[test]
    fn slices_equal() {
        let a: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
        let b: [u8; 8] = [1, 2, 3, 4, 4, 3, 2, 1];

        let a_eq_a = (&a).ct_eq(&a);
        let a_eq_b = (&a).ct_eq(&b);

        assert_eq!(a_eq_a.unwrap_u8(), 1);
        assert_eq!(a_eq_b.unwrap_u8(), 0);

        let c: [u8; 16] = [0u8; 16];

        let a_eq_c = (&a).ct_eq(&c);
        assert_eq!(a_eq_c.unwrap_u8(), 0);
    }

    #[test]
    fn conditional_assign_i32() {
        let mut a: i32 = 5;
        let b: i32 = 13;

        a.conditional_assign(&b, 0.into());
        assert_eq!(a, 5);
        a.conditional_assign(&b, 1.into());
        assert_eq!(a, 13);
    }

    #[test]
    fn conditional_assign_i64() {
        let mut c: i64 = 2343249123;
        let d: i64 = 8723884895;

        c.conditional_assign(&d, 0.into());
        assert_eq!(c, 2343249123);
        c.conditional_assign(&d, 1.into());
        assert_eq!(c, 8723884895);
    }

    macro_rules! generate_integer_conditional_select_tests {
        ($($t:ty)*) => ($(
            let x: $t = 0;  // all 0 bits
            let y: $t = !0; // all 1 bits

            assert_eq!(<$t>::conditional_select(&x, &y, 0.into()), 0);
            assert_eq!(<$t>::conditional_select(&x, &y, 1.into()), y);
        )*)
    }

    #[test]
    fn integer_conditional_select() {
        generate_integer_conditional_select_tests!(u8 u16 u32 u64 u128);
        generate_integer_conditional_select_tests!(i8 i16 i32 i64 i128);
    }


    // Modified from `serde`'s impl of `Serialize` for tuples.
    macro_rules! generate_tuple_conditional_select_tests {
        ($(($($n:tt )+))+) => {
            $(
                let x = ($($n,)+);  // all 0 bits
                let y = ($(!$n,)+); // all 1 bits
                assert_eq!(ConditionallySelectable::conditional_select(&x, &y, 0.into()), x);
                assert_eq!(ConditionallySelectable::conditional_select(&x, &y, 1.into()), y);
            )+
        }
    }

    #[test]
    fn tuple_conditional_select() {
        generate_tuple_conditional_select_tests! {
            (0 )
            (0  0 )
            (0  0  0 )
            (0  0  0  0 )
            (0  0  0  0  0 )
            (0  0  0  0  0  0 )
            (0  0  0  0  0  0  0 )
            (0  0  0  0  0  0  0  0 )
            (0  0  0  0  0  0  0  0  0 )
            (0  0  0  0  0  0  0  0  0  0 )
            (0  0  0  0  0  0  0  0  0  0  0 )
            (0  0  0  0  0  0  0  0  0  0  0  0 )
        }
    }

    #[test]
    fn custom_conditional_select_i16() {
        let x: i16 = 257;
        let y: i16 = 514;

        assert_eq!(i16::conditional_select(&x, &y, 0.into()), 257);
        assert_eq!(i16::conditional_select(&x, &y, 1.into()), 514);
    }

    #[test]
    fn custom_conditional_swap_i64() {
        let mut x: i64 = 11234532463;
        let mut y: i64 = 412345124352;

        x.conditional_swap(&mut y, 0.into());
        assert_eq!(x, 11234532463);
        assert_eq!(y, 412345124352);
        x.conditional_swap(&mut y, 1.into());
        assert_eq!(x, 412345124352);
        assert_eq!(y, 11234532463);
    }

    macro_rules! generate_integer_equal_tests {
        ($($t:ty),*) => ($(
            let y: $t = 0;  // all 0 bits
            let z: $t = !0; // all 1 bits

            let x = z;

            assert_eq!(x.ct_eq(&y).unwrap_u8(), 0);
            assert_eq!(x.ct_eq(&z).unwrap_u8(), 1);
        )*)
    }

    #[test]
    fn integer_equal() {
        generate_integer_equal_tests!(u8, u16, u32, u64, u128);
        generate_integer_equal_tests!(i8, i16, i32, i64, i128);
    }
}
