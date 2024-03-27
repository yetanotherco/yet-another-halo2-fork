#![allow(unused_imports)]
extern crate alloc;

use halo2_middleware::circuit::{ColumnMid, ExpressionMid, VarMid};
use halo2_middleware::ff::{Field, PrimeField};
use num_bigint::BigUint;
use p3_air::{Air, AirBuilder, BaseAir, TwoRowMatrixView};
use p3_field::{AbstractField, Field as p3Field, Packable};
// use p3_uni_stark::SymbolicAirBuilder;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::fmt;
use std::hash::Hash;
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Deref, Div, Mul, MulAssign, Neg, Sub, SubAssign};

mod symbolic_builder;
mod symbolic_expression;
mod symbolic_variable;

pub use symbolic_builder::*;
pub use symbolic_expression::*;
pub use symbolic_variable::*;

pub trait FieldExt: PrimeField + Hash + Serialize {}

#[derive(Default, Clone, Copy, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub struct FWrap<F: FieldExt>(F);

unsafe impl<F: FieldExt> Send for FWrap<F> {}
unsafe impl<F: FieldExt> Sync for FWrap<F> {}

// impl<F: FieldExt> Deref for FWrap<F> {
//     type Target = F;
//
//     fn deref(&self) -> &Self::Target {
//         &self.0
//     }
// }

impl<F: FieldExt> fmt::Display for FWrap<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<F: FieldExt> AbstractField for FWrap<F>
where
    for<'a> F: Deserialize<'a>,
{
    type F = Self;

    fn zero() -> Self {
        Self(F::ZERO)
    }
    fn one() -> Self {
        Self(F::ONE)
    }
    fn two() -> Self {
        Self(F::from(2u64))
    }
    fn neg_one() -> Self {
        Self(F::ZERO - F::ONE)
    }

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f
    }

    fn from_bool(b: bool) -> Self {
        Self(F::from(u64::from(b)))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self(F::from(u64::from(n)))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self(F::from(u64::from(n)))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self(F::from(u64::from(n)))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self(F::from(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self(F::from(n as u64))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        // A u32 must be canonical, plus we don't store canonical encodings anyway, so there's no
        // need for a reduction.
        Self(F::from(u64::from(n)))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        // There's no need to reduce `n` to canonical form, as our internal encoding is
        // non-canonical, so there's no need for a reduction.
        Self(F::from(n))
    }

    fn generator() -> Self {
        Self(F::MULTIPLICATIVE_GENERATOR)
    }
}

impl<F: FieldExt> Add for FWrap<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0.add(rhs.0))
    }
}

// impl<'a, F: FieldExt> Add<&'a FWrap<F>> for FWrap<F> {
//     type Output = Self;
//
//     fn add(self, rhs: &'a Self) -> Self {
//         Self(self.add(rhs.0))
//     }
// }

impl<F: FieldExt> AddAssign for FWrap<F> {
    fn add_assign(&mut self, rhs: Self) {
        self.0.add_assign(rhs.0)
    }
}

// impl<'a, F: FieldExt> AddAssign<&'a FWrap<F>> for FWrap<F> {
//     fn add_assign(&mut self, rhs: &'a Self) {
//         Self(self.0.add_assign(rhs.0))
//     }
// }

impl<F: FieldExt> Sum for FWrap<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.sum()
    }
}

// impl<'a, F: FieldExt> Sum<&'a FWrap<F>> for FWrap<F> {
//     fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
//         iter.sum()
//     }
// }

impl<F: FieldExt> Sub for FWrap<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self(self.0.sub(rhs.0))
    }
}

// impl<'a, F: FieldExt> Sub<&'a FWrap<F>> for FWrap<F> {
//     type Output = Self;
//
//     fn sub(self, rhs: &'a Self) -> Self {
//         Self(self.0.sub(rhs.0))
//     }
// }

impl<F: FieldExt> SubAssign for FWrap<F> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0.sub_assign(rhs.0)
    }
}

// impl<'a, F: FieldExt> SubAssign<&'a FWrap<F>> for FWrap<F> {
//     fn sub_assign(&mut self, rhs: &'a Self) {
//         Self(self.0.sub_assign(rhs.0))
//     }
// }

impl<F: FieldExt> Neg for FWrap<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(self.0.neg())
    }
}

impl<F: FieldExt> Mul for FWrap<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self(self.0.mul(rhs.0))
    }
}

// impl<'a, F: FieldExt> Mul<&'a FWrap<F>> for FWrap<F> {
//     type Output = Self;
//
//     fn mul(self, rhs: &'a Self) -> Self {
//         Self(self.0.mul(rhs.0))
//     }
// }

impl<F: FieldExt> MulAssign for FWrap<F> {
    fn mul_assign(&mut self, rhs: Self) {
        self.0.mul_assign(rhs.0)
    }
}

// impl<'a, F: FieldExt> MulAssign<&'a FWrap<F>> for FWrap<F> {
//     fn mul_assign(&mut self, rhs: &'a Self) {
//         Self(self.0.mul_assign(rhs.0))
//     }
// }

impl<F: FieldExt> Product for FWrap<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self(F::ONE))
    }
}

// impl<'a, F: FieldExt> Product<&'a FWrap<F>> for FWrap<F> {
//     fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
//         iter.reduce(|x, y| x * y).unwrap_or(Self::one())
//     }
// }

impl<F: FieldExt> Div for FWrap<F> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        let rhs_inv = rhs.0.invert().expect("division by 0");
        Self(self.0 * rhs_inv)
    }
}

// impl<F: FieldExt> Field for FWrap<F> {}
impl<F: FieldExt> Packable for FWrap<F> {}
impl<F: FieldExt> p3Field for FWrap<F>
where
    for<'a> F: Deserialize<'a>,
{
    type Packing = Self;

    fn is_zero(&self) -> bool {
        self.0.is_zero().into()
    }

    fn try_inverse(&self) -> Option<Self> {
        let inverse = self.0.invert();

        if inverse.is_some().into() {
            Some(Self(inverse.unwrap()))
        } else {
            None
        }
    }

    fn order() -> BigUint {
        let minus_one = F::ZERO - F::ONE;
        let minus_one_repr = minus_one.to_repr();
        let le = F::ONE.to_repr().as_ref()[0] == 1;
        let mut minus_one = if le {
            BigUint::from_bytes_le(minus_one_repr.as_ref())
        } else {
            BigUint::from_bytes_be(minus_one_repr.as_ref())
        };
        minus_one += 1u64;
        let p = minus_one;
        p
    }
}

pub fn compile<F, A>(air: &A, num_public_values: usize)
where
    for<'a> F: FieldExt + Deserialize<'a>,
    A: Air<SymbolicAirBuilder<FWrap<F>>>,
{
    let mut builder = SymbolicAirBuilder::new(air.width(), num_public_values);
    air.eval(&mut builder);
}
