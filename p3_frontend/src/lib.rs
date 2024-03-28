#![allow(unused_imports)]
extern crate alloc;

use halo2_middleware::circuit::{
    Any, ColumnMid, ConstraintSystemMid, ExpressionMid, GateMid, PreprocessingV2, QueryMid, VarMid,
};
use halo2_middleware::ff::{Field, PrimeField};
use halo2_middleware::permutation;
use halo2_middleware::poly::Rotation;
use num_bigint::BigUint;
use p3_air::{Air, AirBuilder, BaseAir, TwoRowMatrixView};
use p3_field::{AbstractField, Field as p3Field, Packable, PrimeField as p3PrimeField};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::HashMap;
// use p3_uni_stark::SymbolicAirBuilder;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
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

// pub trait FieldExt: PrimeField + Hash + Serialize {}

#[derive(Default, Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FWrap<F: Field>(F);

unsafe impl<F: Field> Send for FWrap<F> {}
unsafe impl<F: Field> Sync for FWrap<F> {}

impl<F: PrimeField> Serialize for FWrap<F> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self.0.to_repr().as_ref())
    }
}

struct FWrapVisitor<F>(PhantomData<F>);

impl<'de, F: PrimeField> de::Visitor<'de> for FWrapVisitor<F> {
    type Value = FWrap<F>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a field repr as bytes")
    }

    fn visit_bytes<E>(self, _value: &[u8]) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        todo!()
        // F::from_repr_vartime(value.into())
        //     .map(|v| FWrap(v))
        //     .ok_or(E::custom("invalid field repr: {:value?}"))
    }
}

impl<'de, F: PrimeField> Deserialize<'de> for FWrap<F> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(FWrapVisitor::<F>(PhantomData {}))
    }
}

impl<F: Field> fmt::Display for FWrap<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<F: PrimeField + Hash> AbstractField for FWrap<F> {
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

impl<F: Field> Add for FWrap<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0.add(rhs.0))
    }
}

impl<F: Field> AddAssign for FWrap<F> {
    fn add_assign(&mut self, rhs: Self) {
        self.0.add_assign(rhs.0)
    }
}

impl<F: Field> Sum for FWrap<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.sum()
    }
}

impl<F: Field> Sub for FWrap<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self(self.0.sub(rhs.0))
    }
}

impl<F: Field> SubAssign for FWrap<F> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0.sub_assign(rhs.0)
    }
}

impl<F: Field> Neg for FWrap<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(self.0.neg())
    }
}

impl<F: Field> Mul for FWrap<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self(self.0.mul(rhs.0))
    }
}

impl<F: Field> MulAssign for FWrap<F> {
    fn mul_assign(&mut self, rhs: Self) {
        self.0.mul_assign(rhs.0)
    }
}

impl<F: Field> Product for FWrap<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self(F::ONE))
    }
}

impl<F: Field> Div for FWrap<F> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self {
        let rhs_inv = rhs.0.invert().expect("division by 0");
        Self(self.0 * rhs_inv)
    }
}

impl<F: Field> Packable for FWrap<F> {}
impl<F: PrimeField + Hash> p3Field for FWrap<F> {
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

impl<F: PrimeField + Hash + Ord> p3PrimeField for FWrap<F> {
    fn as_canonical_biguint(&self) -> BigUint {
        let le = F::ONE.to_repr().as_ref()[0] == 1;
        if le {
            BigUint::from_bytes_le(self.0.to_repr().as_ref())
        } else {
            BigUint::from_bytes_be(self.0.to_repr().as_ref())
        }
    }
}

fn fixed_query_r0<F: PrimeField + Hash>(index: usize) -> ExpressionMid<F> {
    ExpressionMid::Var(VarMid::Query(QueryMid {
        column_index: index,
        column_type: Any::Fixed,
        rotation: Rotation(0),
    }))
}

const LOCATION_COLUMNS: usize = 3; // First, Transition, Last
const COL_FIRST: usize = 0;
const COL_LAST: usize = 1;
const COL_TRANSITION: usize = 2;

fn sym_to_expr<F: PrimeField + Hash>(e: &SymbolicExpression<FWrap<F>>) -> ExpressionMid<F> {
    match e {
        SymbolicExpression::Variable(var) => ExpressionMid::Var(VarMid::Query(QueryMid {
            column_index: var.column,
            column_type: Any::Advice,
            rotation: if var.is_next {
                Rotation(1)
            } else {
                Rotation(0)
            },
        })),
        SymbolicExpression::Location(Location::FirstRow) => fixed_query_r0(COL_FIRST),
        SymbolicExpression::Location(Location::LastRow) => fixed_query_r0(COL_LAST),
        SymbolicExpression::Location(Location::Transition) => fixed_query_r0(COL_TRANSITION),
        SymbolicExpression::Constant(c) => ExpressionMid::Constant(c.0),
        SymbolicExpression::Add(lhs, rhs) => sym_to_expr(&*lhs) + sym_to_expr(&*rhs),
        SymbolicExpression::Neg(e) => -sym_to_expr(&*e),
        SymbolicExpression::Mul(lhs, rhs) => sym_to_expr(&*lhs) * sym_to_expr(&*rhs),
    }
}

pub fn compile_preprocessing<F, A>(k: u32, size: usize, _air: &A) -> PreprocessingV2<F>
where
    F: PrimeField + Hash,
    A: Air<SymbolicAirBuilder<FWrap<F>>>,
{
    let n = 2usize.pow(k);
    let num_fixed_columns = LOCATION_COLUMNS;
    let mut fixed = vec![vec![F::ZERO; n]; num_fixed_columns];

    fixed[COL_FIRST][0] = F::ONE;
    fixed[COL_LAST][size - 1] = F::ONE;
    for i in 0..size {
        fixed[COL_TRANSITION][i] = F::ONE;
    }

    PreprocessingV2 {
        permutation: permutation::AssemblyMid { copies: Vec::new() },
        fixed,
    }
}

pub fn compile_circuit_cs<F, A>(air: &A, num_public_values: usize) -> ConstraintSystemMid<F>
where
    F: PrimeField + Hash,
    A: Air<SymbolicAirBuilder<FWrap<F>>>,
{
    let mut builder = SymbolicAirBuilder::new(air.width(), num_public_values);
    air.eval(&mut builder);
    // DBG
    // println!("main {:?}", builder.main);
    // for constraint in &builder.constraints {
    //     println!("> {:?}", constraint);
    // }

    let num_fixed_columns = LOCATION_COLUMNS;
    let num_advice_columns = air.width();

    let gates: Vec<GateMid<F>> = builder
        .constraints
        .iter()
        .enumerate()
        .map(|(i, e)| GateMid {
            name: format!("constraint{i}"),
            poly: sym_to_expr(e),
        })
        .collect();

    ConstraintSystemMid::<F> {
        num_fixed_columns,
        num_advice_columns,
        num_instance_columns: 0, // TODO: Support public inputs
        num_challenges: 0,
        unblinded_advice_columns: Vec::new(),
        advice_column_phase: (0..num_advice_columns).map(|_| 0).collect(),
        challenge_phase: Vec::new(),
        gates,
        permutation: permutation::ArgumentMid {
            columns: Vec::new(),
        },
        lookups: Vec::new(),
        shuffles: Vec::new(),
        general_column_annotations: HashMap::new(),
        minimum_degree: None,
    }
}

pub fn trace_to_wit<F: Field>(k: u32, trace: RowMajorMatrix<FWrap<F>>) -> Vec<Option<Vec<F>>> {
    let n = 2usize.pow(k);
    let num_columns = trace.width;
    let mut witness = vec![vec![F::ZERO; n]; num_columns];
    for (row_offset, row) in trace.rows().enumerate() {
        for column_index in 0..num_columns {
            witness[column_index][row_offset] = row[column_index].0;
        }
    }
    witness.into_iter().map(|column| Some(column)).collect()
}
