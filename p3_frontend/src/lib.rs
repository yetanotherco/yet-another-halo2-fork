#![allow(unused_imports)]
extern crate alloc;

use halo2_middleware::circuit::{
    Any, Cell, ColumnMid, CompiledCircuitV2, ConstraintSystemMid, ExpressionMid, GateMid,
    PreprocessingV2, QueryMid, VarMid,
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

mod air;
mod symbolic_builder;
mod symbolic_expression;
mod symbolic_variable;

pub use air::*;
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

const LOCATION_COLUMNS: usize = 3; // First, Last, Transition
const COL_FIRST: usize = 0;
const COL_LAST: usize = 1;
const COL_TRANS: usize = 2;

fn sym_to_expr<F: PrimeField + Hash>(e: &SymbolicExpression<FWrap<F>>) -> ExpressionMid<F> {
    match e {
        SymbolicExpression::Variable(SymbolicVariable(Var::Query(query), _)) => {
            ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index: query.column,
                column_type: Any::Advice,
                rotation: if query.is_next {
                    Rotation(1)
                } else {
                    Rotation(0)
                },
            }))
        }
        SymbolicExpression::Variable(SymbolicVariable(Var::Public(public), _)) => {
            panic!("unexpected public variable {:?} in expression", public)
        }
        SymbolicExpression::Location(Location::FirstRow) => fixed_query_r0(COL_FIRST),
        SymbolicExpression::Location(Location::LastRow) => fixed_query_r0(COL_LAST),
        SymbolicExpression::Location(Location::Transition) => fixed_query_r0(COL_TRANS),
        SymbolicExpression::Constant(c) => ExpressionMid::Constant(c.0),
        SymbolicExpression::Add(lhs, rhs) => sym_to_expr(&*lhs) + sym_to_expr(&*rhs),
        SymbolicExpression::Neg(e) => -sym_to_expr(&*e),
        SymbolicExpression::Mul(lhs, rhs) => sym_to_expr(&*lhs) * sym_to_expr(&*rhs),
    }
}

pub fn compile_preprocessing<F, A>(
    k: u32,
    size: usize,
    pre: &PreprocessingInfo,
    _air: &A,
) -> PreprocessingV2<F>
where
    F: PrimeField + Hash,
    A: Air<SymbolicAirBuilder<FWrap<F>>>,
{
    let n = 2usize.pow(k);
    let num_fixed_columns = LOCATION_COLUMNS;
    let mut fixed = vec![vec![F::ZERO; n]; num_fixed_columns];

    fixed[COL_FIRST][0] = F::ONE;
    fixed[COL_LAST][size - 1] = F::ONE;
    for i in 0..size - 1 {
        fixed[COL_TRANS][i] = F::ONE;
    }

    let mut copies = Vec::new();
    for (cell, public) in &pre.copy_public {
        let advice_row = match cell.1 {
            Location::FirstRow => 0,
            Location::LastRow => size - 1,
            Location::Transition => unreachable!(),
        };
        copies.push((
            Cell {
                column: ColumnMid {
                    column_type: Any::Advice,
                    index: cell.0,
                },
                row: advice_row,
            },
            Cell {
                column: ColumnMid {
                    column_type: Any::Instance,
                    index: 0,
                },
                row: *public,
            },
        ));
    }

    PreprocessingV2 {
        permutation: permutation::AssemblyMid { copies },
        fixed,
    }
}

// TODO: Rewrite with https://doc.rust-lang.org/beta/unstable-book/language-features/box-patterns.html
// Check if the constraint is an equality against a public input and extract the copy constraint as
// `(advice_column_index, Location)` and `public_index`.  If there's no copy constriant, return
// None.
fn extract_copy_public<F: PrimeField + Hash>(
    e: &SymbolicExpression<FWrap<F>>,
) -> Option<((usize, Location), usize)> {
    use SymbolicExpression as SE;
    use SymbolicVariable as SV;
    // Example:
    // Mul(
    //   Location(FirstRow),
    //   Add(
    //     Variable(SymbolicVariable(Query(Query { is_next: false, column: 0 }))),
    //     Neg(Variable(SymbolicVariable(Public(Public { index: 0 }))))
    //   )
    // )
    let (mul_lhs, mul_rhs) = match e {
        SE::Mul(lhs, rhs) => (&**lhs, &**rhs),
        _ => return None,
    };
    let location = match mul_lhs {
        SE::Location(location @ (Location::FirstRow | Location::LastRow)) => *location,
        _ => return None,
    };
    let (add_lhs, add_rhs) = match mul_rhs {
        SE::Add(lhs, rhs) => (&**lhs, &**rhs),
        _ => return None,
    };
    let cell = match add_lhs {
        SE::Variable(SV(
            Var::Query(Query {
                is_next: false,
                column,
            }),
            _,
        )) => (*column, location),
        _ => return None,
    };
    let neg = match add_rhs {
        SE::Neg(e) => &**e,
        _ => return None,
    };
    let public = match neg {
        SE::Variable(SV(Var::Public(Public { index }), _)) => *index,
        _ => return None,
    };
    Some((cell, public))
}

pub fn get_public_inputs<F: Field>(
    preprocessing_info: &PreprocessingInfo,
    size: usize,
    witness: &Vec<Option<Vec<F>>>,
) -> Vec<F> {
    let mut public_inputs = vec![F::ZERO; preprocessing_info.num_public_values];
    for (cell, public_index) in &preprocessing_info.copy_public {
        let offset = match cell.1 {
            Location::FirstRow => 0,
            Location::LastRow => size - 1,
            Location::Transition => unreachable!(),
        };
        public_inputs[*public_index] = witness[cell.0].as_ref().unwrap()[offset]
    }
    public_inputs
}

pub struct PreprocessingInfo {
    copy_public: Vec<((usize, Location), usize)>,
    num_public_values: usize,
}

pub fn compile_circuit_cs<F, A>(
    air: &A,
    num_public_values: usize,
) -> (ConstraintSystemMid<F>, PreprocessingInfo)
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

    let mut gates: Vec<GateMid<F>> = Vec::new();
    // copy between `(advice_column_index, Location)` and `public_index`.
    let mut copy_public: Vec<((usize, Location), usize)> = Vec::new();
    let mut copy_columns: Vec<ColumnMid> = Vec::new();
    for (i, constraint) in builder.constraints.iter().enumerate() {
        // Check if the constraint is an equality against a public input and store it as a copy
        // constraint.  Otherwise it's a gate that can't have public variables.
        if let Some((cell, public)) = extract_copy_public(constraint) {
            copy_public.push((cell.clone(), public));
            let column = ColumnMid {
                column_type: Any::Advice,
                index: cell.0,
            };
            if !copy_columns.contains(&column) {
                copy_columns.push(column);
            }
            continue;
        };
        gates.push(GateMid {
            name: format!("constraint{i}"),
            poly: sym_to_expr(constraint),
        });
    }
    let mut num_instance_columns = 0;
    if !copy_public.is_empty() {
        copy_columns.push(ColumnMid {
            column_type: Any::Instance,
            index: 0,
        });
        num_instance_columns += 1;
    }

    let cs = ConstraintSystemMid::<F> {
        num_fixed_columns,
        num_advice_columns,
        num_instance_columns,
        num_challenges: 0,
        unblinded_advice_columns: Vec::new(),
        advice_column_phase: (0..num_advice_columns).map(|_| 0).collect(),
        challenge_phase: Vec::new(),
        gates,
        permutation: permutation::ArgumentMid {
            columns: copy_columns,
        },
        lookups: Vec::new(),
        shuffles: Vec::new(),
        general_column_annotations: HashMap::new(),
        minimum_degree: None,
    };
    (
        cs,
        PreprocessingInfo {
            copy_public,
            num_public_values,
        },
    )
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

// TODO: Move to middleware
pub fn check_witness<F: Field>(
    circuit: &CompiledCircuitV2<F>,
    k: u32,
    witness: &Vec<Option<Vec<F>>>,
    public: &[&[F]],
) {
    let n = 2usize.pow(k);
    let cs = &circuit.cs;
    let preprocessing = &circuit.preprocessing;
    for (i, gate) in cs.gates.iter().enumerate() {
        for offset in 0..n {
            let res = gate.poly.evaluate(
                &|s| s,
                &|v| match v {
                    VarMid::Query(q) => {
                        let offset = offset as i32 + q.rotation.0;
                        // TODO: Try to do mod n with a rust function
                        let offset = if offset < 0 {
                            (offset + n as i32) as usize
                        } else if offset >= n as i32 {
                            (offset - n as i32) as usize
                        } else {
                            offset as usize
                        };
                        match q.column_type {
                            Any::Instance => public[q.column_index][offset],
                            Any::Advice => witness[q.column_index].as_ref().unwrap()[offset],
                            Any::Fixed => preprocessing.fixed[q.column_index][offset],
                        }
                    }
                    VarMid::Challenge(_c) => unimplemented!(),
                },
                &|ne| -ne,
                &|a, b| a + b,
                &|a, b| a * b,
            );
            if !res.is_zero_vartime() {
                println!(
                    "Unsatisfied gate {} \"{}\" at offset {}",
                    i, gate.name, offset
                );
                panic!("");
            }
        }
    }
    println!("Check witness: OK");
}
