use crate::poly::Rotation;
use crate::{lookup, metadata, permutation, shuffle};
use core::cmp::max;
use core::ops::{Add, Mul, Neg, Sub};
use ff::Field;
use std::collections::HashMap;
use std::iter::{Product, Sum};

/// Query of fixed column at a certain relative location
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FixedQueryMid {
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
}

/// Query of advice column at a certain relative location
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AdviceQueryMid {
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
    /// Phase of this advice column
    pub phase: u8,
}

/// Query of instance column at a certain relative location
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InstanceQueryMid {
    /// Column index
    pub column_index: usize,
    /// Rotation of this query
    pub rotation: Rotation,
}

/// A challenge squeezed from transcript after advice columns at the phase have been committed.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ChallengeMid {
    pub index: usize,
    pub phase: u8,
}

impl ChallengeMid {
    /// Index of this challenge.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Phase of this challenge.
    pub fn phase(&self) -> u8 {
        self.phase
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum QueryMid {
    /// This is a fixed column queried at a certain relative location
    Fixed(FixedQueryMid),
    /// This is an advice (witness) column queried at a certain relative location
    Advice(AdviceQueryMid),
    /// This is an instance (external) column queried at a certain relative location
    Instance(InstanceQueryMid),
}

pub trait Variable: Clone + Copy + std::fmt::Debug + Eq + PartialEq {
    /// Degree that an expression would have if it was only this variable.
    fn degree(&self) -> usize;

    /// Return true if this variable is a virtual abstraction that may be transformed later.  Two
    /// expressions containing virtual variables cannot be added or multiplied, this means an
    /// expression can only contain up to one virtual variable.  An expression containing a virtual
    /// variable cannot appear in a lookup.  Originally this is only fulfilled by the simple
    /// selector abstraction in the halo2 frontend.
    /// Overwrite this if the Variable has a virtual case.
    fn is_virtual(&self) -> bool {
        false
    }

    /// Return the name of the virtual variable case.  Originally this is used for "simple
    /// selector".
    /// Overwrite this if the Variable has a virtual case.
    fn virtual_var_case() -> &'static str {
        unimplemented!();
    }

    /// Approximate the computational complexity an expression would have if it was only this
    /// variable.
    fn complexity(&self) -> usize {
        0
    }

    /// Write an identifier of the variable.  If two variables have the same identifier, they must
    /// be the same variable.
    fn write_identifier<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()>;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VarMid {
    /// This is a generic column query
    Query(QueryMid),
    /// This is a challenge
    Challenge(ChallengeMid),
}

impl Variable for VarMid {
    fn degree(&self) -> usize {
        match self {
            VarMid::Query(_) => 1,
            VarMid::Challenge(_) => 0,
        }
    }

    fn complexity(&self) -> usize {
        match self {
            VarMid::Query(_) => 1,
            VarMid::Challenge(_) => 0,
        }
    }

    fn write_identifier<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        match self {
            VarMid::Query(QueryMid::Fixed(query)) => {
                write!(
                    writer,
                    "fixed[{}][{}]",
                    query.column_index, query.rotation.0
                )
            }
            VarMid::Query(QueryMid::Advice(query)) => {
                write!(
                    writer,
                    "advice[{}][{}]",
                    query.column_index, query.rotation.0
                )
            }
            VarMid::Query(QueryMid::Instance(query)) => {
                write!(
                    writer,
                    "instance[{}][{}]",
                    query.column_index, query.rotation.0
                )
            }
            VarMid::Challenge(challenge) => {
                write!(writer, "challenge[{}]", challenge.index())
            }
        }
    }
}

/// Low-degree expression representing an identity that must hold over the committed columns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpressionMid<F, V: Variable> {
    /// This is a constant polynomial
    Constant(F),
    /// This is a variable
    Var(V),
    /// This is a negated polynomial
    Negated(Box<ExpressionMid<F, V>>),
    /// This is the sum of two polynomials
    Sum(Box<ExpressionMid<F, V>>, Box<ExpressionMid<F, V>>),
    /// This is the product of two polynomials
    Product(Box<ExpressionMid<F, V>>, Box<ExpressionMid<F, V>>),
    /// This is a scaled polynomial
    Scaled(Box<ExpressionMid<F, V>>, F),
}

impl<F: Field, V: Variable> ExpressionMid<F, V> {
    /// Evaluate the polynomial using the provided closures to perform the
    /// operations.
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate<T>(
        &self,
        constant: &impl Fn(F) -> T,
        var: &impl Fn(V) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
    ) -> T {
        match self {
            ExpressionMid::Constant(scalar) => constant(*scalar),
            ExpressionMid::Var(v) => var(*v),
            ExpressionMid::Negated(a) => {
                let a = a.evaluate(constant, var, negated, sum, product, scaled);
                negated(a)
            }
            ExpressionMid::Sum(a, b) => {
                let a = a.evaluate(constant, var, negated, sum, product, scaled);
                let b = b.evaluate(constant, var, negated, sum, product, scaled);
                sum(a, b)
            }
            ExpressionMid::Product(a, b) => {
                let a = a.evaluate(constant, var, negated, sum, product, scaled);
                let b = b.evaluate(constant, var, negated, sum, product, scaled);
                product(a, b)
            }
            ExpressionMid::Scaled(a, f) => {
                let a = a.evaluate(constant, var, negated, sum, product, scaled);
                scaled(a, *f)
            }
        }
    }

    /// Evaluate the polynomial lazily using the provided closures to perform the
    /// operations.
    #[allow(clippy::too_many_arguments)]
    pub fn evaluate_lazy<T: PartialEq>(
        &self,
        constant: &impl Fn(F) -> T,
        var: &impl Fn(V) -> T,
        negated: &impl Fn(T) -> T,
        sum: &impl Fn(T, T) -> T,
        product: &impl Fn(T, T) -> T,
        scaled: &impl Fn(T, F) -> T,
        zero: &T,
    ) -> T {
        match self {
            ExpressionMid::Constant(scalar) => constant(*scalar),
            ExpressionMid::Var(v) => var(*v),
            ExpressionMid::Negated(a) => {
                let a = a.evaluate_lazy(constant, var, negated, sum, product, scaled, zero);
                negated(a)
            }
            ExpressionMid::Sum(a, b) => {
                let a = a.evaluate_lazy(constant, var, negated, sum, product, scaled, zero);
                let b = b.evaluate_lazy(constant, var, negated, sum, product, scaled, zero);
                sum(a, b)
            }
            ExpressionMid::Product(a, b) => {
                let (a, b) = if a.complexity() <= b.complexity() {
                    (a, b)
                } else {
                    (b, a)
                };
                let a = a.evaluate_lazy(constant, var, negated, sum, product, scaled, zero);

                if a == *zero {
                    a
                } else {
                    let b = b.evaluate_lazy(constant, var, negated, sum, product, scaled, zero);
                    product(a, b)
                }
            }
            ExpressionMid::Scaled(a, f) => {
                let a = a.evaluate_lazy(constant, var, negated, sum, product, scaled, zero);
                scaled(a, *f)
            }
        }
    }

    fn write_identifier<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        match self {
            ExpressionMid::Constant(scalar) => write!(writer, "{scalar:?}"),
            ExpressionMid::Var(v) => v.write_identifier(writer),
            ExpressionMid::Negated(a) => {
                writer.write_all(b"(-")?;
                a.write_identifier(writer)?;
                writer.write_all(b")")
            }
            ExpressionMid::Sum(a, b) => {
                writer.write_all(b"(")?;
                a.write_identifier(writer)?;
                writer.write_all(b"+")?;
                b.write_identifier(writer)?;
                writer.write_all(b")")
            }
            ExpressionMid::Product(a, b) => {
                writer.write_all(b"(")?;
                a.write_identifier(writer)?;
                writer.write_all(b"*")?;
                b.write_identifier(writer)?;
                writer.write_all(b")")
            }
            ExpressionMid::Scaled(a, f) => {
                a.write_identifier(writer)?;
                write!(writer, "*{f:?}")
            }
        }
    }

    /// Identifier for this expression. Expressions with identical identifiers
    /// do the same calculation (but the expressions don't need to be exactly equal
    /// in how they are composed e.g. `1 + 2` and `2 + 1` can have the same identifier).
    pub fn identifier(&self) -> String {
        let mut cursor = std::io::Cursor::new(Vec::new());
        self.write_identifier(&mut cursor).unwrap();
        String::from_utf8(cursor.into_inner()).unwrap()
    }

    /// Compute the degree of this polynomial
    pub fn degree(&self) -> usize {
        use ExpressionMid::*;
        match self {
            Constant(_) => 0,
            Var(v) => v.degree(),
            Negated(poly) => poly.degree(),
            Sum(a, b) => max(a.degree(), b.degree()),
            Product(a, b) => a.degree() + b.degree(),
            Scaled(poly, _) => poly.degree(),
        }
    }

    /// Approximate the computational complexity of this expression.
    pub fn complexity(&self) -> usize {
        match self {
            ExpressionMid::Constant(_) => 0,
            ExpressionMid::Var(v) => v.complexity(),
            ExpressionMid::Negated(poly) => poly.complexity() + 5,
            ExpressionMid::Sum(a, b) => a.complexity() + b.complexity() + 15,
            ExpressionMid::Product(a, b) => a.complexity() + b.complexity() + 30,
            ExpressionMid::Scaled(poly, _) => poly.complexity() + 30,
        }
    }

    /// Square this expression.
    pub fn square(self) -> Self {
        self.clone() * self
    }

    /// Returns whether or not this expression contains a virtual variable.  Originally this was
    /// the simple `Selector`.
    pub fn contains_virtual_var(&self) -> bool {
        self.evaluate(
            &|_| false,
            &|var| var.is_virtual(),
            &|a| a,
            &|a, b| a || b,
            &|a, b| a || b,
            &|a, _| a,
        )
    }
}

impl<F: Field, V: Variable> Neg for ExpressionMid<F, V> {
    type Output = ExpressionMid<F, V>;
    fn neg(self) -> Self::Output {
        ExpressionMid::Negated(Box::new(self))
    }
}

impl<F: Field, V: Variable> Add for ExpressionMid<F, V> {
    type Output = ExpressionMid<F, V>;
    fn add(self, rhs: ExpressionMid<F, V>) -> ExpressionMid<F, V> {
        if self.contains_virtual_var() || rhs.contains_virtual_var() {
            panic!(
                "attempted to use a {} in an addition",
                V::virtual_var_case()
            );
        }
        ExpressionMid::Sum(Box::new(self), Box::new(rhs))
    }
}

impl<F: Field, V: Variable> Sub for ExpressionMid<F, V> {
    type Output = ExpressionMid<F, V>;
    fn sub(self, rhs: ExpressionMid<F, V>) -> ExpressionMid<F, V> {
        if self.contains_virtual_var() || rhs.contains_virtual_var() {
            panic!(
                "attempted to use a {} in a subtraction",
                V::virtual_var_case()
            );
        }
        ExpressionMid::Sum(Box::new(self), Box::new(-rhs))
    }
}

impl<F: Field, V: Variable> Mul for ExpressionMid<F, V> {
    type Output = ExpressionMid<F, V>;
    fn mul(self, rhs: ExpressionMid<F, V>) -> ExpressionMid<F, V> {
        if self.contains_virtual_var() || rhs.contains_virtual_var() {
            panic!(
                "attempted to multiply two expressions containing {}s",
                V::virtual_var_case()
            );
        }
        ExpressionMid::Product(Box::new(self), Box::new(rhs))
    }
}

impl<F: Field, V: Variable> Mul<F> for ExpressionMid<F, V> {
    type Output = ExpressionMid<F, V>;
    fn mul(self, rhs: F) -> ExpressionMid<F, V> {
        ExpressionMid::Scaled(Box::new(self), rhs)
    }
}

impl<F: Field, V: Variable> Sum<Self> for ExpressionMid<F, V> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x)
            .unwrap_or(ExpressionMid::Constant(F::ZERO))
    }
}

impl<F: Field, V: Variable> Product<Self> for ExpressionMid<F, V> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x)
            .unwrap_or(ExpressionMid::Constant(F::ONE))
    }
}

/// A Gate contains a single polynomial identity with a name as metadata.
#[derive(Clone, Debug)]
pub struct GateV2Backend<F: Field> {
    pub name: String,
    pub poly: ExpressionMid<F, VarMid>,
}

impl<F: Field> GateV2Backend<F> {
    /// Returns the gate name.
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    /// Returns the polynomial identity of this gate
    pub fn polynomial(&self) -> &ExpressionMid<F, VarMid> {
        &self.poly
    }
}

/// This is a description of the circuit environment, such as the gate, column and
/// permutation arrangements.
#[derive(Debug, Clone)]
pub struct ConstraintSystemV2Backend<F: Field> {
    pub num_fixed_columns: usize,
    pub num_advice_columns: usize,
    pub num_instance_columns: usize,
    pub num_challenges: usize,

    /// Contains the index of each advice column that is left unblinded.
    pub unblinded_advice_columns: Vec<usize>,

    /// Contains the phase for each advice column. Should have same length as num_advice_columns.
    pub advice_column_phase: Vec<u8>,
    /// Contains the phase for each challenge. Should have same length as num_challenges.
    pub challenge_phase: Vec<u8>,

    pub gates: Vec<GateV2Backend<F>>,

    // Permutation argument for performing equality constraints
    pub permutation: permutation::ArgumentV2,

    // Vector of lookup arguments, where each corresponds to a sequence of
    // input expressions and a sequence of table expressions involved in the lookup.
    pub lookups: Vec<lookup::ArgumentV2<F>>,

    // Vector of shuffle arguments, where each corresponds to a sequence of
    // input expressions and a sequence of shuffle expressions involved in the shuffle.
    pub shuffles: Vec<shuffle::ArgumentV2<F>>,

    // List of indexes of Fixed columns which are associated to a circuit-general Column tied to their annotation.
    pub general_column_annotations: HashMap<metadata::Column, String>,
}

/// Data that needs to be preprocessed from a circuit
#[derive(Debug, Clone)]
pub struct PreprocessingV2<F: Field> {
    pub permutation: permutation::AssemblyMid,
    pub fixed: Vec<Vec<F>>,
}

/// This is a description of a low level Plonkish compiled circuit. Contains the Constraint System
/// as well as the fixed columns and copy constraints information.
#[derive(Debug, Clone)]
pub struct CompiledCircuitV2<F: Field> {
    pub preprocessing: PreprocessingV2<F>,
    pub cs: ConstraintSystemV2Backend<F>,
}

// TODO: The query_cell method is only used in the frontend, which uses Expression.  By having this
// trait implemented here we can only return ExpressionMid, which requires conversion to Expression
// when used.  On the other hand, it's difficult to move ColumnType to the frontend because this
// trait is implemented for Any which is used in the backend.  It would be great to find a way to
// move all the `query_cell` implementations to the frontend and have them return `Expression`,
// while keeping `Any` in the middleware.
// https://github.com/privacy-scaling-explorations/halo2/issues/270
/// A column type
pub trait ColumnType:
    'static + Sized + Copy + std::fmt::Debug + PartialEq + Eq + Into<Any>
{
    /// Return expression from cell
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F, VarMid>;
}

/// A column with an index and type
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct ColumnMid {
    /// The index of the column.
    pub index: usize,
    /// The type of the column.
    pub column_type: Any,
}

/// A cell identifies a position in the plonkish matrix identified by a column and a row offset.
#[derive(Clone, Debug)]
pub struct Cell {
    pub column: ColumnMid,
    pub row: usize,
}

/// An advice column
#[derive(Default, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Advice {
    pub phase: u8,
}

impl Advice {
    /// Returns `Advice` in given `Phase`
    pub fn new(phase: u8) -> Advice {
        Advice { phase }
    }

    /// Phase of this column
    pub fn phase(&self) -> u8 {
        self.phase
    }
}

impl std::fmt::Debug for Advice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_struct = f.debug_struct("Advice");
        // Only show advice's phase if it's not in first phase.
        if self.phase != 0 {
            debug_struct.field("phase", &self.phase);
        }
        debug_struct.finish()
    }
}

/// A fixed column
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Fixed;

/// An instance column
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Instance;

/// An enum over the Advice, Fixed, Instance structs
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
pub enum Any {
    /// An Advice variant
    Advice(Advice),
    /// A Fixed variant
    Fixed,
    /// An Instance variant
    Instance,
}

impl Any {
    /// Returns Advice variant in `FirstPhase`
    pub fn advice() -> Any {
        Any::Advice(Advice::default())
    }

    /// Returns Advice variant in given `Phase`
    pub fn advice_in(phase: u8) -> Any {
        Any::Advice(Advice::new(phase))
    }
}

impl std::fmt::Debug for Any {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Any::Advice(advice) => {
                let mut debug_struct = f.debug_struct("Advice");
                // Only show advice's phase if it's not in first phase.
                if advice.phase != 0 {
                    debug_struct.field("phase", &advice.phase);
                }
                debug_struct.finish()
            }
            Any::Fixed => f.debug_struct("Fixed").finish(),
            Any::Instance => f.debug_struct("Instance").finish(),
        }
    }
}

impl Ord for Any {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // This ordering is consensus-critical! The layouters rely on deterministic column
        // orderings.
        match (self, other) {
            (Any::Instance, Any::Instance) | (Any::Fixed, Any::Fixed) => std::cmp::Ordering::Equal,
            (Any::Advice(lhs), Any::Advice(rhs)) => lhs.phase.cmp(&rhs.phase),
            // Across column types, sort Instance < Advice < Fixed.
            (Any::Instance, Any::Advice(_))
            | (Any::Advice(_), Any::Fixed)
            | (Any::Instance, Any::Fixed) => std::cmp::Ordering::Less,
            (Any::Fixed, Any::Instance)
            | (Any::Fixed, Any::Advice(_))
            | (Any::Advice(_), Any::Instance) => std::cmp::Ordering::Greater,
        }
    }
}

impl PartialOrd for Any {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ColumnType for Advice {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F, VarMid> {
        ExpressionMid::Var(VarMid::Query(QueryMid::Advice(AdviceQueryMid {
            column_index: index,
            rotation: at,
            phase: self.phase,
        })))
    }
}
impl ColumnType for Fixed {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F, VarMid> {
        ExpressionMid::Var(VarMid::Query(QueryMid::Fixed(FixedQueryMid {
            column_index: index,
            rotation: at,
        })))
    }
}
impl ColumnType for Instance {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F, VarMid> {
        ExpressionMid::Var(VarMid::Query(QueryMid::Instance(InstanceQueryMid {
            column_index: index,
            rotation: at,
        })))
    }
}
impl ColumnType for Any {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F, VarMid> {
        match self {
            Any::Advice(Advice { phase }) => {
                ExpressionMid::Var(VarMid::Query(QueryMid::Advice(AdviceQueryMid {
                    column_index: index,
                    rotation: at,
                    phase: *phase,
                })))
            }
            Any::Fixed => ExpressionMid::Var(VarMid::Query(QueryMid::Fixed(FixedQueryMid {
                column_index: index,
                rotation: at,
            }))),
            Any::Instance => {
                ExpressionMid::Var(VarMid::Query(QueryMid::Instance(InstanceQueryMid {
                    column_index: index,
                    rotation: at,
                })))
            }
        }
    }
}

impl From<Advice> for Any {
    fn from(advice: Advice) -> Any {
        Any::Advice(advice)
    }
}

impl From<Fixed> for Any {
    fn from(_: Fixed) -> Any {
        Any::Fixed
    }
}

impl From<Instance> for Any {
    fn from(_: Instance) -> Any {
        Any::Instance
    }
}
