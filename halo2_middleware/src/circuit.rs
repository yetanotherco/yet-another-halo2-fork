use crate::expression::{Expression, Variable};
use crate::poly::Rotation;
use crate::{lookup, metadata, permutation, shuffle};
use ff::Field;
use std::collections::HashMap;

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

pub type ExpressionMid<F> = Expression<F, VarMid>;

/// A Gate contains a single polynomial identity with a name as metadata.
#[derive(Clone, Debug)]
pub struct GateMid<F: Field> {
    pub name: String,
    pub poly: ExpressionMid<F>,
}

impl<F: Field> GateMid<F> {
    /// Returns the gate name.
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    /// Returns the polynomial identity of this gate
    pub fn polynomial(&self) -> &ExpressionMid<F> {
        &self.poly
    }
}

/// This is a description of the circuit environment, such as the gate, column and
/// permutation arrangements.
#[derive(Debug, Clone)]
pub struct ConstraintSystemMid<F: Field> {
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

    pub gates: Vec<GateMid<F>>,

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
    pub cs: ConstraintSystemMid<F>,
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
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F>;
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
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F> {
        ExpressionMid::Var(VarMid::Query(QueryMid::Advice(AdviceQueryMid {
            column_index: index,
            rotation: at,
            phase: self.phase,
        })))
    }
}
impl ColumnType for Fixed {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F> {
        ExpressionMid::Var(VarMid::Query(QueryMid::Fixed(FixedQueryMid {
            column_index: index,
            rotation: at,
        })))
    }
}
impl ColumnType for Instance {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F> {
        ExpressionMid::Var(VarMid::Query(QueryMid::Instance(InstanceQueryMid {
            column_index: index,
            rotation: at,
        })))
    }
}
impl ColumnType for Any {
    fn query_cell<F: Field>(&self, index: usize, at: Rotation) -> ExpressionMid<F> {
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
