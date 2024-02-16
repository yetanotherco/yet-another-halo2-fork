use super::circuit::{ExpressionMid, VarMid};
use ff::Field;

/// Expressions involved in a shuffle argument, with a name as metadata.
#[derive(Clone, Debug)]
pub struct ArgumentV2<F: Field> {
    pub name: String,
    pub input_expressions: Vec<ExpressionMid<F, VarMid>>,
    pub shuffle_expressions: Vec<ExpressionMid<F, VarMid>>,
}
