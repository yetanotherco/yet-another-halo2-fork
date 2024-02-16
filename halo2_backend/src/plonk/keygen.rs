#![allow(clippy::int_plus_one)]

use group::Curve;
use halo2_middleware::ff::{Field, FromUniformBytes};

use super::{evaluation::Evaluator, permutation, Polynomial, ProvingKey, VerifyingKey};
use crate::{
    arithmetic::{parallelize, CurveAffine},
    poly::{
        commitment::{Blind, Params},
        EvaluationDomain,
    },
};
use halo2_common::plonk::circuit::{Circuit, Column, ConstraintSystem};
use halo2_common::plonk::{
    lookup, sealed, shuffle, AdviceQuery, Error, Expression, FixedQuery, Gate, InstanceQuery,
    Queries,
};
use halo2_middleware::circuit::{
    Advice, Any, CompiledCircuitV2, ConstraintSystemV2Backend, ExpressionMid, Fixed, Instance,
    QueryMid, VarMid,
};
use halo2_middleware::poly::Rotation;
use std::collections::HashMap;

pub(crate) fn create_domain<C, ConcreteCircuit>(
    k: u32,
    #[cfg(feature = "circuit-params")] params: ConcreteCircuit::Params,
) -> (
    EvaluationDomain<C::Scalar>,
    ConstraintSystem<C::Scalar>,
    ConcreteCircuit::Config,
)
where
    C: CurveAffine,
    ConcreteCircuit: Circuit<C::Scalar>,
{
    let mut cs = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut cs, params);
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut cs);

    let degree = cs.degree();

    let domain = EvaluationDomain::new(degree as u32, k);

    (domain, cs, config)
}

/// Generate a `VerifyingKey` from an instance of `CompiledCircuit`.
pub fn keygen_vk_v2<'params, C, P>(
    params: &P,
    circuit: &CompiledCircuitV2<C::Scalar>,
) -> Result<VerifyingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
    C::Scalar: FromUniformBytes<64>,
{
    let cs2 = &circuit.cs;
    let cs: ConstraintSystem<C::Scalar> = csv2_to_cs(cs2.clone());
    let domain = EvaluationDomain::new(cs.degree() as u32, params.k());

    if (params.n() as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    let permutation_vk = permutation::keygen::Assembly::new_from_assembly_mid(
        params.n() as usize,
        &cs2.permutation,
        &circuit.preprocessing.permutation,
    )?
    .build_vk(params, &domain, &cs.permutation);

    let fixed_commitments = circuit
        .preprocessing
        .fixed
        .iter()
        .map(|poly| {
            params
                .commit_lagrange(
                    &Polynomial::new_lagrange_from_vec(poly.clone()),
                    Blind::default(),
                )
                .to_affine()
        })
        .collect();

    Ok(VerifyingKey::from_parts(
        domain,
        fixed_commitments,
        permutation_vk,
        cs,
        Vec::new(),
        false,
    ))
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `CompiledCircuit`.
pub fn keygen_pk_v2<'params, C, P>(
    params: &P,
    vk: VerifyingKey<C>,
    circuit: &CompiledCircuitV2<C::Scalar>,
) -> Result<ProvingKey<C>, Error>
where
    C: CurveAffine,
    P: Params<'params, C>,
{
    let cs = &circuit.cs;

    if (params.n() as usize) < vk.cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    let fixed_polys: Vec<_> = circuit
        .preprocessing
        .fixed
        .iter()
        .map(|poly| {
            vk.domain
                .lagrange_to_coeff(Polynomial::new_lagrange_from_vec(poly.clone()))
        })
        .collect();

    let fixed_cosets = fixed_polys
        .iter()
        .map(|poly| vk.domain.coeff_to_extended(poly.clone()))
        .collect();

    let permutation_pk = permutation::keygen::Assembly::new_from_assembly_mid(
        params.n() as usize,
        &cs.permutation,
        &circuit.preprocessing.permutation,
    )?
    .build_pk(params, &vk.domain, &cs.permutation.clone().into());

    // Compute l_0(X)
    // TODO: this can be done more efficiently
    // https://github.com/privacy-scaling-explorations/halo2/issues/269
    let mut l0 = vk.domain.empty_lagrange();
    l0[0] = C::Scalar::ONE;
    let l0 = vk.domain.lagrange_to_coeff(l0);
    let l0 = vk.domain.coeff_to_extended(l0);

    // Compute l_blind(X) which evaluates to 1 for each blinding factor row
    // and 0 otherwise over the domain.
    let mut l_blind = vk.domain.empty_lagrange();
    for evaluation in l_blind[..].iter_mut().rev().take(vk.cs.blinding_factors()) {
        *evaluation = C::Scalar::ONE;
    }
    let l_blind = vk.domain.lagrange_to_coeff(l_blind);
    let l_blind = vk.domain.coeff_to_extended(l_blind);

    // Compute l_last(X) which evaluates to 1 on the first inactive row (just
    // before the blinding factors) and 0 otherwise over the domain
    let mut l_last = vk.domain.empty_lagrange();
    l_last[params.n() as usize - vk.cs.blinding_factors() - 1] = C::Scalar::ONE;
    let l_last = vk.domain.lagrange_to_coeff(l_last);
    let l_last = vk.domain.coeff_to_extended(l_last);

    // Compute l_active_row(X)
    let one = C::Scalar::ONE;
    let mut l_active_row = vk.domain.empty_extended();
    parallelize(&mut l_active_row, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = i + start;
            *value = one - (l_last[idx] + l_blind[idx]);
        }
    });

    // Compute the optimized evaluation data structure
    let ev = Evaluator::new(&vk.cs);

    Ok(ProvingKey {
        vk,
        l0,
        l_last,
        l_active_row,
        fixed_values: circuit
            .preprocessing
            .fixed
            .clone()
            .into_iter()
            .map(Polynomial::new_lagrange_from_vec)
            .collect(),
        fixed_polys,
        fixed_cosets,
        permutation: permutation_pk,
        ev,
    })
}

struct QueriesMap {
    advice_map: HashMap<(Column<Advice>, Rotation), usize>,
    instance_map: HashMap<(Column<Instance>, Rotation), usize>,
    fixed_map: HashMap<(Column<Fixed>, Rotation), usize>,
    advice: Vec<(Column<Advice>, Rotation)>,
    instance: Vec<(Column<Instance>, Rotation)>,
    fixed: Vec<(Column<Fixed>, Rotation)>,
}

impl QueriesMap {
    fn add_advice(&mut self, col: Column<Advice>, rot: Rotation) -> usize {
        *self.advice_map.entry((col, rot)).or_insert_with(|| {
            self.advice.push((col, rot));
            self.advice.len() - 1
        })
    }
    fn add_instance(&mut self, col: Column<Instance>, rot: Rotation) -> usize {
        *self.instance_map.entry((col, rot)).or_insert_with(|| {
            self.instance.push((col, rot));
            self.instance.len() - 1
        })
    }
    fn add_fixed(&mut self, col: Column<Fixed>, rot: Rotation) -> usize {
        *self.fixed_map.entry((col, rot)).or_insert_with(|| {
            self.fixed.push((col, rot));
            self.fixed.len() - 1
        })
    }
}

impl QueriesMap {
    fn as_expression<F: Field>(&mut self, expr: &ExpressionMid<F, VarMid>) -> Expression<F> {
        match expr {
            ExpressionMid::Constant(c) => Expression::Constant(*c),
            ExpressionMid::Var(VarMid::Query(QueryMid::Fixed(query))) => {
                let (col, rot) = (Column::new(query.column_index, Fixed), query.rotation);
                let index = self.add_fixed(col, rot);
                Expression::Fixed(FixedQuery {
                    index: Some(index),
                    column_index: query.column_index,
                    rotation: query.rotation,
                })
            }
            ExpressionMid::Var(VarMid::Query(QueryMid::Advice(query))) => {
                let (col, rot) = (
                    Column::new(query.column_index, Advice { phase: query.phase }),
                    query.rotation,
                );
                let index = self.add_advice(col, rot);
                Expression::Advice(AdviceQuery {
                    index: Some(index),
                    column_index: query.column_index,
                    rotation: query.rotation,
                    phase: sealed::Phase(query.phase),
                })
            }
            ExpressionMid::Var(VarMid::Query(QueryMid::Instance(query))) => {
                let (col, rot) = (Column::new(query.column_index, Instance), query.rotation);
                let index = self.add_instance(col, rot);
                Expression::Instance(InstanceQuery {
                    index: Some(index),
                    column_index: query.column_index,
                    rotation: query.rotation,
                })
            }
            ExpressionMid::Var(VarMid::Challenge(c)) => Expression::Challenge((*c).into()),
            ExpressionMid::Negated(e) => Expression::Negated(Box::new(self.as_expression(e))),
            ExpressionMid::Sum(lhs, rhs) => Expression::Sum(
                Box::new(self.as_expression(lhs)),
                Box::new(self.as_expression(rhs)),
            ),
            ExpressionMid::Product(lhs, rhs) => Expression::Product(
                Box::new(self.as_expression(lhs)),
                Box::new(self.as_expression(rhs)),
            ),
            ExpressionMid::Scaled(e, c) => Expression::Scaled(Box::new(self.as_expression(e)), *c),
        }
    }
}

/// Collect queries used in gates while mapping those gates to equivalent ones with indexed
/// query references in the expressions.
fn cs2_collect_queries_gates<F: Field>(
    cs2: &ConstraintSystemV2Backend<F>,
    queries: &mut QueriesMap,
) -> Vec<Gate<F>> {
    cs2.gates
        .iter()
        .map(|gate| Gate {
            name: gate.name.clone(),
            constraint_names: Vec::new(),
            polys: vec![queries.as_expression(gate.polynomial())],
            queried_selectors: Vec::new(), // Unused?
            queried_cells: Vec::new(),     // Unused?
        })
        .collect()
}

/// Collect queries used in lookups while mapping those lookups to equivalent ones with indexed
/// query references in the expressions.
fn cs2_collect_queries_lookups<F: Field>(
    cs2: &ConstraintSystemV2Backend<F>,
    queries: &mut QueriesMap,
) -> Vec<lookup::Argument<F>> {
    cs2.lookups
        .iter()
        .map(|lookup| lookup::Argument {
            name: lookup.name.clone(),
            input_expressions: lookup
                .input_expressions
                .iter()
                .map(|e| queries.as_expression(e))
                .collect(),
            table_expressions: lookup
                .table_expressions
                .iter()
                .map(|e| queries.as_expression(e))
                .collect(),
        })
        .collect()
}

/// Collect queries used in shuffles while mapping those lookups to equivalent ones with indexed
/// query references in the expressions.
fn cs2_collect_queries_shuffles<F: Field>(
    cs2: &ConstraintSystemV2Backend<F>,
    queries: &mut QueriesMap,
) -> Vec<shuffle::Argument<F>> {
    cs2.shuffles
        .iter()
        .map(|shuffle| shuffle::Argument {
            name: shuffle.name.clone(),
            input_expressions: shuffle
                .input_expressions
                .iter()
                .map(|e| queries.as_expression(e))
                .collect(),
            shuffle_expressions: shuffle
                .shuffle_expressions
                .iter()
                .map(|e| queries.as_expression(e))
                .collect(),
        })
        .collect()
}

/// Collect all queries used in the expressions of gates, lookups and shuffles.  Map the
/// expressions of gates, lookups and shuffles into equivalent ones with indexed query
/// references.
#[allow(clippy::type_complexity)]
fn collect_queries<F: Field>(
    cs2: &ConstraintSystemV2Backend<F>,
) -> (
    Queries,
    Vec<Gate<F>>,
    Vec<lookup::Argument<F>>,
    Vec<shuffle::Argument<F>>,
) {
    let mut queries = QueriesMap {
        advice_map: HashMap::new(),
        instance_map: HashMap::new(),
        fixed_map: HashMap::new(),
        advice: Vec::new(),
        instance: Vec::new(),
        fixed: Vec::new(),
    };

    let gates = cs2_collect_queries_gates(cs2, &mut queries);
    let lookups = cs2_collect_queries_lookups(cs2, &mut queries);
    let shuffles = cs2_collect_queries_shuffles(cs2, &mut queries);

    // Each column used in a copy constraint involves a query at rotation current.
    for column in &cs2.permutation.columns {
        match column.column_type {
            Any::Instance => {
                queries.add_instance(Column::new(column.index, Instance), Rotation::cur())
            }
            Any::Fixed => queries.add_fixed(Column::new(column.index, Fixed), Rotation::cur()),
            Any::Advice(advice) => {
                queries.add_advice(Column::new(column.index, advice), Rotation::cur())
            }
        };
    }

    let mut num_advice_queries = vec![0; cs2.num_advice_columns];
    for (column, _) in queries.advice.iter() {
        num_advice_queries[column.index()] += 1;
    }

    let queries = Queries {
        advice: queries.advice,
        instance: queries.instance,
        fixed: queries.fixed,
        num_advice_queries,
    };
    (queries, gates, lookups, shuffles)
}

// TODO: Rename this function after renaming the types
// https://github.com/privacy-scaling-explorations/halo2/issues/263
fn csv2_to_cs<F: Field>(cs2: ConstraintSystemV2Backend<F>) -> ConstraintSystem<F> {
    let (queries, gates, lookups, shuffles) = collect_queries(&cs2);
    ConstraintSystem {
        num_fixed_columns: cs2.num_fixed_columns,
        num_advice_columns: cs2.num_advice_columns,
        num_instance_columns: cs2.num_instance_columns,
        num_selectors: 0,
        num_challenges: cs2.num_challenges,
        unblinded_advice_columns: cs2.unblinded_advice_columns,
        advice_column_phase: cs2
            .advice_column_phase
            .into_iter()
            .map(sealed::Phase)
            .collect(),
        challenge_phase: cs2.challenge_phase.into_iter().map(sealed::Phase).collect(),
        selector_map: Vec::new(),
        gates,
        advice_queries: queries.advice,
        num_advice_queries: queries.num_advice_queries,
        instance_queries: queries.instance,
        fixed_queries: queries.fixed,
        permutation: cs2.permutation.into(),
        lookups,
        shuffles,
        general_column_annotations: cs2.general_column_annotations,
        constants: Vec::new(),
        minimum_degree: None,
    }
}
