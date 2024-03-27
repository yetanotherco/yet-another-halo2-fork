// The MIT License (MIT)
//
// Copyright (c) 2022 The Plonky3 Authors
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues};
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_ceil_usize;

use crate::symbolic_expression::SymbolicExpression;
use crate::symbolic_variable::SymbolicVariable;

pub fn get_log_quotient_degree<F, A>(air: &A, num_public_values: usize) -> usize
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    // We pad to at least degree 2, since a quotient argument doesn't make sense with smaller degrees.
    let constraint_degree = get_max_constraint_degree(air, num_public_values).max(2);

    // The quotient's actual degree is approximately (max_constraint_degree - 1) n,
    // where subtracting 1 comes from division by the zerofier.
    // But we pad it to a power of two so that we can efficiently decompose the quotient.
    log2_ceil_usize(constraint_degree - 1)
}

pub fn get_max_constraint_degree<F, A>(air: &A, num_public_values: usize) -> usize
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    get_symbolic_constraints(air, num_public_values)
        .iter()
        .map(|c| c.degree_multiple())
        .max()
        .unwrap_or(0)
}

pub fn get_symbolic_constraints<F, A>(
    air: &A,
    num_public_values: usize,
) -> Vec<SymbolicExpression<F>>
where
    F: Field,
    A: Air<SymbolicAirBuilder<F>>,
{
    let mut builder = SymbolicAirBuilder::new(air.width(), num_public_values);
    air.eval(&mut builder);
    builder.constraints()
}

/// An `AirBuilder` for evaluating constraints symbolically, and recording them for later use.
pub struct SymbolicAirBuilder<F: Field> {
    main: RowMajorMatrix<SymbolicVariable<F>>,
    public_values: Vec<F>,
    constraints: Vec<SymbolicExpression<F>>,
}

impl<F: Field> SymbolicAirBuilder<F> {
    pub(crate) fn new(width: usize, num_public_values: usize) -> Self {
        let values = [false, true]
            .into_iter()
            .flat_map(|is_next| {
                (0..width).map(move |column| SymbolicVariable {
                    is_next,
                    column,
                    _phantom: PhantomData,
                })
            })
            .collect();
        Self {
            main: RowMajorMatrix::new(values, width),
            // TODO replace zeros once we have SymbolicExpression::PublicValue
            public_values: vec![F::zero(); num_public_values],
            constraints: vec![],
        }
    }

    pub(crate) fn constraints(self) -> Vec<SymbolicExpression<F>> {
        self.constraints
    }
}

impl<F: Field> AirBuilder for SymbolicAirBuilder<F> {
    type F = F;
    type Expr = SymbolicExpression<F>;
    type Var = SymbolicVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        SymbolicExpression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        SymbolicExpression::IsLastRow
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            SymbolicExpression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.constraints.push(x.into());
    }
}

impl<F: Field> AirBuilderWithPublicValues for SymbolicAirBuilder<F> {
    fn public_values(&self) -> &[Self::F] {
        self.public_values.as_slice()
    }
}
