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

use core::marker::PhantomData;
use core::ops::{Add, Mul, Sub};

use p3_field::Field;

use crate::symbolic_expression::SymbolicExpression;

/// A variable within the evaluation window, i.e. a column in either the local or next row.
#[derive(Copy, Clone, Debug)]
pub struct SymbolicVariable<F: Field>(pub Var, pub PhantomData<F>);

#[derive(Copy, Clone, Debug)]
pub enum Var {
    Query(Query),
    Public(Public),
}

#[derive(Copy, Clone, Debug)]
pub struct Query {
    pub is_next: bool,
    pub column: usize,
}

#[derive(Copy, Clone, Debug)]
pub struct Public {
    pub index: usize,
}

impl<F: Field> SymbolicVariable<F> {
    pub fn new_query(is_next: bool, column: usize) -> Self {
        Self(Var::Query(Query { is_next, column }), PhantomData)
    }
    pub fn new_public(index: usize) -> Self {
        Self(Var::Public(Public { index }), PhantomData)
    }
}

impl<F: Field> From<SymbolicVariable<F>> for SymbolicExpression<F> {
    fn from(value: SymbolicVariable<F>) -> Self {
        SymbolicExpression::Variable(value)
    }
}

impl<F: Field> Add for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: Self) -> Self::Output {
        SymbolicExpression::from(self) + SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Add<F> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: F) -> Self::Output {
        SymbolicExpression::from(self) + SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Add<SymbolicExpression<F>> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: SymbolicExpression<F>) -> Self::Output {
        SymbolicExpression::from(self) + rhs
    }
}

impl<F: Field> Add<SymbolicVariable<F>> for SymbolicExpression<F> {
    type Output = Self;

    fn add(self, rhs: SymbolicVariable<F>) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: Field> Sub for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        SymbolicExpression::from(self) - SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Sub<F> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: F) -> Self::Output {
        SymbolicExpression::from(self) - SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Sub<SymbolicExpression<F>> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: SymbolicExpression<F>) -> Self::Output {
        SymbolicExpression::from(self) - rhs
    }
}

impl<F: Field> Sub<SymbolicVariable<F>> for SymbolicExpression<F> {
    type Output = Self;

    fn sub(self, rhs: SymbolicVariable<F>) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: Field> Mul for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: Self) -> Self::Output {
        SymbolicExpression::from(self) * SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Mul<F> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: F) -> Self::Output {
        SymbolicExpression::from(self) * SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Mul<SymbolicExpression<F>> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: SymbolicExpression<F>) -> Self::Output {
        SymbolicExpression::from(self) * rhs
    }
}

impl<F: Field> Mul<SymbolicVariable<F>> for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: SymbolicVariable<F>) -> Self::Output {
        self * Self::from(rhs)
    }
}
