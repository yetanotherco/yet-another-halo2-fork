//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

// use crate::plonk::circuit::Column;
use crate::transcript::ChallengeScalar;
use halo2_middleware::circuit::ColumnMid;
use halo2_middleware::poly::Rotation;

/// List of queries (columns and rotations) used by a circuit
#[derive(Debug, Clone)]
pub struct Queries {
    /// List of unique advice queries
    pub advice: Vec<(ColumnMid, Rotation)>,
    /// List of unique instance queries
    pub instance: Vec<(ColumnMid, Rotation)>,
    /// List of unique fixed queries
    pub fixed: Vec<(ColumnMid, Rotation)>,
    /// Contains an integer for each advice column
    /// identifying how many distinct queries it has
    /// so far; should be same length as cs.num_advice_columns.
    pub num_advice_queries: Vec<usize>,
}

impl Queries {
    /// Returns the minimum necessary rows that need to exist in order to
    /// account for e.g. blinding factors.
    pub fn minimum_rows(&self) -> usize {
        self.blinding_factors() // m blinding factors
            + 1 // for l_{-(m + 1)} (l_last)
            + 1 // for l_0 (just for extra breathing room for the permutation
                // argument, to essentially force a separation in the
                // permutation polynomial between the roles of l_last, l_0
                // and the interstitial values.)
            + 1 // for at least one row
    }

    /// Compute the number of blinding factors necessary to perfectly blind
    /// each of the prover's witness polynomials.
    pub fn blinding_factors(&self) -> usize {
        // All of the prover's advice columns are evaluated at no more than
        let factors = *self.num_advice_queries.iter().max().unwrap_or(&1);
        // distinct points during gate checks.

        // - The permutation argument witness polynomials are evaluated at most 3 times.
        // - Each lookup argument has independent witness polynomials, and they are
        //   evaluated at most 2 times.
        let factors = std::cmp::max(3, factors);

        // Each polynomial is evaluated at most an additional time during
        // multiopen (at x_3 to produce q_evals):
        let factors = factors + 1;

        // h(x) is derived by the other evaluations so it does not reveal
        // anything; in fact it does not even appear in the proof.

        // h(x_3) is also not revealed; the verifier only learns a single
        // evaluation of a polynomial in x_1 which has h(x_3) and another random
        // polynomial evaluated at x_3 as coefficients -- this random polynomial
        // is "random_poly" in the vanishing argument.

        // Add an additional blinding factor as a slight defense against
        // off-by-one errors.
        factors + 1
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Theta;
pub type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

#[derive(Clone, Copy, Debug)]
pub struct Beta;
pub type ChallengeBeta<F> = ChallengeScalar<F, Beta>;

#[derive(Clone, Copy, Debug)]
pub struct Gamma;
pub type ChallengeGamma<F> = ChallengeScalar<F, Gamma>;

#[derive(Clone, Copy, Debug)]
pub struct Y;
pub type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone, Copy, Debug)]
pub struct X;
pub type ChallengeX<F> = ChallengeScalar<F, X>;

#[cfg(test)]
mod tests {
    use halo2curves::pasta::Fp;

    use super::Assigned;
    // We use (numerator, denominator) in the comments below to denote a rational.
    #[test]
    fn add_trivial_to_inv0_rational() {
        // a = 2
        // b = (1,0)
        let a = Assigned::Trivial(Fp::from(2));
        let b = Assigned::Rational(Fp::one(), Fp::zero());

        // 2 + (1,0) = 2 + 0 = 2
        // This fails if addition is implemented using normal rules for rationals.
        assert_eq!((a + b).evaluate(), a.evaluate());
        assert_eq!((b + a).evaluate(), a.evaluate());
    }

    #[test]
    fn add_rational_to_inv0_rational() {
        // a = (1,2)
        // b = (1,0)
        let a = Assigned::Rational(Fp::one(), Fp::from(2));
        let b = Assigned::Rational(Fp::one(), Fp::zero());

        // (1,2) + (1,0) = (1,2) + 0 = (1,2)
        // This fails if addition is implemented using normal rules for rationals.
        assert_eq!((a + b).evaluate(), a.evaluate());
        assert_eq!((b + a).evaluate(), a.evaluate());
    }

    #[test]
    fn sub_trivial_from_inv0_rational() {
        // a = 2
        // b = (1,0)
        let a = Assigned::Trivial(Fp::from(2));
        let b = Assigned::Rational(Fp::one(), Fp::zero());

        // (1,0) - 2 = 0 - 2 = -2
        // This fails if subtraction is implemented using normal rules for rationals.
        assert_eq!((b - a).evaluate(), (-a).evaluate());

        // 2 - (1,0) = 2 - 0 = 2
        assert_eq!((a - b).evaluate(), a.evaluate());
    }

    #[test]
    fn sub_rational_from_inv0_rational() {
        // a = (1,2)
        // b = (1,0)
        let a = Assigned::Rational(Fp::one(), Fp::from(2));
        let b = Assigned::Rational(Fp::one(), Fp::zero());

        // (1,0) - (1,2) = 0 - (1,2) = -(1,2)
        // This fails if subtraction is implemented using normal rules for rationals.
        assert_eq!((b - a).evaluate(), (-a).evaluate());

        // (1,2) - (1,0) = (1,2) - 0 = (1,2)
        assert_eq!((a - b).evaluate(), a.evaluate());
    }

    #[test]
    fn mul_rational_by_inv0_rational() {
        // a = (1,2)
        // b = (1,0)
        let a = Assigned::Rational(Fp::one(), Fp::from(2));
        let b = Assigned::Rational(Fp::one(), Fp::zero());

        // (1,2) * (1,0) = (1,2) * 0 = 0
        assert_eq!((a * b).evaluate(), Fp::zero());

        // (1,0) * (1,2) = 0 * (1,2) = 0
        assert_eq!((b * a).evaluate(), Fp::zero());
    }
}

#[cfg(test)]
mod proptests {
    use std::{
        cmp,
        ops::{Add, Mul, Neg, Sub},
    };

    use group::ff::Field;
    use halo2curves::pasta::Fp;
    use proptest::{collection::vec, prelude::*, sample::select};

    use super::Assigned;

    trait UnaryOperand: Neg<Output = Self> {
        fn double(&self) -> Self;
        fn square(&self) -> Self;
        fn cube(&self) -> Self;
        fn inv0(&self) -> Self;
    }

    impl<F: Field> UnaryOperand for F {
        fn double(&self) -> Self {
            self.double()
        }

        fn square(&self) -> Self {
            self.square()
        }

        fn cube(&self) -> Self {
            self.cube()
        }

        fn inv0(&self) -> Self {
            self.invert().unwrap_or(F::ZERO)
        }
    }

    impl<F: Field> UnaryOperand for Assigned<F> {
        fn double(&self) -> Self {
            self.double()
        }

        fn square(&self) -> Self {
            self.square()
        }

        fn cube(&self) -> Self {
            self.cube()
        }

        fn inv0(&self) -> Self {
            self.invert()
        }
    }

    #[derive(Clone, Debug)]
    enum UnaryOperator {
        Neg,
        Double,
        Square,
        Cube,
        Inv0,
    }

    const UNARY_OPERATORS: &[UnaryOperator] = &[
        UnaryOperator::Neg,
        UnaryOperator::Double,
        UnaryOperator::Square,
        UnaryOperator::Cube,
        UnaryOperator::Inv0,
    ];

    impl UnaryOperator {
        fn apply<F: UnaryOperand>(&self, a: F) -> F {
            match self {
                Self::Neg => -a,
                Self::Double => a.double(),
                Self::Square => a.square(),
                Self::Cube => a.cube(),
                Self::Inv0 => a.inv0(),
            }
        }
    }

    trait BinaryOperand: Sized + Add<Output = Self> + Sub<Output = Self> + Mul<Output = Self> {}
    impl<F: Field> BinaryOperand for F {}
    impl<F: Field> BinaryOperand for Assigned<F> {}

    #[derive(Clone, Debug)]
    enum BinaryOperator {
        Add,
        Sub,
        Mul,
    }

    const BINARY_OPERATORS: &[BinaryOperator] = &[
        BinaryOperator::Add,
        BinaryOperator::Sub,
        BinaryOperator::Mul,
    ];

    impl BinaryOperator {
        fn apply<F: BinaryOperand>(&self, a: F, b: F) -> F {
            match self {
                Self::Add => a + b,
                Self::Sub => a - b,
                Self::Mul => a * b,
            }
        }
    }

    #[derive(Clone, Debug)]
    enum Operator {
        Unary(UnaryOperator),
        Binary(BinaryOperator),
    }

    prop_compose! {
        /// Use narrow that can be easily reduced.
        fn arb_element()(val in any::<u64>()) -> Fp {
            Fp::from(val)
        }
    }

    prop_compose! {
        fn arb_trivial()(element in arb_element()) -> Assigned<Fp> {
            Assigned::Trivial(element)
        }
    }

    prop_compose! {
        /// Generates half of the denominators as zero to represent a deferred inversion.
        fn arb_rational()(
            numerator in arb_element(),
            denominator in prop_oneof![
                1 => Just(Fp::zero()),
                2 => arb_element(),
            ],
        ) -> Assigned<Fp> {
            Assigned::Rational(numerator, denominator)
        }
    }

    prop_compose! {
        fn arb_operators(num_unary: usize, num_binary: usize)(
            unary in vec(select(UNARY_OPERATORS), num_unary),
            binary in vec(select(BINARY_OPERATORS), num_binary),
        ) -> Vec<Operator> {
            unary.into_iter()
                .map(Operator::Unary)
                .chain(binary.into_iter().map(Operator::Binary))
                .collect()
        }
    }

    prop_compose! {
        fn arb_testcase()(
            num_unary in 0usize..5,
            num_binary in 0usize..5,
        )(
            values in vec(
                prop_oneof![
                    1 => Just(Assigned::Zero),
                    2 => arb_trivial(),
                    2 => arb_rational(),
                ],
                // Ensure that:
                // - we have at least one value to apply unary operators to.
                // - we can apply every binary operator pairwise sequentially.
                cmp::max(usize::from(num_unary > 0), num_binary + 1)),
            operations in arb_operators(num_unary, num_binary).prop_shuffle(),
        ) -> (Vec<Assigned<Fp>>, Vec<Operator>) {
            (values, operations)
        }
    }

    proptest! {
        #[test]
        fn operation_commutativity((values, operations) in arb_testcase()) {
            // Evaluate the values at the start.
            let elements: Vec<_> = values.iter().cloned().map(|v| v.evaluate()).collect();

            // Apply the operations to both the deferred and evaluated values.
            fn evaluate<F: UnaryOperand + BinaryOperand>(
                items: Vec<F>,
                operators: &[Operator],
            ) -> F {
                let mut ops = operators.iter();

                // Process all binary operators. We are guaranteed to have exactly as many
                // binary operators as we need calls to the reduction closure.
                let mut res = items.into_iter().reduce(|mut a, b| loop {
                    match ops.next() {
                        Some(Operator::Unary(op)) => a = op.apply(a),
                        Some(Operator::Binary(op)) => break op.apply(a, b),
                        None => unreachable!(),
                    }
                }).unwrap();

                // Process any unary operators that weren't handled in the reduce() call
                // above (either if we only had one item, or there were unary operators
                // after the last binary operator). We are guaranteed to have no binary
                // operators remaining at this point.
                loop {
                    match ops.next() {
                        Some(Operator::Unary(op)) => res = op.apply(res),
                        Some(Operator::Binary(_)) => unreachable!(),
                        None => break res,
                    }
                }
            }
            let deferred_result = evaluate(values, &operations);
            let evaluated_result = evaluate(elements, &operations);

            // The two should be equal, i.e. deferred inversion should commute with the
            // list of operations.
            assert_eq!(deferred_result.evaluate(), evaluated_result);
        }
    }
}
