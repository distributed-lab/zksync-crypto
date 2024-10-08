use crate::bellman::pairing::{Engine, GenericCurveAffine, GenericCurveProjective};

use crate::bellman::pairing::ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, ScalarEngine};

use crate::bellman::SynthesisError;

use crate::bellman::plonk::better_better_cs::cs::{
    ArithmeticTerm, Coefficient, ConstraintSystem, Gate, GateInternal, LinearCombinationOfTerms, MainGate, MainGateTerm, PlonkConstraintSystemParams, PlonkCsWidth4WithNextStepParams,
    PolynomialInConstraint, PolynomialMultiplicativeTerm, TimeDilation, TrivialAssembly, Variable, Width4MainGateWithDNext,
};

use crate::plonk::circuit::hashes_with_tables::utils::{u64_to_ff, IdentifyFirstLast};
use crate::plonk::circuit::Assignment;

use super::super::allocated_num::{AllocatedNum, Num};
use super::super::boolean::{AllocatedBit, Boolean};
use super::super::linear_combination::LinearCombination;
use super::super::simple_term::Term;

use num_bigint::BigUint;
use num_integer::Integer;

use crate::plonk::circuit::bigint_new::*;
use crate::plonk::circuit::curve_new::sw_projective::*;

#[derive(Clone, Debug)]
pub struct AffinePoint<'a, E: Engine, G: GenericCurveAffine>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub x: FieldElement<'a, E, G::Base>,
    pub y: FieldElement<'a, E, G::Base>,
    // the used paradigm is zero abstraction: we won't pay for this flag if it is never used and
    // all our points are regular (i.e. not points at infinity)
    // for this purpose we introduce lazy_select
    // if current point is actually a point at infinity than x, y may contain any values and are actually meaningless
    //pub is_infinity: Boolean,
    pub value: Option<G>,
}

impl<'a, E: Engine, G: GenericCurveAffine> AffinePoint<'a, E, G>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub fn get_x(&self) -> FieldElement<'a, E, G::Base> {
        self.x.clone()
    }

    pub fn get_y(&self) -> FieldElement<'a, E, G::Base> {
        self.y.clone()
    }

    #[track_caller]
    pub fn alloc<CS: ConstraintSystem<E>>(cs: &mut CS, value: Option<G>, params: &'a RnsParameters<E, G::Base>) -> Result<Self, SynthesisError> {
        let (new, _x_decomposition, _y_decomposition) = Self::alloc_ext(cs, value, params)?;
        Ok(new)
    }

    #[track_caller]
    pub fn alloc_ext<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        value: Option<G>,
        params: &'a RnsParameters<E, G::Base>,
    ) -> Result<(Self, RangeCheckDecomposition<E>, RangeCheckDecomposition<E>), SynthesisError> {
        let (x, y) = match value {
            Some(v) => {
                assert!(!v.is_zero());
                let (x, y) = v.into_xy_unchecked();
                (Some(x), Some(y))
            }
            None => (None, None),
        };

        let (x, x_decomposition) = FieldElement::alloc_ext(cs, x, params)?;
        let (y, y_decomposition) = FieldElement::alloc_ext(cs, y, params)?;
        let new = Self { x, y, value };

        Ok((new, x_decomposition, y_decomposition))
    }

    pub unsafe fn from_xy_unchecked(x: FieldElement<'a, E, G::Base>, y: FieldElement<'a, E, G::Base>) -> Self {
        let value = match (x.get_field_value(), y.get_field_value()) {
            (Some(x), Some(y)) => Some(G::from_xy_unchecked(x, y)),
            _ => None,
        };

        let new = Self { x, y, value };
        new
    }

    pub fn constant(value: G, params: &'a RnsParameters<E, G::Base>) -> Self {
        assert!(!value.is_zero());
        let (x, y) = value.into_xy_unchecked();
        let x = FieldElement::constant(x, params);
        let y = FieldElement::constant(y, params);
        let new = Self { x, y, value: Some(value) };

        new
    }

    pub fn get_raw_limbs_representation<CS>(&self, cs: &mut CS) -> Result<Vec<Num<E>>, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let mut res = self.x.get_raw_limbs_representation(cs)?;
        let extension = self.y.get_raw_limbs_representation(cs)?;
        res.extend_from_slice(&extension[..]);
        Ok(res)
    }

    pub fn is_constant(&self) -> bool {
        self.x.is_constant() & self.y.is_constant()
    }

    pub fn get_value(&self) -> Option<G> {
        self.value
    }

    pub fn normalize_coordinates<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.x.normalize(cs)?;
        self.y.normalize(cs)
    }

    pub fn enforce_if_normalized<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        self.x.enforce_if_normalized(cs)?;
        self.y.enforce_if_normalized(cs)
    }

    pub fn enforce_equal<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        FieldElement::enforce_equal(cs, &mut this.x, &mut other.x)?;
        FieldElement::enforce_equal(cs, &mut this.y, &mut other.y)
    }

    pub fn equals<CS>(cs: &mut CS, this: &mut Self, other: &mut Self) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let x_check = FieldElement::equals(cs, &mut this.x, &mut other.x)?;
        let y_check = FieldElement::equals(cs, &mut this.y, &mut other.y)?;
        let equals = Boolean::and(cs, &x_check, &y_check)?;

        Ok(equals)
    }

    pub fn negate<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        let y_negated = self.y.negate(cs)?;
        let new_value = self.value.map(|x| {
            let mut tmp = x;
            tmp.negate();
            tmp
        });
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            value: new_value,
        };

        Ok(new)
    }

    pub fn conditionally_negate<CS>(&self, cs: &mut CS, flag: &Boolean) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let y_negated = self.y.conditionally_negate(cs, flag)?;
        let new_value = self.value.map(|x| {
            let mut tmp = x;
            tmp.negate();
            tmp
        });
        let new = Self {
            x: self.x.clone(),
            y: y_negated,
            value: new_value,
        };

        Ok(new)
    }

    pub fn select<CS>(cs: &mut CS, flag: &Boolean, first: &Self, second: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let first_value = first.get_value();
        let second_value = second.get_value();
        let x = FieldElement::conditionally_select(cs, flag, &first.x, &second.x)?;
        let y = FieldElement::conditionally_select(cs, flag, &first.y, &second.y)?;

        let value = match (flag.get_value(), first_value, second_value) {
            (Some(true), Some(p), _) => Some(p),
            (Some(false), _, Some(p)) => Some(p),
            (_, _, _) => None,
        };
        let selected = AffinePoint { x, y, value };

        Ok(selected)
    }

    #[track_caller]
    pub fn is_on_curve_for_zero_a<CS: ConstraintSystem<E>>(&self, cs: &mut CS, curve_b: G::Base) -> Result<Boolean, SynthesisError> {
        let params = &self.x.representation_params;
        assert_eq!(curve_b, G::b_coeff());
        let b = FieldElement::constant(curve_b, params);

        let mut lhs = self.y.square(cs)?;
        let x_squared = self.x.square(cs)?;
        let x_cubed = x_squared.mul(cs, &self.x)?;
        let mut rhs = x_cubed.add(cs, &b)?;

        FieldElement::equals(cs, &mut lhs, &mut rhs)
    }

    #[track_caller]
    pub fn add_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // only enforce that x != x'
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.add_unequal_unchecked(cs, other)
    }

    #[track_caller]
    pub fn add_unequal_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal with value {}", first);
            }
            _ => {}
        }
        // since we are in a circuit we don't use projective coodinates: inversions are "cheap" in terms of constraints
        // we also do not want to have branching here, so this function implicitly requires that points are not equal
        // we need to calculate lambda = (y' - y)/(x' - x). We don't care about a particular
        // value of y' - y, so we don't add them explicitly and just use in inversion witness
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&other.y).add_neg_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * (x - new_x) + (- y)
        let this_x_minus_new_x = self.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &this_x_minus_new_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.add_assign_mixed(&other);
                Some(tmp.into_affine())
            }
            _ => None,
        };

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok(new)
    }

    #[track_caller]
    pub fn sub_unequal<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // only enforce that x != x'
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.sub_unequal_unchecked(cs, other)
    }

    #[track_caller]
    pub fn sub_unequal_unchecked<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        match (self.get_value(), other.get_value()) {
            (Some(first), Some(second)) => {
                assert!(first != second, "points are actually equal with value {}", first);
            }
            _ => {}
        }

        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&other.y).add_pos_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.x).add_neg_term(&other.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        // lambda * -(x - new_x) + (- y)
        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &new_x_minus_this_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                let mut t0 = other;
                t0.negate();
                tmp.add_assign_mixed(&t0);

                Some(tmp.into_affine())
            }
            _ => None,
        };

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok(new)
    }

    #[track_caller]
    pub fn double<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<Self, SynthesisError> {
        // this formula is only valid for curve with zero j-ivariant
        assert!(G::a_coeff().is_zero());

        let x_squared = self.x.square(cs)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&x_squared).add_pos_term(&x_squared).add_pos_term(&x_squared);
        let two_y = self.y.double(cs)?;
        let lambda = FieldElement::div_with_chain(cs, chain, &two_y)?;

        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        let x_minus_new_x = self.x.sub(cs, &new_x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &lambda, &x_minus_new_x, chain)?;

        let new_value = self.get_value().map(|this| {
            let mut tmp = this.into_projective();
            tmp.double();
            tmp.into_affine()
        });

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok(new)
    }

    // doubles self and adds other
    #[track_caller]
    pub fn double_and_add<CS>(&mut self, cs: &mut CS, other: &mut Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        // even though https://www.researchgate.net/publication/283556724_New_Fast_Algorithms_for_Elliptic_Curve_Arithmetic_in_Affine_Coordinates exists
        // inversions are cheap, so Montgomery ladder is better
        // we can also try https://eprint.iacr.org/2015/1060.pdf
        // only check that x - x' != 0 and go into the unchecked routine
        FieldElement::enforce_not_equal(cs, &mut self.x, &mut other.x)?;
        self.double_and_add_unchecked(cs, &other)
    }

    #[track_caller]
    pub fn double_and_add_unchecked<CS>(&self, cs: &mut CS, other: &Self) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<E>,
    {
        let other_x_minus_this_x = other.x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_pos_term(&other.y).add_neg_term(&self.y);
        let lambda = FieldElement::div_with_chain(cs, chain, &other_x_minus_this_x)?;

        // lambda^2 + (-x' - x)
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&other.x).add_neg_term(&self.x);
        let new_x = lambda.square_with_chain(cs, chain)?;

        let new_x_minus_this_x = new_x.sub(cs, &self.x)?;
        let two_y = self.y.double(cs)?;
        let t0 = two_y.div(cs, &new_x_minus_this_x)?;
        let t1 = lambda.add(cs, &t0)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.x).add_neg_term(&new_x);
        let new_x = t1.square_with_chain(cs, chain)?;

        let new_x_minus_x = new_x.sub(cs, &self.x)?;
        let mut chain = FieldElementsChain::new();
        chain.add_neg_term(&self.y);
        let new_y = FieldElement::mul_with_chain(cs, &t1, &new_x_minus_x, chain)?;

        let new_value = match (self.value, other.value) {
            (Some(this), Some(other)) => {
                assert!(this != other);
                let mut tmp = this.into_projective();
                tmp.double();
                tmp.add_assign_mixed(&other);

                Some(tmp.into_affine())
            }
            _ => None,
        };

        let new = Self { x: new_x, y: new_y, value: new_value };
        Ok(new)
    }
}

// we are particularly interested in three curves: secp256k1, bn256 and bls12-281
// unfortunately, only bls12-381 has a cofactor
impl<'a, E: Engine, G: GenericCurveAffine + rand::Rand> AffinePoint<'a, E, G>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    #[track_caller]
    pub fn mul_by_scalar_for_composite_order_curve<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>) -> Result<Self, SynthesisError> {
        if let Some(value) = scalar.get_field_value() {
            assert!(!value.is_zero(), "can not multiply by zero in the current approach");
        }
        if scalar.is_constant() {
            unimplemented!();
        }

        let params = self.x.representation_params;
        let entries = scalar.decompose_into_skewed_representation(cs)?;

        // we add a random point to the accumulator to avoid having zero anywhere (with high probability)
        // and unknown discrete log allows us to be "safe"
        let offset_generator = crate::constants::make_random_points_with_unknown_discrete_log::<G>(&crate::constants::MULTIEXP_DST[..], 1)[0];
        let mut generator = Self::constant(offset_generator, params);
        let mut acc = self.add_unequal(cs, &mut generator)?;

        let entries_without_first_and_last = &entries[1..(entries.len() - 1)];
        let mut num_doubles = 0;

        let mut x = self.x.clone();
        let mut minus_y = self.y.negate(cs)?;
        minus_y.reduce_loose(cs)?;

        for e in entries_without_first_and_last.iter() {
            let selected_y = FieldElement::conditionally_select(cs, e, &minus_y, &self.y)?;
            let t_value = match (self.value, e.get_value()) {
                (Some(val), Some(bit)) => {
                    let mut val = val;
                    if bit {
                        val.negate();
                    }
                    Some(val)
                }
                _ => None,
            };
            let mut t = Self { x: x, y: selected_y, value: t_value };

            acc = acc.double_and_add(cs, &mut t)?;
            num_doubles += 1;
            x = t.x;
        }

        let with_skew = acc.sub_unequal(cs, &mut self.clone())?;
        let last_entry = entries.last().unwrap();

        let with_skew_value = with_skew.get_value();
        let with_skew_x = with_skew.x;
        let with_skew_y = with_skew.y;

        let acc_value = acc.get_value();
        let acc_x = acc.x;
        let acc_y = acc.y;

        let final_value = match (with_skew_value, acc_value, last_entry.get_value()) {
            (Some(s_value), Some(a_value), Some(b)) => {
                if b {
                    Some(s_value)
                } else {
                    Some(a_value)
                }
            }
            _ => None,
        };

        let final_acc_x = FieldElement::conditionally_select(cs, last_entry, &with_skew_x, &acc_x)?;
        let final_acc_y = FieldElement::conditionally_select(cs, last_entry, &with_skew_y, &acc_y)?;

        let mut scaled_offset = offset_generator.into_projective();
        for _ in 0..num_doubles {
            scaled_offset.double();
        }
        let mut offset = Self::constant(scaled_offset.into_affine(), params);

        let mut result = Self {
            x: final_acc_x,
            y: final_acc_y,
            value: final_value,
        };
        let result = result.sub_unequal(cs, &mut offset)?;

        Ok(result)
    }
}

impl<'a, E: Engine, G: GenericCurveAffine> AffinePoint<'a, E, G>
where
    <G as GenericCurveAffine>::Base: PrimeField,
{
    pub fn mul_by_scalar_for_prime_order_curve<CS: ConstraintSystem<E>>(&mut self, cs: &mut CS, scalar: &mut FieldElement<'a, E, G::Scalar>) -> Result<ProjectivePoint<'a, E, G>, SynthesisError> {
        let params = self.x.representation_params;
        let scalar_decomposition = scalar.decompose_into_binary_representation(cs)?;

        // TODO: use standard double-add algorithm for now, optimize later
        let mut acc = ProjectivePoint::<E, G>::zero(params);
        let mut tmp = self.clone();

        for bit in scalar_decomposition.into_iter() {
            let added = acc.add_mixed(cs, &mut tmp)?;
            acc = ProjectivePoint::conditionally_select(cs, &bit, &added, &acc)?;
            tmp = tmp.double(cs)?;
        }

        Ok(acc)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bellman::pairing::bn256::{Bn256, Fq, Fr, G1Affine};
    use bellman::plonk::better_better_cs::cs::*;
    use bellman::plonk::better_better_cs::gates::{self, selector_optimized_with_d_next::SelectorOptimizedWidth4MainGateWithDNext};
    use plonk::circuit::Width4WithCustomGates;
    use rand::{Rng, SeedableRng, XorShiftRng};

    #[test]
    fn test_arithmetic_for_bn256_curve() {
        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bn256, Fq>::new_optimal(&mut cs, 80usize);
        let scalar_params = RnsParameters::<Bn256, Fr>::new_optimal(&mut cs, 80usize);
        let mut rng = rand::thread_rng();

        let a: G1Affine = rng.gen();
        let scalar: Fr = rng.gen();
        let mut tmp = a.into_projective();
        tmp.mul_assign(scalar);
        let result = tmp.into_affine();

        let mut a = AffinePoint::alloc(&mut cs, Some(a), &params).unwrap();
        let mut scalar = FieldElement::alloc(&mut cs, Some(scalar), &scalar_params).unwrap();
        let mut actual_result = AffinePoint::alloc(&mut cs, Some(result), &params).unwrap();
        let naive_mul_start = cs.get_current_step_number();
        let mut result = a.mul_by_scalar_for_prime_order_curve(&mut cs, &mut scalar).unwrap();
        let mut result = unsafe { result.convert_to_affine(&mut cs).unwrap() };
        let naive_mul_end = cs.get_current_step_number();
        println!("num of gates: {}", naive_mul_end - naive_mul_start);

        // println!("actual result: x: {}, y: {}", actual_result.x.get_field_value().unwrap(), actual_result.y.get_field_value().unwrap());
        // println!("computed result: x: {}, y: {}", result.x.get_field_value().unwrap(), result.y.get_field_value().unwrap());

        AffinePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
        assert!(cs.is_satisfied());
        println!("SCALAR MULTIPLICATION final");
    }

    #[test]
    fn test_arithmetic_for_secp256k1_curve() {
        use super::super::secp256k1::fq::Fq as SecpFq;
        use super::super::secp256k1::fr::Fr as SecpFr;
        use super::super::secp256k1::PointAffine as SecpG1;

        let mut cs = TrivialAssembly::<Bn256, Width4WithCustomGates, SelectorOptimizedWidth4MainGateWithDNext>::new();
        inscribe_default_bitop_range_table(&mut cs).unwrap();
        let params = RnsParameters::<Bn256, SecpFq>::new_optimal(&mut cs, 64usize);
        let scalar_params = RnsParameters::<Bn256, SecpFr>::new_optimal(&mut cs, 80usize);
        let mut rng = rand::thread_rng();

        let a: SecpG1 = rng.gen();
        let scalar: SecpFr = rng.gen();
        let mut tmp = a.into_projective();
        tmp.mul_assign(scalar);
        let result = tmp.into_affine();

        let mut a = AffinePoint::alloc(&mut cs, Some(a), &params).unwrap();
        let mut scalar = FieldElement::alloc(&mut cs, Some(scalar), &scalar_params).unwrap();
        let mut actual_result = AffinePoint::alloc(&mut cs, Some(result), &params).unwrap();
        let naive_mul_start = cs.get_current_step_number();
        let mut result = a.mul_by_scalar_for_prime_order_curve(&mut cs, &mut scalar).unwrap();
        let mut result = unsafe { result.convert_to_affine(&mut cs).unwrap() };
        let naive_mul_end = cs.get_current_step_number();
        println!("num of gates: {}", naive_mul_end - naive_mul_start);

        // println!("actual result: x: {}, y: {}", actual_result.x.get_field_value().unwrap(), actual_result.y.get_field_value().unwrap());
        // println!("computed result: x: {}, y: {}", result.x.get_field_value().unwrap(), result.y.get_field_value().unwrap());

        AffinePoint::enforce_equal(&mut cs, &mut result, &mut actual_result).unwrap();
        assert!(cs.is_satisfied());
        println!("SCALAR MULTIPLICATION final");
    }
}
