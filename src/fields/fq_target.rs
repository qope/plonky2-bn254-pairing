use ark_bn254::Fq;
use itertools::Itertools;
use num::{One, Zero};
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use std::marker::PhantomData;

use crate::{fields::bn254base::Bn254Base, pairing::final_exp_native::get_naf};

#[derive(Clone, Debug)]
pub struct FqTarget<F: RichField + Extendable<D>, const D: usize> {
    pub(crate) target: NonNativeTarget<Bn254Base>,
    _marker: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> FqTarget<F, D> {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let target = builder.add_virtual_nonnative_target();
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn target(&self) -> NonNativeTarget<Bn254Base> {
        self.target.clone()
    }

    pub fn limbs(&self) -> Vec<U32Target> {
        self.target.value.limbs.iter().cloned().collect_vec()
    }

    pub fn construct(value: NonNativeTarget<Bn254Base>) -> Self {
        Self {
            target: value,
            _marker: PhantomData,
        }
    }

    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        builder.connect_nonnative(&lhs.target, &rhs.target);
    }

    pub fn select(
        builder: &mut CircuitBuilder<F, D>,
        a: &Self,
        b: &Self,
        flag: &BoolTarget,
    ) -> Self {
        let s = builder.if_nonnative(flag.clone(), &a.target, &b.target);
        Self {
            target: s,
            _marker: PhantomData,
        }
    }

    pub fn is_equal(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> BoolTarget {
        let a_limbs = self.target.value.limbs.iter().map(|x| x.0).collect_vec();
        let b_limbs = rhs.target.value.limbs.iter().map(|x| x.0).collect_vec();
        assert_eq!(a_limbs.len(), b_limbs.len());

        let terms = a_limbs
            .iter()
            .zip(b_limbs)
            .map(|(&a, b)| builder.is_equal(a, b).target)
            .collect_vec();
        let is_equal = builder.mul_many(terms);

        // is_equal is ensured to be 0 or 1, so we can safely convert it to bool.
        BoolTarget::new_unsafe(is_equal)
    }

    pub fn is_zero(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let zero = Self::zero(builder);
        self.is_equal(builder, &zero)
    }

    pub fn constant(builder: &mut CircuitBuilder<F, D>, c: Fq) -> Self {
        let target = builder.constant_nonnative(c.into());
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn from_bool(builder: &mut CircuitBuilder<F, D>, b: &BoolTarget) -> Self {
        let target = builder.bool_to_nonnative::<Bn254Base>(&b);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn zero(builder: &mut CircuitBuilder<F, D>) -> Self {
        Self::constant(builder, Fq::zero())
    }

    pub fn add(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let target = builder.add_nonnative(&self.target, &rhs.target);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn neg(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let target = builder.neg_nonnative(&self.target);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn sub(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let target = builder.sub_nonnative(&self.target, &rhs.target);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn mul(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let target = builder.mul_nonnative(&self.target, &rhs.target);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn mul_const(&self, builder: &mut CircuitBuilder<F, D>, c: &Fq) -> Self {
        let c = FqTarget::constant(builder, *c);
        self.mul(builder, &c)
    }

    pub fn inv(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let target = builder.inv_nonnative(&self.target);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn div(&self, builder: &mut CircuitBuilder<F, D>, other: &Self) -> Self {
        let inv = other.inv(builder);
        self.mul(builder, &inv)
    }

    // returns self % 2 == 1
    pub fn sgn0(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let first_digit = self.target.value.limbs[0].0;
        let bits = builder.split_le(first_digit, 32);
        bits[0]
    }

    // TODO! have to consider self = zero case
    pub fn pow(&self, builder: &mut CircuitBuilder<F, D>, exp: Vec<u64>) -> Self {
        let a = self.clone();
        let mut res = self.clone();
        let mut is_started = false;
        let naf = get_naf(exp);

        for &z in naf.iter().rev() {
            if is_started {
                res = res.mul(builder, &res);
            }

            if z != 0 {
                assert!(z == 1 || z == -1);
                if is_started {
                    res = if z == 1 {
                        res.mul(builder, &a)
                    } else {
                        res.div(builder, &a)
                    };
                } else {
                    assert_eq!(z, 1);
                    is_started = true;
                }
            }
        }
        res
    }

    pub fn legendre(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let k: BigUint = (Fq::from(-1) / Fq::from(2)).into();
        self.pow(builder, k.to_u64_digits())
    }

    pub fn is_square(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let legendre = self.legendre(builder);
        let one = FqTarget::constant(builder, Fq::one());
        legendre.is_equal(builder, &one)
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fq;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use ark_std::Zero;

    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field as Plonky2Field},
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::FqTarget;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_fq_mul_circuit() {
        let rng = &mut rand::thread_rng();
        let a = Fq::rand(rng);
        let b = Fq::rand(rng);
        let c_expected = a * b;

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = FqTarget::constant(&mut builder, a);
        let b_t = FqTarget::constant(&mut builder, b);
        let c_t = a_t.mul(&mut builder, &b_t);
        let c_expected_t = FqTarget::constant(&mut builder, c_expected);

        FqTarget::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_select_and_is_equal() {
        let rng = &mut rand::thread_rng();
        let a = Fq::rand(rng);
        let b = Fq::rand(rng);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = FqTarget::constant(&mut builder, a);
        let b_t = FqTarget::constant(&mut builder, b);

        let flag = builder.constant_bool(true);

        let a_expected = FqTarget::select(&mut builder, &a_t, &b_t, &flag);

        let is_a_eq = a_expected.is_equal(&mut builder, &a_t);
        let is_b_eq = a_expected.is_equal(&mut builder, &b_t);

        let mut pw = PartialWitness::new();
        pw.set_target(is_a_eq.target, F::ONE);
        pw.set_target(is_b_eq.target, F::ZERO);
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_is_zero() {
        let zero = Fq::zero();
        let non_zero = Fq::rand(&mut rand::thread_rng());
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let zero_t = FqTarget::constant(&mut builder, zero);
        let is_zero = zero_t.is_zero(&mut builder);
        let non_zero_t = FqTarget::constant(&mut builder, non_zero);
        let is_zero_non_zero = non_zero_t.is_zero(&mut builder);

        let not_is_zero_non_zero = builder.not(is_zero_non_zero);
        builder.connect(not_is_zero_non_zero.target, is_zero.target);

        let mut pw = PartialWitness::new();
        pw.set_target(is_zero.target, F::ONE);
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_sign0() {
        let a = Fq::from(5);
        let b = Fq::from(6);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a_t = FqTarget::constant(&mut builder, a);
        let b_t = FqTarget::constant(&mut builder, b);

        let a_sign0 = a_t.sgn0(&mut builder);
        let b_sign0 = b_t.sgn0(&mut builder);

        let mut pw = PartialWitness::new();
        pw.set_target(a_sign0.target, F::ONE);
        pw.set_target(b_sign0.target, F::ZERO);
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_is_square() {
        let rng = &mut rand::thread_rng();
        let a = Fq::rand(rng);
        let a_is_sq_expected: bool = a.legendre().is_qr();
        dbg!(a_is_sq_expected);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a_t = FqTarget::constant(&mut builder, a);
        let a_is_sq = a_t.is_square(&mut builder);
        let a_is_sq_expected_t = builder.constant_bool(a_is_sq_expected);

        builder.connect(a_is_sq.target, a_is_sq_expected_t.target);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
        dbg!(data.common.degree_bits());
    }
}
