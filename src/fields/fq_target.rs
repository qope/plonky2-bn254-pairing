use ark_bn254::Fq;
use itertools::Itertools;
use num::Zero;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use std::marker::PhantomData;

use crate::fields::bn254base::Bn254Base;

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

    pub fn add_many(builder: &mut CircuitBuilder<F, D>, to_add: &[Self]) -> Self {
        let target =
            builder.add_many_nonnative(&to_add.iter().map(|x| x.target.clone()).collect_vec());
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn mul_many(builder: &mut CircuitBuilder<F, D>, to_add: &[Self]) -> Self {
        let target =
            builder.mul_many_nonnative(&to_add.iter().map(|x| x.target.clone()).collect_vec());
        Self {
            target,
            _marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fq;
    use ark_std::UniformRand;
    use ark_std::Zero;

    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
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
}
