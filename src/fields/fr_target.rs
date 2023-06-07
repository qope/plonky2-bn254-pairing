use ark_bn254::Fr;
use itertools::Itertools;
use num::Zero;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::PartialWitness,
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::{
    biguint::BigUintTarget,
    nonnative::{CircuitBuilderNonNative, NonNativeTarget},
};
use plonky2_u32::{
    gadgets::{arithmetic_u32::U32Target, range_check::range_check_u32_circuit},
    witness::WitnessU32,
};
use std::marker::PhantomData;

use crate::traits::recursive_circuit_target::RecursiveCircuitTarget;

use super::bn254scalar::Bn254Scalar;

#[derive(Clone, Debug)]
pub struct FrTarget<F: RichField + Extendable<D>, const D: usize> {
    pub(crate) target: NonNativeTarget<Bn254Scalar>,
    _marker: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> FrTarget<F, D> {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let target = builder.add_virtual_nonnative_target();
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn target(&self) -> NonNativeTarget<Bn254Scalar> {
        self.target.clone()
    }

    pub fn limbs(&self) -> Vec<U32Target> {
        self.target.value.limbs.iter().cloned().collect_vec()
    }

    pub fn num_max_limbs() -> usize {
        CircuitBuilder::<F, D>::num_nonnative_limbs::<Bn254Scalar>()
    }

    pub fn to_bits(&self, builder: &mut CircuitBuilder<F, D>) -> Vec<BoolTarget> {
        builder.split_nonnative_to_bits(&self.target)
    }

    pub fn construct(value: NonNativeTarget<Bn254Scalar>) -> Self {
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

    pub fn constant(builder: &mut CircuitBuilder<F, D>, c: Fr) -> Self {
        let target = builder.constant_nonnative(c.into());
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn from_bool(builder: &mut CircuitBuilder<F, D>, b: &BoolTarget) -> Self {
        let target = builder.bool_to_nonnative::<Bn254Scalar>(&b);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn zero(builder: &mut CircuitBuilder<F, D>) -> Self {
        Self::constant(builder, Fr::zero())
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

    pub fn mul_const(&self, builder: &mut CircuitBuilder<F, D>, c: &Fr) -> Self {
        let c = FrTarget::constant(builder, *c);
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
}

impl<F: RichField + Extendable<D>, const D: usize> RecursiveCircuitTarget<F, D, FrTarget<F, D>, Fr>
    for FrTarget<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        self.limbs().iter().cloned().map(|x| x.0).collect()
    }

    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        let num_limbs = Self::num_max_limbs();
        assert_eq!(input.len(), num_limbs);
        let limbs = input.iter().cloned().map(|a| U32Target(a)).collect_vec();
        range_check_u32_circuit(builder, limbs.clone());
        let biguint = BigUintTarget { limbs };
        let target = builder.biguint_to_nonnative::<Bn254Scalar>(&biguint);
        FrTarget {
            target,
            _marker: PhantomData,
        }
    }

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fr) {
        let value_b: BigUint = value.clone().into();
        let mut limbs = value_b.to_u32_digits();

        // padding
        let num_lims = Self::num_max_limbs();
        let to_padd = num_lims - limbs.len();
        limbs.extend(vec![0; to_padd]);

        self.limbs()
            .iter()
            .cloned()
            .zip(limbs)
            .map(|(l_t, l)| pw.set_u32_target(l_t, l))
            .for_each(drop);
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use num_traits::*;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::FrTarget;

    type F = GoldilocksField;
    const D: usize = 2;

    #[test]
    fn test_fr_bit_decompose() {
        let x = Fr::one();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config.clone());
        let x_t = FrTarget::constant(&mut builder, x);
        let bits = x_t.to_bits(&mut builder);
        dbg!(bits.len());
    }
}
