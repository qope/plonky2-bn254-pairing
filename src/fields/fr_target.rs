use ark_bn254::Fr;
use itertools::Itertools;
use num::Zero;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::target::BoolTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::nonnative::{CircuitBuilderNonNative, NonNativeTarget};
use plonky2_u32::gadgets::arithmetic_u32::U32Target;
use std::marker::PhantomData;

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
