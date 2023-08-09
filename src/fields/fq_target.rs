use ark_bn254::Fq;
use itertools::Itertools;
use num::{One, Zero};
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartialWitness, PartitionWitness, Witness},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::{
    biguint::{BigUintTarget, GeneratedValuesBigUint, WitnessBigUint},
    nonnative::{CircuitBuilderNonNative, NonNativeTarget},
};
use plonky2_u32::{
    gadgets::{arithmetic_u32::U32Target, range_check::range_check_u32_circuit},
    witness::WitnessU32,
};
use std::marker::PhantomData;

use crate::{
    fields::{
        bn254base::Bn254Base,
        native::{from_biguint_to_fq, sgn0_fq},
    },
    pairing::final_exp_native::get_naf,
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

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

    pub fn from_targets(builder: &mut CircuitBuilder<F, D>, targets: &[Target]) -> Self {
        let num_limbs = CircuitBuilder::<F, D>::num_nonnative_limbs::<Bn254Base>();
        assert_eq!(targets.len(), num_limbs);
        let limbs = targets.iter().cloned().map(|a| U32Target(a)).collect_vec();
        let biguint = BigUintTarget { limbs };
        let target = builder.reduce(&biguint);
        Self {
            target,
            _marker: PhantomData,
        }
    }

    pub fn limbs(&self) -> Vec<U32Target> {
        self.target.value.limbs.iter().cloned().collect_vec()
    }

    pub fn num_max_limbs() -> usize {
        CircuitBuilder::<F, D>::num_nonnative_limbs::<Bn254Base>()
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

    // if self is not square, this fails
    // the return value is ensured to be sgn0(x) = sgn0(sgn)
    pub fn sqrt_with_sgn(&self, builder: &mut CircuitBuilder<F, D>, sgn: BoolTarget) -> Self {
        let sqrt = Self::new(builder);
        builder.add_simple_generator(FqSqrtGenerator::<F, D> {
            x: self.clone(),
            sgn: sgn.clone(),
            sqrt: sqrt.clone(),
        });

        // sqrt^2 = x
        let sqrt_sq = sqrt.mul(builder, &sqrt);
        Self::connect(builder, &sqrt_sq, self);

        // sgn0(sqrt) = sgn0(sgn)
        let sgn0_sqrt = sqrt.sgn0(builder);
        builder.connect(sgn0_sqrt.target, sgn.target);

        sqrt
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

impl<F: RichField + Extendable<D>, const D: usize> RecursiveCircuitTarget<F, D, FqTarget<F, D>, Fq>
    for FqTarget<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        self.limbs().iter().cloned().map(|x| x.0).collect()
    }

    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        let num_limbs = CircuitBuilder::<F, D>::num_nonnative_limbs::<Bn254Base>();
        assert_eq!(input.len(), num_limbs);
        let limbs = input.iter().cloned().map(|a| U32Target(a)).collect_vec();
        range_check_u32_circuit(builder, limbs.clone());
        let biguint = BigUintTarget { limbs };
        let target = builder.biguint_to_nonnative::<Bn254Base>(&biguint);
        FqTarget {
            target,
            _marker: PhantomData,
        }
    }

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq) {
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

#[derive(Debug)]
struct FqSqrtGenerator<F: RichField + Extendable<D>, const D: usize> {
    x: FqTarget<F, D>,
    sgn: BoolTarget,
    sqrt: FqTarget<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F> for FqSqrtGenerator<F, D> {
    fn dependencies(&self) -> Vec<Target> {
        let mut x_vec = self.x.target.value.limbs.iter().map(|&l| l.0).collect_vec();
        x_vec.push(self.sgn.target);
        x_vec
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        use ark_ff::Field as ArkField;
        let x = from_biguint_to_fq(witness.get_biguint_target(self.x.target.value.clone()));
        let sgn_val = witness.get_target(self.sgn.target);
        let mut sqrt_x: Fq = x.sqrt().unwrap();
        let desired_sgn = sgn_val.to_canonical_u64() % 2 == 1;
        let sng0_x = sgn0_fq(sqrt_x);
        if sng0_x != desired_sgn {
            sqrt_x = -sqrt_x;
        }
        assert_eq!(sgn0_fq(sqrt_x), desired_sgn);
        let sqrt_x_biguint: BigUint = sqrt_x.into();
        out_buffer.set_biguint_target(&self.sqrt.target.value, &sqrt_x_biguint);
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
    use rand::Rng;

    use crate::fields::native::sgn0_fq;
    use crate::traits::recursive_circuit_target::RecursiveCircuitTarget;

    use super::FqTarget;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_from_to_vec() {
        let rng = &mut rand::thread_rng();
        let a = Fq::rand(rng);
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = FqTarget::constant(&mut builder, a);

        let a_vec = a_t.to_vec();
        let restored_a_t = FqTarget::from_vec(&mut builder, &a_vec);

        FqTarget::connect(&mut builder, &a_t, &restored_a_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

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

    #[test]
    fn test_sqrt_with_sgn() {
        let rng = &mut rand::thread_rng();
        let a: Fq = {
            // resample a until it is a square
            let mut a = Fq::rand(rng);
            while !a.legendre().is_qr() {
                a = Fq::rand(rng);
            }
            a
        };
        assert!(a.legendre().is_qr());
        let sgn: bool = rng.gen();
        let sqrt = a.sqrt().unwrap();
        let expected_sqrt = if sgn == sgn0_fq(sqrt) { sqrt } else { -sqrt };
        assert_eq!(expected_sqrt * expected_sqrt, a);
        assert_eq!(sgn0_fq(expected_sqrt), sgn);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = FqTarget::constant(&mut builder, a);
        let sgn_t = builder.constant_bool(sgn);
        let sqrt_t = a_t.sqrt_with_sgn(&mut builder, sgn_t);
        let expected_sqrt_t = FqTarget::constant(&mut builder, expected_sqrt);

        FqTarget::connect(&mut builder, &sqrt_t, &expected_sqrt_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }
}
