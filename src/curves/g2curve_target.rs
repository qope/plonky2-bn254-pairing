use ark_bn254::G2Affine;
use ark_std::UniformRand;
use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::PartialWitness,
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::nonnative::CircuitBuilderNonNative;
use rand::SeedableRng;

use crate::{
    fields::{fq2_target::Fq2Target, fq_target::FqTarget, fr_target::FrTarget},
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

#[derive(Clone, Debug)]
pub struct G2Target<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq2Target<F, D>,
    pub y: Fq2Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> G2Target<F, D> {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let x = Fq2Target::new(builder);
        let y = Fq2Target::new(builder);
        G2Target { x, y }
    }

    pub fn construct(x: Fq2Target<F, D>, y: Fq2Target<F, D>) -> Self {
        G2Target { x, y }
    }

    pub fn constant(builder: &mut CircuitBuilder<F, D>, a: G2Affine) -> Self {
        let x = a.x;
        let y = a.y;

        let x_target = Fq2Target::constant(builder, x);
        let y_target = Fq2Target::constant(builder, y);

        G2Target {
            x: x_target,
            y: y_target,
        }
    }

    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        Fq2Target::connect(builder, &lhs.x, &rhs.x);
        Fq2Target::connect(builder, &lhs.y, &rhs.y);
    }

    pub fn neg(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let x = self.x.clone();
        let y = self.y.neg(builder);
        G2Target { x, y }
    }

    pub fn double(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let x = self.x.clone();
        let y = self.y.clone();
        let double_y = y.add(builder, &y);
        let inv_double_y = double_y.inv(builder);
        let x_squared = x.mul(builder, &x);
        let double_x_squared = x_squared.add(builder, &x_squared);
        let triple_x_squared = double_x_squared.add(builder, &x_squared);
        let triple_xx_a = triple_x_squared.clone();
        let lambda = triple_xx_a.mul(builder, &inv_double_y);
        let lambda_squared = lambda.mul(builder, &lambda);
        let x_double = x.add(builder, &x);
        let x3 = lambda_squared.sub(builder, &x_double);
        let x_diff = x.sub(builder, &x3);
        let lambda_x_diff = lambda.mul(builder, &x_diff);
        let y3 = lambda_x_diff.sub(builder, &y);

        G2Target { x: x3, y: y3 }
    }

    pub fn add(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let x1 = self.x.clone();
        let y1 = self.y.clone();
        let x2 = rhs.x.clone();
        let y2 = rhs.y.clone();

        let u = y2.sub(builder, &y1);
        let v = x2.sub(builder, &x1);
        let v_inv = v.inv(builder);
        let s = u.mul(builder, &v_inv);
        let s_squared = s.mul(builder, &s);
        let x_sum = x2.add(builder, &x1);
        let x3 = s_squared.sub(builder, &x_sum);
        let x_diff = x1.sub(builder, &x3);
        let prod = s.mul(builder, &x_diff);
        let y3 = prod.sub(builder, &y1);

        G2Target { x: x3, y: y3 }
    }

    pub fn conditional_add(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        p: &Self,
        b: &BoolTarget,
    ) -> Self {
        let sum = self.add(builder, p);

        let x = Fq2Target::select(builder, &sum.x, &self.x, b);
        let y = Fq2Target::select(builder, &sum.y, &self.y, b);

        Self { x, y }
    }

    pub fn pow_var_simple(&self, builder: &mut CircuitBuilder<F, D>, s: &FrTarget<F, D>) -> Self {
        let bits = builder.split_nonnative_to_bits(&s.target);

        let mut doubles = vec![];
        let mut v = self.clone();
        doubles.push(v.clone());
        for _ in 1..bits.len() {
            v = v.double(builder);
            doubles.push(v.clone());
        }

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let rando = G2Affine::rand(&mut rng);
        let rando_t = G2Target::constant(builder, rando);
        let neg_rando = G2Target::constant(builder, -rando);
        let mut r = rando_t;

        for i in 0..bits.len() {
            r = r.conditional_add(builder, &doubles[i], &bits[i]);
        }

        r = r.add(builder, &neg_rando);

        r
    }
}

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, G2Target<F, D>, G2Affine> for G2Target<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        self.x.to_vec().into_iter().chain(self.y.to_vec()).collect()
    }

    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        let num_lims = FqTarget::<F, D>::num_max_limbs();
        let num_fq2_lims = 2 * num_lims;
        assert_eq!(input.len(), num_fq2_lims * 2);
        let mut input = input.to_vec();
        let x_raw = input.drain(0..num_fq2_lims).collect_vec();
        let y_raw = input;
        Self {
            x: Fq2Target::from_vec(builder, &x_raw),
            y: Fq2Target::from_vec(builder, &y_raw),
        }
    }

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &G2Affine) {
        self.x.set_witness(pw, &value.x);
        self.y.set_witness(pw, &value.y);
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G2Affine};
    use ark_std::UniformRand;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::fields::fr_target::FrTarget;

    use super::G2Target;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_g2_add() {
        let rng = &mut rand::thread_rng();
        let a = G2Affine::rand(rng);
        let b = G2Affine::rand(rng);
        let c_expected: G2Affine = (a + b).into();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = G2Target::constant(&mut builder, a);
        let b_t = G2Target::constant(&mut builder, b);
        let c_t = a_t.add(&mut builder, &b_t);
        let c_expected_t = G2Target::constant(&mut builder, c_expected);

        G2Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_g2_double() {
        let rng = &mut rand::thread_rng();
        let a = G2Affine::rand(rng);
        let c_expected: G2Affine = (a + a).into();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = G2Target::constant(&mut builder, a);
        let c_t = a_t.double(&mut builder);
        let c_expected_t = G2Target::constant(&mut builder, c_expected);

        G2Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_g2_neg() {
        let rng = &mut rand::thread_rng();
        let a = G2Affine::rand(rng);
        let c_expected: G2Affine = (-a).into();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = G2Target::constant(&mut builder, a);
        let c_t = a_t.neg(&mut builder);
        let c_expected_t = G2Target::constant(&mut builder, c_expected);

        G2Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_pow_var_simple_g2() {
        let rng = &mut rand::thread_rng();

        let p = G2Affine::rand(rng);
        let n = Fr::rand(rng);
        let r_expected: G2Affine = (p * n).into();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let p_t = G2Target::constant(&mut builder, p);
        let n_t = FrTarget::constant(&mut builder, n);

        let r_t = p_t.pow_var_simple(&mut builder, &n_t);
        let r_expected_t = G2Target::constant(&mut builder, r_expected);

        G2Target::connect(&mut builder, &r_t, &r_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }
}
