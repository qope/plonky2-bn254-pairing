use anyhow::Result;
use ark_bn254::{Fr, G1Affine};
use itertools::Itertools;
use plonky2::{
    field::goldilocks_field::GoldilocksField,
    iop::{target::Target, witness::PartialWitness},
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::PoseidonGoldilocksConfig,
        proof::ProofWithPublicInputs,
    },
};

use crate::{
    curves::g1curve_target::G1Target,
    fields::{fq_target::FqTarget, fr_target::FrTarget},
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

pub struct G1ExpTarget {
    pub p: G1Target<GoldilocksField, 2>,
    pub p_x: G1Target<GoldilocksField, 2>,
    pub x: FrTarget<GoldilocksField, 2>,
}

pub struct G1ExpWitness {
    pub p: G1Affine,
    pub p_x: G1Affine,
    pub x: Fr,
}

impl RecursiveCircuitTarget<GoldilocksField, 2, G1ExpTarget, G1ExpWitness> for G1ExpTarget {
    fn to_vec(&self) -> Vec<Target> {
        self.p
            .to_vec()
            .iter()
            .chain(self.p_x.to_vec().iter())
            .chain(self.x.to_vec().iter())
            .cloned()
            .collect_vec()
    }

    fn from_vec(builder: &mut CircuitBuilder<GoldilocksField, 2>, input: &[Target]) -> Self {
        let num_limbs = FqTarget::<GoldilocksField, 2>::num_max_limbs();
        let num_g1_limbs = 2 * num_limbs;
        let num_fr_limbs = FrTarget::<GoldilocksField, 2>::num_max_limbs();
        let mut input = input.to_vec();
        let p_raw = input.drain(0..num_g1_limbs).collect_vec();
        let p_x_raw = input.drain(0..num_g1_limbs).collect_vec();
        let x_raw = input.drain(0..num_fr_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let p = G1Target::from_vec(builder, &p_raw);
        let p_x = G1Target::from_vec(builder, &p_x_raw);
        let x = FrTarget::from_vec(builder, &x_raw);
        Self { p, p_x, x }
    }

    fn set_witness(&self, pw: &mut PartialWitness<GoldilocksField>, value: &G1ExpWitness) {
        self.p.set_witness(pw, &value.p);
        self.p_x.set_witness(pw, &value.p_x);
        self.x.set_witness(pw, &value.x);
    }
}

pub fn build_g1_exp_circuit() -> (
    CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    G1ExpTarget,
) {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
    let p = G1Target::new(&mut builder);
    let x = FrTarget::new(&mut builder);
    let p_x = p.pow_var_simple(&mut builder, &x);
    let target = G1ExpTarget { p, p_x, x };
    // register public inputs
    builder.register_public_inputs(&target.to_vec());
    let data = builder.build();
    (data, target)
}

pub fn generate_g1_exp_proof(
    data: &CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    g1exp_t: &G1ExpTarget,
    g1exp_witness: &G1ExpWitness,
) -> Result<ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2>> {
    let mut pw = PartialWitness::<GoldilocksField>::new();
    g1exp_t.set_witness(&mut pw, g1exp_witness);
    let proof = data.prove(pw);
    proof
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bn254::{Fr, G1Affine};
    use ark_std::UniformRand;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::traits::recursive_circuit_target::RecursiveCircuitTarget;

    use super::{build_g1_exp_circuit, generate_g1_exp_proof, G1ExpTarget, G1ExpWitness};

    type F = GoldilocksField;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;

    #[test]
    fn test_recursive_g1_exp() {
        let (inner_data, g1exp_t) = build_g1_exp_circuit();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut rng = rand::thread_rng();
        let p = G1Affine::rand(&mut rng);
        let x = Fr::rand(&mut rng);
        let p_x: G1Affine = (p * x).into();
        let now = Instant::now();
        let proof =
            generate_g1_exp_proof(&inner_data, &g1exp_t, &G1ExpWitness { p, x, p_x }).unwrap();
        println!("proof generation took {} s", now.elapsed().as_secs());

        let verifier_target = builder.constant_verifier_data(&inner_data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        let pi = G1ExpTarget::from_vec(&mut builder, &proof_t.public_inputs);
        builder.verify_proof::<C>(&proof_t, &verifier_target, &inner_data.common);

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_t, &proof);
        pi.p.set_witness(&mut pw, &p);
        pi.p_x.set_witness(&mut pw, &p_x);
        pi.x.set_witness(&mut pw, &x);

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}
