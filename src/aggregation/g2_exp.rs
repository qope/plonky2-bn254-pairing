use anyhow::Result;
use ark_bn254::{Fr, G2Affine};
use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, goldilocks_field::GoldilocksField},
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::PoseidonGoldilocksConfig,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};

use crate::{
    curves::g2curve_target::G2Target,
    fields::{fq_target::FqTarget, fr_target::FrTarget},
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

use super::g2_exp_witness::{gen_rando, PartialExpStatementWitness};

const NUM_BITS: usize = 6;

pub struct PartialG2ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    bits: Vec<BoolTarget>,
    start: G2Target<F, D>,
    end: G2Target<F, D>,
    start_square: G2Target<F, D>,
    end_square: G2Target<F, D>,
}

fn verify_partial_g2_exp_statement<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    statement: &PartialG2ExpStatement<F, D>,
) {
    let mut squares = vec![];
    let mut v = statement.start_square.clone();
    squares.push(v.clone());
    for _ in 0..statement.bits.len() {
        v = v.double(builder);
        squares.push(v.clone());
    }
    let end_square = squares.pop().unwrap();

    G2Target::connect(builder, &end_square, &statement.end_square);

    let mut r = statement.start.clone();
    for i in 0..statement.bits.len() {
        r = r.conditional_add(builder, &squares[i], &statement.bits[i]);
    }
    G2Target::connect(builder, &r, &statement.end);
}

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, PartialG2ExpStatement<F, D>, PartialExpStatementWitness>
    for PartialG2ExpStatement<F, D>
{
    fn to_vec(&self) -> Vec<Target> {
        let mut output = vec![];
        let bits = self.bits.iter().map(|x| x.target).collect_vec();
        output.extend(bits);
        output.extend(self.start.to_vec());
        output.extend(self.end.to_vec());
        output.extend(self.start_square.to_vec());
        output.extend(self.end_square.to_vec());
        output
    }

    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        let num_limbs = FqTarget::<F, D>::num_max_limbs();
        let num_g2_limbs = 4 * num_limbs;

        let mut input = input.to_vec();
        let bits_raw = input.drain(0..NUM_BITS).collect_vec();
        let start_raw = input.drain(0..num_g2_limbs).collect_vec();
        let end_raw = input.drain(0..num_g2_limbs).collect_vec();
        let start_square_raw = input.drain(0..num_g2_limbs).collect_vec();
        let end_square_raw = input.drain(0..num_g2_limbs).collect_vec();

        assert_eq!(input.len(), 0);

        // for range check
        let bits = (0..NUM_BITS)
            .map(|_| builder.add_virtual_bool_target_safe())
            .collect_vec();
        bits_raw
            .iter()
            .cloned()
            .zip(bits.clone())
            .map(|(b0, b1)| builder.connect(b0, b1.target))
            .for_each(drop);
        let start = G2Target::from_vec(builder, &start_raw);
        let end = G2Target::from_vec(builder, &end_raw);
        let start_square = G2Target::from_vec(builder, &start_square_raw);
        let end_square = G2Target::from_vec(builder, &end_square_raw);

        Self {
            bits,
            start,
            end,
            start_square,
            end_square,
        }
    }

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &PartialExpStatementWitness) {
        self.bits
            .iter()
            .cloned()
            .zip(&value.bits)
            .map(|(bit_t, bit)| pw.set_bool_target(bit_t, *bit))
            .for_each(drop);
        self.start.set_witness(pw, &value.start);
        self.end.set_witness(pw, &value.end);
        self.start_square.set_witness(pw, &value.start_square);
        self.end_square.set_witness(pw, &value.end_square);
    }
}

pub fn build_g2_exp_circuit() -> (
    CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    PartialG2ExpStatement<GoldilocksField, 2>,
) {
    const D: usize = 2;
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<GoldilocksField, D>::new(config);
    let bits_t = (0..NUM_BITS)
        .map(|_| builder.add_virtual_bool_target_safe())
        .collect_vec();
    let statement_t = PartialG2ExpStatement {
        bits: bits_t,
        start: G2Target::new(&mut builder),
        end: G2Target::new(&mut builder),
        start_square: G2Target::new(&mut builder),
        end_square: G2Target::new(&mut builder),
    };
    verify_partial_g2_exp_statement(&mut builder, &statement_t);

    // register public input
    let pi_vec = statement_t.to_vec();
    builder.register_public_inputs(&pi_vec);
    let data = builder.build::<PoseidonGoldilocksConfig>();
    (data, statement_t)
}

pub fn generate_g2_exp_proof(
    inner_data: &CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    statement_t: &PartialG2ExpStatement<GoldilocksField, 2>,
    statement_witness: &PartialExpStatementWitness,
) -> Result<ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2>> {
    let mut pw = PartialWitness::<GoldilocksField>::new();
    statement_t.set_witness(&mut pw, statement_witness);
    let proof = inner_data.prove(pw);
    proof
}

pub struct G2ExpAggregationTarget {
    pub proofs: Vec<ProofWithPublicInputsTarget<2>>,
    pub p: G2Target<GoldilocksField, 2>,
    pub p_x: G2Target<GoldilocksField, 2>,
    pub x: FrTarget<GoldilocksField, 2>,
}

pub struct G2ExpAggregationWitness {
    pub proofs: Vec<ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2>>,
    pub p: G2Affine,
    pub p_x: G2Affine,
    pub x: Fr,
}

pub struct G2ExpAggregationPublicInputs {
    pub p: G2Target<GoldilocksField, 2>,
    pub p_x: G2Target<GoldilocksField, 2>,
    pub x: FrTarget<GoldilocksField, 2>,
}

impl
    RecursiveCircuitTarget<
        GoldilocksField,
        2,
        G2ExpAggregationPublicInputs,
        G2ExpAggregationWitness,
    > for G2ExpAggregationTarget
{
    fn to_vec(&self) -> Vec<Target> {
        self.p
            .to_vec()
            .iter()
            .chain(self.p_x.to_vec().iter())
            .chain(self.x.to_vec().iter())
            .cloned()
            .collect_vec()
    }

    fn from_vec(
        builder: &mut CircuitBuilder<GoldilocksField, 2>,
        input: &[Target],
    ) -> G2ExpAggregationPublicInputs {
        let num_limbs = FqTarget::<GoldilocksField, 2>::num_max_limbs();
        let num_g2_limbs = 4 * num_limbs;
        let num_fr_limbs = FrTarget::<GoldilocksField, 2>::num_max_limbs();
        let mut input = input.to_vec();
        let p_raw = input.drain(0..num_g2_limbs).collect_vec();
        let p_x_raw = input.drain(0..num_g2_limbs).collect_vec();
        let x_raw = input.drain(0..num_fr_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let p = G2Target::from_vec(builder, &p_raw);
        let p_x = G2Target::from_vec(builder, &p_x_raw);
        let x = FrTarget::from_vec(builder, &x_raw);
        G2ExpAggregationPublicInputs { p, p_x, x }
    }

    fn set_witness(
        &self,
        pw: &mut PartialWitness<GoldilocksField>,
        value: &G2ExpAggregationWitness,
    ) {
        self.proofs
            .iter()
            .zip(value.proofs.iter())
            .for_each(|(p_t, p)| {
                pw.set_proof_with_pis_target(p_t, p);
            });
        self.p.set_witness(pw, &value.p);
        self.p_x.set_witness(pw, &value.p_x);
        self.x.set_witness(pw, &value.x);
    }
}

pub fn build_g2_exp_aggregation_circuit(
    inner_data: &CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    num_proofs: usize,
) -> (
    CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    G2ExpAggregationTarget,
) {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<GoldilocksField, 2>::new(config);
    let verifier_circuit_target = builder.constant_verifier_data(&inner_data.verifier_only);

    let mut proofs_t = vec![];
    let mut statements = vec![];
    for _ in 0..num_proofs {
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        builder.verify_proof::<PoseidonGoldilocksConfig>(
            &proof_t,
            &verifier_circuit_target,
            &inner_data.common,
        );
        let pi_vec = proof_t.public_inputs.clone();
        let statement = PartialG2ExpStatement::from_vec(&mut builder, &pi_vec);
        proofs_t.push(proof_t);
        statements.push(statement);
    }

    // verify boundry condition
    let rando = G2Target::constant(&mut builder, gen_rando());
    let start = statements.first().unwrap().start.clone();
    G2Target::connect(&mut builder, &start, &rando);
    let p = statements.first().unwrap().start_square.clone();
    let end = statements.last().unwrap().end.clone();
    let neg_rando = G2Target::constant(&mut builder, -gen_rando());
    let p_x = end.add(&mut builder, &neg_rando);

    // verify transition rule
    for i in 1..statements.len() {
        let prev_end = statements[i - 1].end.clone();
        let prev_end_square = statements[i - 1].end_square.clone();
        let start = statements[i].start.clone();
        let start_square = statements[i].start_square.clone();
        G2Target::connect(&mut builder, &start, &prev_end);
        G2Target::connect(&mut builder, &start_square, &prev_end_square);
    }

    // verify bit decomposition
    let mut bits = vec![];
    for s in statements {
        assert_eq!(s.bits.len(), NUM_BITS);
        bits.extend(s.bits.clone());
    }
    let x = FrTarget::new(&mut builder);
    let x_bits = x.to_bits(&mut builder);

    assert!(x_bits.len() <= bits.len());
    for i in 0..x_bits.len() {
        builder.connect(bits[i].target, x_bits[i].target);
    }
    let false_t = builder.constant_bool(false);
    for i in x_bits.len()..bits.len() {
        builder.connect(bits[i].target, false_t.target);
    }

    let target = G2ExpAggregationTarget {
        proofs: proofs_t,
        p,
        p_x,
        x,
    };

    // register public inputs
    builder.register_public_inputs(&target.to_vec());

    let data = builder.build();

    (data, target)
}

pub fn generate_g2_exp_aggregation_proof(
    data: &CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    aggregation_t: &G2ExpAggregationTarget,
    aggregation_witness: &G2ExpAggregationWitness,
) -> Result<ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2>> {
    let mut pw = PartialWitness::<GoldilocksField>::new();
    aggregation_t.set_witness(&mut pw, aggregation_witness);
    let proof = data.prove(pw);
    proof
}
#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G2Affine};
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::Rng;
    use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

    use crate::{
        aggregation::{
            g2_exp::{
                build_g2_exp_aggregation_circuit, build_g2_exp_circuit, generate_g2_exp_proof,
                verify_partial_g2_exp_statement, PartialG2ExpStatement, NUM_BITS,
            },
            g2_exp_witness::{
                generate_witness_from_x, get_num_statements, partial_exp_statement_witness,
                PartialExpStatementWitnessInput, PartialExpStatementWitnessOutput,
            },
        },
        curves::g2curve_target::G2Target,
        traits::recursive_circuit_target::RecursiveCircuitTarget,
    };

    use super::{
        generate_g2_exp_aggregation_proof, G2ExpAggregationTarget, G2ExpAggregationWitness,
    };

    type F = GoldilocksField;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;

    #[test]
    fn test_verify_partial_g2_exp_statement() {
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut rng = rand::thread_rng();

        // make witness
        let start = G2Affine::rand(&mut rng);
        let start_square = G2Affine::rand(&mut rng);
        let bits: Vec<bool> = vec![rng.gen(); 5];
        let PartialExpStatementWitnessOutput { end, end_square } =
            partial_exp_statement_witness(&PartialExpStatementWitnessInput {
                bits: bits.clone(),
                start,
                start_square,
            });

        let start_t = G2Target::constant(&mut builder, start);
        let end_t = G2Target::constant(&mut builder, end);
        let start_square_t = G2Target::constant(&mut builder, start_square);
        let end_square_t = G2Target::constant(&mut builder, end_square);
        let bits_t = bits.iter().map(|b| builder.constant_bool(*b)).collect_vec();

        verify_partial_g2_exp_statement(
            &mut builder,
            &PartialG2ExpStatement {
                bits: bits_t,
                start: start_t,
                end: end_t,
                start_square: start_square_t,
                end_square: end_square_t,
            },
        );

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
        dbg!(data.common.degree_bits());
    }

    // #[test]
    // fn test_g2_aggregation() {
    //     let now = Instant::now();
    //     let (inner_data, statement_t) = build_g2_exp_circuit();
    //     let mut rng = rand::thread_rng();
    //     let p = G2Affine::rand(&mut rng);
    //     let x = Fr::rand(&mut rng);
    //     let x_biguint: BigUint = x.into();
    //     let bits = biguint_to_bits(&x_biguint);

    //     let statements_witness = generate_witness(p, bits.clone(), NUM_BITS);

    //     let p_x: G2Affine = (p * x).into();
    //     let result: G2Affine = (statements_witness.last().unwrap().end - gen_rando()).into();
    //     assert_eq!(result, p_x);
    //     println!(
    //         "Step circuit construction took {} secs",
    //         now.elapsed().as_secs()
    //     );

    //     println!("Start of proof generation");
    //     let now = Instant::now();
    //     let proofs: Vec<_> = statements_witness
    //         .par_iter()
    //         .map(|sw| generate_g2_exp_proof(&inner_data, &statement_t, sw).unwrap())
    //         .collect();
    //     println!(
    //         "{} proofs generation took: {} secs",
    //         proofs.len(),
    //         now.elapsed().as_secs()
    //     );

    //     let now = Instant::now();
    //     let (data, aggregation_t) =
    //         build_g2_exp_aggregation_circuit(&inner_data, statements_witness.len());
    //     println!(
    //         "Aggregation circuit construction took {} secs",
    //         now.elapsed().as_secs()
    //     );

    //     let mut pw = PartialWitness::new();
    //     aggregation_t
    //         .proofs
    //         .iter()
    //         .zip(proofs)
    //         .map(|(p_t, p)| pw.set_proof_with_pis_target(&p_t, &p))
    //         .for_each(drop);
    //     aggregation_t.p.set_witness(&mut pw, &p);
    //     aggregation_t
    //         .bits
    //         .iter()
    //         .zip(bits)
    //         .map(|(b_t, b)| pw.set_bool_target(*b_t, b))
    //         .for_each(drop);
    //     aggregation_t.p_x.set_witness(&mut pw, &p_x);

    //     println!("Start aggregation proof");
    //     let now = Instant::now();
    //     let _proof = data.prove(pw).unwrap();
    //     println!("Aggregation took {} secs", now.elapsed().as_secs());
    // }

    #[test]
    fn test_recursive_g2_aggregation() {
        let mut rng = rand::thread_rng();
        let p = G2Affine::rand(&mut rng);
        let x = Fr::rand(&mut rng);
        let p_x = (p * x).into();

        let num_statements = get_num_statements(256, NUM_BITS);
        let (inner_data, statement_t) = build_g2_exp_circuit();
        let (data, aggregation_t) = build_g2_exp_aggregation_circuit(&inner_data, num_statements);

        // witness generation
        let statements_witness = generate_witness_from_x(p, x, NUM_BITS);
        let proofs: Vec<_> = statements_witness
            .par_iter()
            .map(|sw| generate_g2_exp_proof(&inner_data, &statement_t, sw).unwrap())
            .collect();

        // set witness
        let aggregation_witness = G2ExpAggregationWitness { proofs, p, p_x, x };

        // generate aggregation proof
        let proof =
            generate_g2_exp_aggregation_proof(&data, &aggregation_t, &aggregation_witness).unwrap();

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let verifier_target = builder.constant_verifier_data(&data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&data.common);
        let pi = G2ExpAggregationTarget::from_vec(&mut builder, &proof_t.public_inputs);
        builder.verify_proof::<C>(&proof_t, &verifier_target, &data.common);

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_t, &proof);
        pi.p.set_witness(&mut pw, &p);
        pi.p_x.set_witness(&mut pw, &p_x);
        pi.x.set_witness(&mut pw, &x);

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }
}
