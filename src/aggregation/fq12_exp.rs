use anyhow::Result;
use ark_bn254::{Fq12, Fr};
use bitvec::prelude::*;
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::One;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::{AlgebraicHasher, GenericConfig},
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
};

use crate::{
    fields::{fq12_target::Fq12Target, fq_target::FqTarget, fr_target::FrTarget},
    traits::recursive_circuit_target::RecursiveCircuitTarget,
};

use super::fq12_exp_witness::PartialExpStatementWitness;

const NUM_BITS: usize = 5;

pub struct PartialFq12ExpStatement<F: RichField + Extendable<D>, const D: usize> {
    bits: Vec<BoolTarget>,
    start: Fq12Target<F, D>,
    end: Fq12Target<F, D>,
    start_square: Fq12Target<F, D>,
    end_square: Fq12Target<F, D>,
}

fn verify_partial_fq12_exp_statement<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    statement: &PartialFq12ExpStatement<F, D>,
) {
    let mut squares = vec![];
    let mut v = statement.start_square.clone();
    squares.push(v.clone());
    for _ in 0..statement.bits.len() {
        v = v.mul(builder, &v);
        squares.push(v.clone());
    }
    let end_square = squares.pop().unwrap();

    Fq12Target::connect(builder, &end_square, &statement.end_square);

    let mut r = statement.start.clone();
    for i in 0..statement.bits.len() {
        r = r.conditional_mul(builder, &squares[i], &statement.bits[i]);
    }
    Fq12Target::connect(builder, &r, &statement.end);
}

impl<F: RichField + Extendable<D>, const D: usize>
    RecursiveCircuitTarget<F, D, PartialFq12ExpStatement<F, D>, PartialExpStatementWitness>
    for PartialFq12ExpStatement<F, D>
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
        let num_fq12_limbs = 12 * num_limbs;

        let mut input = input.to_vec();
        let bits_raw = input.drain(0..NUM_BITS).collect_vec();
        let start_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let end_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let start_square_raw = input.drain(0..num_fq12_limbs).collect_vec();
        let end_square_raw = input.drain(0..num_fq12_limbs).collect_vec();

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
        let start = Fq12Target::from_vec(builder, &start_raw);
        let end = Fq12Target::from_vec(builder, &end_raw);
        let start_square = Fq12Target::from_vec(builder, &start_square_raw);
        let end_square = Fq12Target::from_vec(builder, &end_square_raw);

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

pub fn build_fq12_exp_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>() -> (CircuitData<F, C, D>, PartialFq12ExpStatement<F, D>) {
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let bits_t = (0..NUM_BITS)
        .map(|_| builder.add_virtual_bool_target_safe())
        .collect_vec();
    let statement_t = PartialFq12ExpStatement {
        bits: bits_t,
        start: Fq12Target::new(&mut builder),
        end: Fq12Target::new(&mut builder),
        start_square: Fq12Target::new(&mut builder),
        end_square: Fq12Target::new(&mut builder),
    };
    verify_partial_fq12_exp_statement(&mut builder, &statement_t);

    // register public input
    let pi_vec = statement_t.to_vec();
    builder.register_public_inputs(&pi_vec);
    let data = builder.build::<C>();
    (data, statement_t)
}

pub fn generate_fq12_exp_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    inner_data: &CircuitData<F, C, D>,
    statement_t: &PartialFq12ExpStatement<F, D>,
    statement_witness: &PartialExpStatementWitness,
) -> Result<ProofWithPublicInputs<F, C, D>> {
    let mut pw = PartialWitness::<F>::new();
    statement_t.set_witness(&mut pw, statement_witness);
    let proof = inner_data.prove(pw);
    proof
}

pub struct Fq12ExpAggregationTarget<F: RichField + Extendable<D>, const D: usize> {
    pub proofs: Vec<ProofWithPublicInputsTarget<D>>,
    pub p: Fq12Target<F, D>,
    pub p_x: Fq12Target<F, D>,
    pub x: FrTarget<F, D>,
}

pub struct Fq12ExpAggregationWitness<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub proofs: Vec<ProofWithPublicInputs<F, C, D>>,
    pub p: Fq12,
    pub p_x: Fq12,
    pub x: Fr,
}

pub struct Fq12ExpAggregationPublicInputs<F: RichField + Extendable<D>, const D: usize> {
    pub p: Fq12Target<F, D>,
    pub p_x: Fq12Target<F, D>,
    pub x: FrTarget<F, D>,
}

impl<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
    RecursiveCircuitTarget<
        F,
        D,
        Fq12ExpAggregationPublicInputs<F, D>,
        Fq12ExpAggregationWitness<F, C, D>,
    > for Fq12ExpAggregationTarget<F, D>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
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
        builder: &mut CircuitBuilder<F, D>,
        input: &[Target],
    ) -> Fq12ExpAggregationPublicInputs<F, D> {
        let num_lims = FqTarget::<F, D>::num_max_limbs();
        let num_fq12_lims = 12 * num_lims;
        let num_fr_limbs = FrTarget::<F, D>::num_max_limbs();
        let mut input = input.to_vec();
        let p_raw = input.drain(0..num_fq12_lims).collect_vec();
        let p_x_raw = input.drain(0..num_fq12_lims).collect_vec();
        let x_raw = input.drain(0..num_fr_limbs).collect_vec();
        assert_eq!(input.len(), 0);

        let p = Fq12Target::from_vec(builder, &p_raw);
        let p_x = Fq12Target::from_vec(builder, &p_x_raw);
        let x = FrTarget::from_vec(builder, &x_raw);
        Fq12ExpAggregationPublicInputs { p, p_x, x }
    }

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &Fq12ExpAggregationWitness<F, C, D>) {
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

pub fn build_fq12_exp_aggregation_circuit<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    inner_data: &CircuitData<F, C, D>,
    num_proofs: usize,
) -> (CircuitData<F, C, D>, Fq12ExpAggregationTarget<F, D>)
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let verifier_circuit_target = builder.constant_verifier_data(&inner_data.verifier_only);

    let mut proofs_t = vec![];
    let mut statements = vec![];
    for _ in 0..num_proofs {
        let proof_t = builder.add_virtual_proof_with_pis(&inner_data.common);
        builder.verify_proof::<C>(&proof_t, &verifier_circuit_target, &inner_data.common);
        let pi_vec = proof_t.public_inputs.clone();
        let statement = PartialFq12ExpStatement::from_vec(&mut builder, &pi_vec);
        proofs_t.push(proof_t);
        statements.push(statement);
    }

    // verify boundry condition
    let one = Fq12Target::constant(&mut builder, Fq12::one());
    let start = statements.first().unwrap().start.clone();
    Fq12Target::connect(&mut builder, &start, &one);
    let p = statements.first().unwrap().start_square.clone();
    let p_x = statements.last().unwrap().end.clone();

    // verify transition rule
    for i in 1..statements.len() {
        let prev_end = statements[i - 1].end.clone();
        let prev_end_square = statements[i - 1].end_square.clone();
        let start = statements[i].start.clone();
        let start_square = statements[i].start_square.clone();
        Fq12Target::connect(&mut builder, &start, &prev_end);
        Fq12Target::connect(&mut builder, &start_square, &prev_end_square);
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

    let target = Fq12ExpAggregationTarget::<F, D> {
        proofs: proofs_t,
        p,
        p_x,
        x,
    };

    // register public inputs
    let pi_vec = <Fq12ExpAggregationTarget<F, D> as RecursiveCircuitTarget<
        F,
        D,
        Fq12ExpAggregationPublicInputs<F, D>,
        Fq12ExpAggregationWitness<F, C, D>,
    >>::to_vec(&target);
    builder.register_public_inputs(&pi_vec);

    let data = builder.build();

    (data, target)
}

pub fn biguint_to_bits(x: &BigUint) -> Vec<bool> {
    let limbs = x.to_bytes_le();
    let mut bits = vec![];
    for limb in limbs {
        let limb_bits = limb.view_bits::<Lsb0>().iter().map(|b| *b).collect_vec();
        bits.extend(limb_bits);
    }
    bits
}

pub fn generate_fq12_exp_aggregation_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
>(
    data: &CircuitData<F, C, D>,
    aggregation_t: &Fq12ExpAggregationTarget<F, D>,
    aggregation_witness: &Fq12ExpAggregationWitness<F, C, D>,
) -> Result<ProofWithPublicInputs<F, C, D>>
where
    <C as GenericConfig<D>>::Hasher: AlgebraicHasher<F>,
{
    let mut pw = PartialWitness::<F>::new();
    aggregation_t.set_witness(&mut pw, aggregation_witness);
    let proof = data.prove(pw);
    proof
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bn254::{Fq12, Fr};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use num_bigint::BigUint;
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

    use super::{
        build_fq12_exp_aggregation_circuit, build_fq12_exp_circuit,
        generate_fq12_exp_aggregation_proof, verify_partial_fq12_exp_statement,
        Fq12ExpAggregationWitness, PartialFq12ExpStatement,
    };
    use crate::aggregation::fq12_exp::{Fq12ExpAggregationPublicInputs, Fq12ExpAggregationTarget};
    use crate::{
        aggregation::{
            fq12_exp::{generate_fq12_exp_proof, NUM_BITS},
            fq12_exp_witness::{
                generate_fq12exp_witness_from_x, partial_exp_statement_witness,
                PartialExpStatementWitness, PartialExpStatementWitnessInput,
                PartialExpStatementWitnessOutput,
            },
            g2_exp_witness::get_num_statements,
        },
        fields::fq12_target::Fq12Target,
        traits::recursive_circuit_target::RecursiveCircuitTarget,
    };

    type F = GoldilocksField;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;

    #[test]
    fn test_verify_partial_exp_statement() {
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let mut rng = rand::thread_rng();

        // make witness
        let start = Fq12::rand(&mut rng);
        let start_square = Fq12::rand(&mut rng);
        let bits: Vec<bool> = vec![rng.gen(); 5];
        let PartialExpStatementWitnessOutput { end, end_square } =
            partial_exp_statement_witness(&PartialExpStatementWitnessInput {
                bits: bits.clone(),
                start,
                start_square,
            });

        let start_t = Fq12Target::constant(&mut builder, start);
        let end_t = Fq12Target::constant(&mut builder, end);
        let start_square_t = Fq12Target::constant(&mut builder, start_square);
        let end_square_t = Fq12Target::constant(&mut builder, end_square);
        let bits_t = bits.iter().map(|b| builder.constant_bool(*b)).collect_vec();

        verify_partial_fq12_exp_statement(
            &mut builder,
            &PartialFq12ExpStatement {
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

    #[test]
    fn test_gen_proof() {
        let (inner_data, statement_target) = build_fq12_exp_circuit::<F, C, D>();
        let mut rng = rand::thread_rng();
        // make witness
        let start = Fq12::rand(&mut rng);
        let start_square = Fq12::rand(&mut rng);
        let bits: Vec<bool> = vec![rng.gen(); NUM_BITS];
        let PartialExpStatementWitnessOutput { end, end_square } =
            partial_exp_statement_witness(&PartialExpStatementWitnessInput {
                bits: bits.clone(),
                start,
                start_square,
            });
        let sw = PartialExpStatementWitness {
            bits,
            start,
            end,
            start_square,
            end_square,
        };
        let _proof = generate_fq12_exp_proof(&inner_data, &statement_target, &sw).unwrap();
    }

    #[test]
    fn test_recursive_fq12_aggregation() {
        let mut rng = rand::thread_rng();
        let p = Fq12::rand(&mut rng);
        let x = Fr::rand(&mut rng);
        let x_biguint: BigUint = x.into();
        let p_x = p.pow(&x_biguint.to_u64_digits());

        let num_statements = get_num_statements(256, NUM_BITS);
        let (inner_data, statement_t) = build_fq12_exp_circuit::<F, C, D>();
        let (data, aggregation_t) = build_fq12_exp_aggregation_circuit(&inner_data, num_statements);

        // witness generation
        println!("Start generating proofs");
        let now = Instant::now();
        let statements_witness = generate_fq12exp_witness_from_x(p, x, NUM_BITS);
        let proofs: Vec<_> = statements_witness
            .par_iter()
            .map(|sw| generate_fq12_exp_proof(&inner_data, &statement_t, sw).unwrap())
            .collect();
        println!(
            "End of witness proofs generation: {} s",
            now.elapsed().as_secs()
        );

        // set witness
        let aggregation_witness = Fq12ExpAggregationWitness { proofs, p, p_x, x };

        // generate aggregation proof
        let now = Instant::now();
        let proof =
            generate_fq12_exp_aggregation_proof(&data, &aggregation_t, &aggregation_witness)
                .unwrap();
        println!(
            "End of aggregation proof generation: {} s",
            now.elapsed().as_secs()
        );

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let verifier_target = builder.constant_verifier_data(&data.verifier_only);
        let proof_t = builder.add_virtual_proof_with_pis(&data.common);
        let pi = <Fq12ExpAggregationTarget<F, D> as RecursiveCircuitTarget<
            F,
            D,
            Fq12ExpAggregationPublicInputs<F, D>,
            Fq12ExpAggregationWitness<F, C, D>,
        >>::from_vec(&mut builder, &proof_t.public_inputs);
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
