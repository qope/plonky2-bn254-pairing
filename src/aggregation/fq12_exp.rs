use anyhow::Result;
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
        proof::ProofWithPublicInputs,
    },
};

use crate::fields::{fq12_target::Fq12Target, fq_target::FqTarget};

use super::{
    fq12_generate_witness::PartialExpStatementWitness,
    recursive_circuit_target::RecursiveCircuitTarget,
};

const NUM_BITS: usize = 5;

pub struct PartialExpStatement<F: RichField + Extendable<D>, const D: usize> {
    bits: Vec<BoolTarget>,
    start: Fq12Target<F, D>,
    end: Fq12Target<F, D>,
    start_square: Fq12Target<F, D>,
    end_square: Fq12Target<F, D>,
}

pub fn verify_partial_exp_statement<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    statement: &PartialExpStatement<F, D>,
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
    RecursiveCircuitTarget<F, D, PartialExpStatementWitness> for PartialExpStatement<F, D>
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

pub fn build_circuit(
    bits_len: usize,
) -> (
    CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    PartialExpStatement<GoldilocksField, 2>,
) {
    const D: usize = 2;
    let config = CircuitConfig::standard_ecc_config();
    let mut builder = CircuitBuilder::<GoldilocksField, D>::new(config);
    let bits_t = (0..bits_len)
        .map(|_| builder.add_virtual_bool_target_safe())
        .collect_vec();
    let statement_t = PartialExpStatement {
        bits: bits_t,
        start: Fq12Target::new(&mut builder),
        end: Fq12Target::new(&mut builder),
        start_square: Fq12Target::new(&mut builder),
        end_square: Fq12Target::new(&mut builder),
    };
    verify_partial_exp_statement(&mut builder, &statement_t);

    // register public input
    let pi_vec = statement_t.to_vec();
    builder.register_public_inputs(&pi_vec);
    let data = builder.build::<PoseidonGoldilocksConfig>();
    (data, statement_t)
}

pub fn generate_proof(
    data: &CircuitData<GoldilocksField, PoseidonGoldilocksConfig, 2>,
    statement_t: &PartialExpStatement<GoldilocksField, 2>,
    statement_witness: &PartialExpStatementWitness,
) -> Result<ProofWithPublicInputs<GoldilocksField, PoseidonGoldilocksConfig, 2>> {
    let mut pw = PartialWitness::<GoldilocksField>::new();
    statement_t.set_witness(&mut pw, statement_witness);
    let proof = data.prove(pw);
    proof
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fq12;
    use ark_std::UniformRand;
    use itertools::Itertools;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::Rng;

    use crate::{
        aggregation::fq12_generate_witness::{
            partial_exp_statement_witness, PartialExpStatementWitnessInput,
            PartialExpStatementWitnessOutput,
        },
        fields::fq12_target::Fq12Target,
    };

    use super::{verify_partial_exp_statement, PartialExpStatement};

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

        verify_partial_exp_statement(
            &mut builder,
            &PartialExpStatement {
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
}
