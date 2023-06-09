use ark_bn254::{Fr, G2Affine};
use ark_std::UniformRand;
use itertools::Itertools;
use rand::SeedableRng;

use super::fq12_exp::biguint_to_bits;

pub const RAND_SEED: u64 = 42;

pub struct PartialExpStatementWitnessInput {
    pub bits: Vec<bool>,
    pub start: G2Affine,
    pub start_square: G2Affine,
}

pub struct PartialExpStatementWitnessOutput {
    pub end: G2Affine,
    pub end_square: G2Affine,
}

#[derive(Clone, Debug)]
pub struct PartialExpStatementWitness {
    pub bits: Vec<bool>,
    pub start: G2Affine,
    pub end: G2Affine,
    pub start_square: G2Affine,
    pub end_square: G2Affine,
}

pub fn gen_rando() -> G2Affine {
    let mut rng = rand::rngs::StdRng::seed_from_u64(RAND_SEED);
    let rando = G2Affine::rand(&mut rng);
    rando
}

pub fn get_num_statements(bits: usize, bits_per_step: usize) -> usize {
    let rem = bits % bits_per_step;
    let to_padd = if rem == 0 { 0 } else { bits_per_step - rem };
    (bits + to_padd) / bits_per_step
}

pub fn generate_g2exp_witness(
    p: G2Affine,
    bits: Vec<bool>,
    bits_per_step: usize,
) -> Vec<PartialExpStatementWitness> {
    let mut bits = bits;

    // pad with false
    let rem = bits.len() % bits_per_step;
    let to_padd = if rem == 0 { 0 } else { bits_per_step - rem };
    bits.extend(vec![false; to_padd]);

    let mut start = gen_rando();
    let mut cur_square = p;

    let statements = bits
        .iter()
        .cloned()
        .chunks(bits_per_step)
        .into_iter()
        .map(|bit_chunk| {
            let input = PartialExpStatementWitnessInput {
                bits: bit_chunk.collect_vec(),
                start,
                start_square: cur_square,
            };
            let output = partial_exp_statement_witness(&input);
            start = output.end;
            cur_square = output.end_square;
            PartialExpStatementWitness {
                bits: input.bits,
                start: input.start,
                end: output.end,
                start_square: input.start_square,
                end_square: output.end_square,
            }
        })
        .collect_vec();

    statements
}

pub fn generate_g2exp_witness_from_x(
    p: G2Affine,
    x: Fr,
    bits_per_step: usize,
) -> Vec<PartialExpStatementWitness> {
    // decompose x to 256bits
    let mut bits = biguint_to_bits(&x.into());
    let to_padd = 256 - bits.len();
    bits.extend(vec![false; to_padd]);
    assert_eq!(bits.len(), 256);
    generate_g2exp_witness(p, bits, bits_per_step)
}

pub fn partial_exp_statement_witness(
    statement: &PartialExpStatementWitnessInput,
) -> PartialExpStatementWitnessOutput {
    let mut squares = vec![];
    let mut v = statement.start_square.clone();
    squares.push(v.clone());
    for _ in 0..statement.bits.len() {
        v = (v + v).into();
        squares.push(v.clone());
    }
    let end_square = squares.pop().unwrap();
    let mut r = statement.start.clone();
    for i in 0..statement.bits.len() {
        r = if statement.bits[i] {
            (r + squares[i]).into()
        } else {
            r
        };
    }
    let end = r;
    PartialExpStatementWitnessOutput { end, end_square }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fr, G2Affine};
    use ark_std::UniformRand;
    use num_bigint::BigUint;
    use rand::Rng;

    use crate::aggregation::{
        fq12_exp::biguint_to_bits,
        g2_exp_witness::{gen_rando, generate_g2exp_witness},
    };

    #[test]
    fn test_g2_generate_witness() {
        let mut rng = rand::thread_rng();
        let p = G2Affine::rand(&mut rng);
        let x: u8 = rng.gen();
        let x_biguint: BigUint = x.into();
        let bits = biguint_to_bits(&x_biguint);
        let expected: G2Affine = (p * Fr::from(x)).into();

        let statements = generate_g2exp_witness(p, bits, 4);

        let rando = gen_rando();
        let end = statements.last().unwrap().end;
        let result: G2Affine = (end - rando).into();
        assert_eq!(result, expected);
    }
}
