use ark_bn254::{Fq12, Fr};
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::One;

pub fn u8_to_bools(n: u8) -> Vec<bool> {
    let mut bits = Vec::with_capacity(8);
    for i in 0..8 {
        bits.push((n & (1 << i)) != 0);
    }
    bits
}

pub fn u16_to_bools(n: u16) -> Vec<bool> {
    let mut bits = Vec::with_capacity(16);
    for i in 0..16 {
        bits.push((n & (1 << i)) != 0);
    }
    bits
}

pub fn bools_to_u8(bits: &[bool]) -> u8 {
    let mut result: u8 = 0;
    for (index, &bit) in bits.iter().enumerate().take(8) {
        if bit {
            result |= 1 << index;
        }
    }
    result
}

pub fn generate_witness(p: Fq12, n: Fr, bits_per_step: usize) -> Vec<PartialExpStatementWitness> {
    let n_biguint: BigUint = n.into();
    let n_bytes = n_biguint.to_bytes_le();
    let mut bits = n_bytes.iter().flat_map(|a| u8_to_bools(*a)).collect_vec();

    // pad with false
    let rem = bits.len() % bits_per_step;
    bits.extend(vec![false; rem]);

    let mut start = Fq12::one();
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

pub fn generate_witness_from_bits(
    p: Fq12,
    bits: Vec<bool>,
    bits_per_step: usize,
) -> Vec<PartialExpStatementWitness> {
    let mut bits = bits;

    // pad with false
    let rem = bits.len() % bits_per_step;
    let to_padd = if rem == 0 { 0 } else { bits_per_step - rem };
    bits.extend(vec![false; to_padd]);

    let mut start = Fq12::one();
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

pub struct PartialExpStatementWitnessInput {
    pub bits: Vec<bool>,
    pub start: Fq12,
    pub start_square: Fq12,
}

pub struct PartialExpStatementWitnessOutput {
    pub end: Fq12,
    pub end_square: Fq12,
}

#[derive(Clone, Debug)]
pub struct PartialExpStatementWitness {
    pub bits: Vec<bool>,
    pub start: Fq12,
    pub end: Fq12,
    pub start_square: Fq12,
    pub end_square: Fq12,
}

pub fn partial_exp_statement_witness(
    statement: &PartialExpStatementWitnessInput,
) -> PartialExpStatementWitnessOutput {
    let mut squares = vec![];
    let mut v = statement.start_square.clone();
    squares.push(v.clone());
    for _ in 0..statement.bits.len() {
        v = v * v;
        squares.push(v.clone());
    }
    let end_square = squares.pop().unwrap();
    let mut r = statement.start.clone();
    for i in 0..statement.bits.len() {
        r = if statement.bits[i] { r * squares[i] } else { r };
    }
    let end = r;
    PartialExpStatementWitnessOutput { end, end_square }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq12, Fr};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use num_bigint::BigUint;
    use rand::Rng;

    use crate::aggregation::fq12_generate_witness::{generate_witness_from_bits, u8_to_bools};

    use super::generate_witness;

    #[test]
    fn test_generate_witness() {
        let mut rng = rand::thread_rng();
        let p = Fq12::rand(&mut rng);
        let x = Fr::rand(&mut rng);

        let x_biguint: BigUint = x.into();
        let result = p.pow(&x_biguint.to_u64_digits());

        let statement = generate_witness(p, x, 4);
        let end = statement.last().unwrap().end;

        assert_eq!(end, result);
    }

    #[test]
    fn test_generate_witness_from_bits() {
        let mut rng = rand::thread_rng();
        let p = Fq12::rand(&mut rng);
        let x: u8 = rng.gen();
        let x_biguint: BigUint = x.into();
        let bits = u8_to_bools(x);
        let result = p.pow(&x_biguint.to_u64_digits());

        let statements = generate_witness_from_bits(p, bits, 4);
        let end = statements.last().unwrap().end;

        assert_eq!(end, result);
    }
}
