use ark_bn254::Fq12;
use itertools::Itertools;
use num_traits::One;

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

pub fn generate_witness(
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
    use ark_bn254::Fq12;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use num_bigint::BigUint;
    use rand::Rng;

    use crate::aggregation::{fq12_exp::biguint_to_bits, fq12_exp_witness::generate_witness};

    #[test]
    fn test_generate_witness() {
        let mut rng = rand::thread_rng();
        let p = Fq12::rand(&mut rng);
        let x: u8 = rng.gen();
        let x_biguint: BigUint = x.into();
        let bits = biguint_to_bits(&x_biguint);
        let result = p.pow(&x_biguint.to_u64_digits());

        let statements = generate_witness(p, bits, 4);
        let end = statements.last().unwrap().end;

        assert_eq!(end, result);
    }
}
