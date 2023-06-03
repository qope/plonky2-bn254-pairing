use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::target::BoolTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::fields::fq12_target::Fq12Target;

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

    use crate::fields::fq12_target::Fq12Target;

    use super::{verify_partial_exp_statement, PartialExpStatement};

    type F = GoldilocksField;
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;

    pub struct PartialExpStatementWitnessInput {
        bits: Vec<bool>,
        start: Fq12,
        start_square: Fq12,
    }

    pub struct PartialExpStatementWitnessOutput {
        end: Fq12,
        end_square: Fq12,
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
