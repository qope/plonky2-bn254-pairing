use ark_bn254::Fq;
use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::{extension::Extendable, types::PrimeField64},
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartitionWitness, Witness},
    },
    plonk::circuit_builder::CircuitBuilder,
};

use crate::fields::fq_target::FqTarget;

use super::native::MyFq12;

#[derive(Debug, Clone)]
struct FqPrintGenerator {
    targets: Vec<Target>,
    annotation: String,
}

impl<F: PrimeField64> SimpleGenerator<F> for FqPrintGenerator {
    fn dependencies(&self) -> Vec<Target> {
        self.targets.clone()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, _out_buffer: &mut GeneratedValues<F>) {
        let values = self
            .targets
            .iter()
            .cloned()
            .map(|x| witness.get_target(x))
            .collect_vec();
        let values_u32: Vec<u32> = values
            .iter()
            .cloned()
            .map(|x| x.to_canonical_u64() as u32)
            .collect_vec();
        let values_biguint = BigUint::from_slice(&values_u32);
        let values_hex = hex::encode(values_biguint.to_bytes_be());
        println!("{}: {}", self.annotation, values_hex);
    }
}
pub fn print_fq_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: &FqTarget<F, D>,
    annotation: String,
) {
    let targets = x
        .target
        .value
        .limbs
        .iter()
        .cloned()
        .map(|x| x.0)
        .collect_vec();
    let generator = FqPrintGenerator {
        targets,
        annotation,
    };
    builder.add_simple_generator(generator);
}

pub fn print_ark_fq(x: Fq, annotation: String) {
    let values_biguint: BigUint = x.into();
    let values_hex = hex::encode(values_biguint.to_bytes_be());
    println!("{}: {}", annotation, values_hex);
}

pub fn ark_fq_to_string(x: &Fq) -> String {
    let values_biguint: BigUint = x.clone().into();
    let values_hex = hex::encode(values_biguint.to_bytes_be());
    values_hex
}

pub fn print_fq12(anon: &str, a: &MyFq12) {
    a.coeffs
        .iter()
        .enumerate()
        .map(|(i, x)| println!("{} {}: {}", anon, i, ark_fq_to_string(x)))
        .for_each(drop);
}

pub fn restore_fq(values_hex: String) -> Fq {
    let values_biguint = BigUint::from_bytes_be(&hex::decode(values_hex).unwrap());
    let values: Fq = values_biguint.into();
    values
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq, G2Affine};
    use ark_ec::AffineRepr;
    use ark_std::UniformRand;
    use num_bigint::BigUint;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::fields::fq_target::FqTarget;

    use super::{print_ark_fq, print_fq_target};

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_debug_print() {
        let gen = G2Affine::generator();
        let x0 = gen.x.c0;
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x0_t = FqTarget::constant(&mut builder, x0);
        print_fq_target(&mut builder, &x0_t, "x0_t".to_string());
        print_ark_fq(x0, "x0".to_string());
        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_back_forward() {
        let rng = &mut rand::thread_rng();
        let x = Fq::rand(rng);
        let values_biguint: BigUint = x.into();
        let values_hex = hex::encode(values_biguint.to_bytes_be());

        let y_biguint = BigUint::from_bytes_be(&hex::decode(values_hex).unwrap());
        let y: Fq = y_biguint.into();
        assert_eq!(x, y);
    }
}
