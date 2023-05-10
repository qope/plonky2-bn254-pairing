#![allow(non_snake_case)]
use ark_bn254::{Fq, Fq2};
use ark_ff::{Field, One, Zero};
use itertools::Itertools;
use num_bigint::BigUint;

use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::fields::{fq12_target::Fq12Target, fq2_target::Fq2Target};

use crate::pairing::final_exp_native::{frob_coeffs, get_naf, BN_X};

pub fn frobenius_map<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
    power: usize,
) -> Fq12Target<F, D> {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus = neg_one + BigUint::from(1u64);
    assert_eq!(modulus.clone() % 4u64, BigUint::from(3u64));
    assert_eq!(modulus % 6u64, BigUint::from(1u64));
    let pow = power % 12;

    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        let frob_coeff = frob_coeffs(pow).pow([i as u64]);
        let mut a_fp2 = Fq2Target {
            coeffs: [a.coeffs[i].clone(), a.coeffs[i + 6].clone()],
        };
        if pow % 2 != 0 {
            a_fp2 = a_fp2.conjugate(builder);
        }
        if frob_coeff == Fq2::one() {
            out_fp2.push(a_fp2);
        } else if frob_coeff.c1 == Fq::zero() {
            let frob_fixed = Fq2::new(frob_coeff.c0, Fq::zero());
            let frob_fixed_t = Fq2Target::constant(builder, frob_fixed);
            let out_nocarry = a_fp2.mul(builder, &frob_fixed_t);
            out_fp2.push(out_nocarry);
        } else {
            let frob_fixed = Fq2::new(frob_coeff.c0, frob_coeff.c1);
            let frob_fixed_t = Fq2Target::constant(builder, frob_fixed);
            let out_nocarry = a_fp2.mul(builder, &frob_fixed_t);
            out_fp2.push(out_nocarry);
        }
    }
    let out_coeffs = out_fp2
        .iter()
        .map(|x| x.coeffs[0].clone())
        .chain(out_fp2.iter().map(|x| x.coeffs[1].clone()))
        .collect_vec();

    Fq12Target {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

pub fn pow<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
    exp: Vec<u64>,
) -> Fq12Target<F, D> {
    let mut res = a.clone();
    let mut is_started = false;
    let naf = get_naf(exp);

    for &z in naf.iter().rev() {
        if is_started {
            res = res.mul(builder, &res);
        }

        if z != 0 {
            assert!(z == 1 || z == -1);
            if is_started {
                res = if z == 1 {
                    res.mul(builder, a)
                } else {
                    res.div(builder, a)
                };
            } else {
                assert_eq!(z, 1);
                is_started = true;
            }
        }
    }
    res
}

pub fn hard_part_BN<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    m: &Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let mp = frobenius_map(builder, m, 1);
    let mp2 = frobenius_map(builder, m, 2);
    let mp3 = frobenius_map(builder, m, 3);

    // let mp2_mp3 = mp2 * mp3;
    // let y0 = mp * mp2_mp3;
    // let y1 = conjugate_fp12(m);
    let mp2_mp3 = mp2.mul(builder, &mp3);
    let y0 = mp.mul(builder, &mp2_mp3);
    let y1 = m.confugate(builder);

    let mx = pow(builder, m, vec![BN_X]);

    let mxp = frobenius_map(builder, &mx, 1);
    let mx2 = pow(builder, &mx, vec![BN_X]);
    let mx2p = frobenius_map(builder, &mx2, 1);
    let y2 = frobenius_map(builder, &mx2, 2);
    let y5 = mx2.confugate(builder);
    let mx3 = pow(builder, &mx2, vec![BN_X]);
    let mx3p = frobenius_map(builder, &mx3, 1);

    // let y3 = conjugate_fp12(mxp);
    // let mx_mx2p = mx * mx2p;
    // let y4 = conjugate_fp12(mx_mx2p);
    // let mx3_mx3p = mx3 * mx3p;
    // let y6 = conjugate_fp12(mx3_mx3p);
    let y3 = mxp.confugate(builder);
    let mx_mx2p = mx.mul(builder, &mx2p);
    let y4 = mx_mx2p.confugate(builder);
    let mx3_mx3p = mx3.mul(builder, &mx3p);
    let y6 = mx3_mx3p.confugate(builder);

    // let mut T0 = y6 * y6;
    // T0 = T0 * y4;
    // T0 = T0 * y5;
    let mut T0 = y6.mul(builder, &y6);
    T0 = T0.mul(builder, &y4);
    T0 = T0.mul(builder, &y5);

    // let mut T1 = y3 * y5;
    // T1 = T1 * T0;
    // T0 = y2 * T0;
    // T1 = T1 * T1;
    // T1 = T1 * T0;
    // T1 = T1 * T1;
    // T0 = T1 * y1;
    // T1 = T1 * y0;
    // T0 = T0 * T0;
    // T0 = T0 * T1;
    let mut T1 = y3.mul(builder, &y5);
    T1 = T1.mul(builder, &T0);
    T0 = y2.mul(builder, &T0);
    T1 = T1.mul(builder, &T1);
    T1 = T1.mul(builder, &T0);
    T1 = T1.mul(builder, &T1);
    T0 = T1.mul(builder, &y1);
    T1 = T1.mul(builder, &y0);
    T0 = T0.mul(builder, &T0);
    T0 = T0.mul(builder, &T1);

    T0
    // Fq12Target::new(builder)
}

pub fn easy_part<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let f1 = a.confugate(builder);
    let f2 = f1.div(builder, &a);
    let f3 = frobenius_map(builder, &f2, 2);
    let f = f3.mul(builder, &f2);
    f
}

pub fn final_exp<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: Fq12Target<F, D>,
) -> Fq12Target<F, D> {
    let f0 = easy_part(builder, &a);
    let f = hard_part_BN(builder, &f0);
    f
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq12, G1Affine, G2Affine};
    use ark_std::UniformRand;
    use rand::Rng;

    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::pairing::miller_loop_native::miller_loop as miller_loop_native;
    use crate::pairing::{
        final_exp_native::{final_exp as final_exp_native, frobenius_map as frobenius_map_native},
        final_exp_target::final_exp,
    };
    use crate::{fields::fq12_target::Fq12Target, pairing::final_exp_target::frobenius_map};

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_final_exp() {
        let rng = &mut rand::thread_rng();
        let Q = G2Affine::rand(rng);
        let P = G1Affine::rand(rng);
        let input = miller_loop_native(&Q, &P);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let input_t = Fq12Target::constant(&mut builder, input.into());
        let output = final_exp(&mut builder, input_t);
        let output_expected = final_exp_native(input);

        let output_expected_t = Fq12Target::constant(&mut builder, output_expected.into());

        Fq12Target::connect(&mut builder, &output, &output_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_frobenius_map() {
        let rng = &mut rand::thread_rng();
        let power = rng.gen();
        let a = Fq12::rand(rng);
        let b_expected = frobenius_map_native(a.into(), power);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = Fq12Target::constant(&mut builder, a);
        let b_t = frobenius_map(&mut builder, &a_t, power);
        let b_expected_t = Fq12Target::constant(&mut builder, b_expected.into());

        Fq12Target::connect(&mut builder, &b_t, &b_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }
}
