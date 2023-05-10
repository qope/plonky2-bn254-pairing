#![allow(non_snake_case)]
use crate::curves::{g1curve_target::G1Target, g2curve_target::G2Target};
use crate::fields::fq12_target::Fq12Target;
use crate::fields::{debug_tools::print_fq_target, fq2_target::Fq2Target, fq_target::FqTarget};
use crate::pairing::miller_loop_native::SIX_U_PLUS_2_NAF;
use ark_bn254::{Fq, Fq2};
use ark_ff::Field;
use ark_std::One;
use num_bigint::BigUint;
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField,
    plonk::circuit_builder::CircuitBuilder,
};

const XI_0: usize = 9;

pub fn sparse_line_function_unequal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: (&G2Target<F, D>, &G2Target<F, D>),
    P: &G1Target<F, D>,
) -> Vec<Option<Fq2Target<F, D>>> {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (x, y) = (&P.x, &P.y);
    let y1_minus_y2 = y_1.sub(builder, &y_2);
    let x2_minus_x1 = x_2.sub(builder, &x_1);
    let x1y2 = x_1.mul(builder, &y_2);
    let x2y1 = x_2.mul(builder, &y_1);
    let out3 = y1_minus_y2.mul_scalar(builder, &x);
    let out2 = x2_minus_x1.mul_scalar(builder, &y);
    let out5 = x1y2.sub(builder, &x2y1);

    vec![None, None, Some(out2), Some(out3), None, Some(out5)]
}

pub fn sparse_line_function_equal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
) -> Vec<Option<Fq2Target<F, D>>> {
    let (x, y) = (&Q.x, &Q.y);
    let x_sq = x.mul(builder, &x);
    let x_cube = x_sq.mul(builder, &x);
    let three_x_cu = x_cube.mul_scalar_const(builder, &Fq::from(3));
    let y_sq = y.mul(builder, &y);
    let two_y_sq = y_sq.mul_scalar_const(builder, &Fq::from(2));
    let out0_left = three_x_cu.sub(builder, &two_y_sq);
    let out0 = out0_left.mul_w6::<XI_0>(builder);
    let x_sq_px = x_sq.mul_scalar(builder, &P.x);
    let out4 = x_sq_px.mul_scalar_const(builder, &Fq::from(-3));
    let y_py = y.mul_scalar(builder, &P.y);
    let out3 = y_py.mul_scalar_const(builder, &Fq::from(2));

    vec![Some(out0), None, None, Some(out3), Some(out4), None]
}

pub fn sparse_fp12_multiply<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &Fq12Target<F, D>,
    b: Vec<Option<Fq2Target<F, D>>>,
) -> Fq12Target<F, D> {
    let mut a_fp2_coeffs = Vec::with_capacity(6);
    for i in 0..6 {
        a_fp2_coeffs.push(Fq2Target {
            coeffs: [a.coeffs[i].clone(), a.coeffs[i + 6].clone()],
        });
    }
    let mut prod_2d: Vec<Option<Fq2Target<F, D>>> = vec![None; 11];
    for i in 0..6 {
        for j in 0..6 {
            prod_2d[i + j] = match (prod_2d[i + j].clone(), &a_fp2_coeffs[i], b[j].as_ref()) {
                (a, _, None) => a,
                (None, a, Some(b)) => {
                    let ab = a.mul(builder, b);
                    Some(ab)
                }
                (Some(a), b, Some(c)) => {
                    let bc = b.mul(builder, c);
                    let out = a.add(builder, &bc);
                    Some(out)
                }
            };
        }
    }
    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        let prod = if i != 5 {
            let eval_w6 = prod_2d[i + 6].as_ref().map(|a| a.mul_w6::<XI_0>(builder));
            match (prod_2d[i].as_ref(), eval_w6) {
                (None, b) => b.unwrap(), // Our current use cases of 235 and 034 sparse multiplication always result in non-None value
                (Some(a), None) => a.clone(),
                (Some(a), Some(b)) => a.add(builder, &b),
            }
        } else {
            prod_2d[i].clone().unwrap()
        };
        out_fp2.push(prod);
    }
    let mut out_coeffs = Vec::with_capacity(12);
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.coeffs[0].clone());
    }
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.coeffs[1].clone());
    }

    Fq12Target {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

pub fn fp12_multiply_with_line_unequal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    g: &Fq12Target<F, D>,
    Q: (&G2Target<F, D>, &G2Target<F, D>),
    P: &G1Target<F, D>,
) -> Fq12Target<F, D> {
    let line = sparse_line_function_unequal(builder, Q, P);
    sparse_fp12_multiply(builder, g, line)
}

pub fn fp12_multiply_with_line_equal<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    g: &Fq12Target<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
) -> Fq12Target<F, D> {
    let line = sparse_line_function_equal(builder, Q, P);
    sparse_fp12_multiply(builder, g, line)
}

pub fn miller_loop_BN<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
    pseudo_binary_encoding: &[i8],
) -> Fq12Target<F, D> {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert!(pseudo_binary_encoding[i] == 1 || pseudo_binary_encoding[i] == -1);
    let mut R = if pseudo_binary_encoding[i] == 1 {
        Q.clone()
    } else {
        Q.neg(builder)
    };
    i -= 1;

    // initialize the first line function into Fq12 point
    let sparse_f = sparse_line_function_equal(builder, &R, P);
    assert_eq!(sparse_f.len(), 6);

    let zero_fp = FqTarget::constant(builder, Fq::ZERO);
    let mut f_coeffs = Vec::with_capacity(12);
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[0].clone());
        } else {
            f_coeffs.push(zero_fp.clone());
        }
    }
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.coeffs[1].clone());
        } else {
            f_coeffs.push(zero_fp.clone());
        }
    }

    let mut f = Fq12Target {
        coeffs: f_coeffs.try_into().unwrap(),
    };

    loop {
        if i != last_index - 1 {
            let f_sq = f.mul(builder, &f);
            f = fp12_multiply_with_line_equal(builder, &f_sq, &R, P);
        }

        R = R.double(builder);

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_Q = if pseudo_binary_encoding[i] == 1 {
                Q.clone()
            } else {
                Q.neg(builder)
            };
            f = fp12_multiply_with_line_unequal(builder, &f, (&R, &sign_Q), P);
            R = R.add(builder, &sign_Q);
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(9), Fq::one()).pow(k.to_u64_digits());
    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;
    let c2 = Fq2Target::constant(builder, c2);
    let c3 = Fq2Target::constant(builder, c3);

    let Q_1 = twisted_frobenius(builder, Q, c2.clone(), c3.clone());
    let neg_Q_2 = neg_twisted_frobenius(builder, &Q_1, c2.clone(), c3.clone());
    f = fp12_multiply_with_line_unequal(builder, &f, (&R, &Q_1), P);
    R = R.add(builder, &Q_1);
    f = fp12_multiply_with_line_unequal(builder, &f, (&R, &neg_Q_2), P);

    print_fq_target(builder, &f.coeffs[0], "final_f".to_string());

    f
}

pub fn multi_miller_loop_BN<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    pairs: Vec<(&G1Target<F, D>, &G2Target<F, D>)>,
    pseudo_binary_encoding: &[i8],
) -> Fq12Target<F, D> {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert_eq!(pseudo_binary_encoding[last_index], 1);

    let neg_b: Vec<G2Target<F, D>> = pairs.iter().map(|pair| pair.1.neg(builder)).collect();

    // initialize the first line function into Fq12 point
    let mut f = {
        let sparse_f = sparse_line_function_equal(builder, pairs[0].1, pairs[0].0);
        assert_eq!(sparse_f.len(), 6);

        let zero_fp = FqTarget::constant(builder, Fq::ZERO);
        let mut f_coeffs = Vec::with_capacity(12);
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.coeffs[0].clone());
            } else {
                f_coeffs.push(zero_fp.clone());
            }
        }
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.coeffs[1].clone());
            } else {
                f_coeffs.push(zero_fp.clone());
            }
        }
        Fq12Target {
            coeffs: f_coeffs.try_into().unwrap(),
        }
    };

    for &(a, b) in pairs.iter().skip(1) {
        f = fp12_multiply_with_line_equal(builder, &f, b, a);
    }

    i -= 1;
    let mut r = pairs.iter().map(|pair| pair.1.clone()).collect::<Vec<_>>();
    loop {
        if i != last_index - 1 {
            f = f.mul(builder, &f);
            for (r, &(a, _)) in r.iter().zip(pairs.iter()) {
                f = fp12_multiply_with_line_equal(builder, &f, r, a);
            }
        }
        for r in r.iter_mut() {
            *r = r.double(builder);
        }

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            for ((r, neg_b), &(a, b)) in r.iter_mut().zip(neg_b.iter()).zip(pairs.iter()) {
                let sign_b = if pseudo_binary_encoding[i] == 1 {
                    b
                } else {
                    neg_b
                };
                f = fp12_multiply_with_line_unequal(builder, &f, (r, sign_b), a);
                *r = r.add(builder, &sign_b);
            }
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(9), Fq::one()).pow(k.to_u64_digits());

    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;
    let c2 = Fq2Target::constant(builder, c2);
    let c3 = Fq2Target::constant(builder, c3);

    // finish multiplying remaining line functions outside the loop
    for (r, &(a, b)) in r.iter_mut().zip(pairs.iter()) {
        let b_1 = twisted_frobenius(builder, &b, c2.clone(), c3.clone());
        let neg_b_2 = neg_twisted_frobenius(builder, &b_1, c2.clone(), c3.clone());
        f = fp12_multiply_with_line_unequal(builder, &f, (r, &b_1), a);
        // *r = (r.clone() + b_1).into();
        *r = r.add(builder, &b_1);
        f = fp12_multiply_with_line_unequal(builder, &f, (r, &neg_b_2), a);
    }
    f
}

pub fn twisted_frobenius<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    c2: Fq2Target<F, D>,
    c3: Fq2Target<F, D>,
) -> G2Target<F, D> {
    let frob_x = Q.x.conjugate(builder);
    let frob_y = Q.y.conjugate(builder);
    let out_x = c2.mul(builder, &frob_x);
    let out_y = c3.mul(builder, &frob_y);
    G2Target::construct(out_x, out_y)
}

pub fn neg_twisted_frobenius<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    c2: Fq2Target<F, D>,
    c3: Fq2Target<F, D>,
) -> G2Target<F, D> {
    let frob_x = Q.x.conjugate(builder);
    let neg_frob_y = Q.y.neg_conjugate(builder);
    let out_x = c2.mul(builder, &frob_x);
    let out_y = c3.mul(builder, &neg_frob_y);
    G2Target::construct(out_x, out_y)
}

pub fn miller_loop<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    Q: &G2Target<F, D>,
    P: &G1Target<F, D>,
) -> Fq12Target<F, D> {
    miller_loop_BN(builder, Q, P, &SIX_U_PLUS_2_NAF)
}

pub fn multi_miller_loop<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    pairs: Vec<(&G1Target<F, D>, &G2Target<F, D>)>,
) -> Fq12Target<F, D> {
    multi_miller_loop_BN(builder, pairs, &SIX_U_PLUS_2_NAF)
}

#[cfg(test)]
mod tests {
    use ark_bn254::{G1Affine, G2Affine};
    use ark_std::UniformRand;
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use super::miller_loop;
    use crate::pairing::{
        miller_loop_native::{
            miller_loop as miller_loop_native, multi_miller_loop as multi_miller_loop_native,
        },
        miller_loop_target::multi_miller_loop,
    };
    use crate::{
        curves::{g1curve_target::G1Target, g2curve_target::G2Target},
        fields::fq12_target::Fq12Target,
    };

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_miller_loop_target() {
        let rng = &mut rand::thread_rng();
        let Q = G2Affine::rand(rng);
        let P = G1Affine::rand(rng);
        let r_expected = miller_loop_native(&Q, &P);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let Q_t = G2Target::constant(&mut builder, Q);
        let P_t = G1Target::constant(&mut builder, P);

        let r_t = miller_loop(&mut builder, &Q_t, &P_t);
        let r_expected_t = Fq12Target::constant(&mut builder, r_expected.into());

        Fq12Target::connect(&mut builder, &r_t, &r_expected_t);

        let pw = PartialWitness::<F>::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_multi_miller_loop_target() {
        let rng = &mut rand::thread_rng();
        let Q0 = G2Affine::rand(rng);
        let P0 = G1Affine::rand(rng);
        let Q1 = G2Affine::rand(rng);
        let P1 = G1Affine::rand(rng);

        let r_expected = multi_miller_loop_native(vec![(&P0, &Q0), (&P1, &Q1)]);

        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let Q0_t = G2Target::constant(&mut builder, Q0);
        let P0_t = G1Target::constant(&mut builder, P0);
        let Q1_t = G2Target::constant(&mut builder, Q1);
        let P1_t = G1Target::constant(&mut builder, P1);

        let r_t = multi_miller_loop(&mut builder, vec![(&P0_t, &Q0_t), (&P1_t, &Q1_t)]);
        let r_expected_t = Fq12Target::constant(&mut builder, r_expected.into());

        Fq12Target::connect(&mut builder, &r_t, &r_expected_t);

        let pw = PartialWitness::<F>::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }
}
