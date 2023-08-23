#![allow(non_snake_case)]

use ark_bn254::{Fq, Fq2, G1Affine, G2Affine};
use ark_ff::{Field, Fp2};
use ark_std::{One, Zero};
use num_bigint::BigUint;

use plonky2_bn254::fields::native::MyFq12;

fn sparse_line_function_unequal_native(
    Q: (&G2Affine, &G2Affine),
    P: &G1Affine,
) -> Vec<Option<Fq2>> {
    let (x_1, y_1) = (&Q.0.x, &Q.0.y);
    let (x_2, y_2) = (&Q.1.x, &Q.1.y);
    let (x, y) = (&P.x, &P.y);

    let y1_minus_y2 = y_1 - y_2;
    let x2_minus_x1 = x_2 - x_1;
    let x1y2 = x_1 * y_2;
    let x2y1 = x_2 * y_1;

    let out3 = y1_minus_y2 * Fq2::new(x.clone(), Fq::zero());
    let out2 = x2_minus_x1 * Fq2::new(y.clone(), Fq::zero());
    let out5 = x1y2 - x2y1;

    vec![None, None, Some(out2), Some(out3), None, Some(out5)]
}

fn sparse_line_function_equal_native(Q: &G2Affine, P: &G1Affine) -> Vec<Option<Fq2>> {
    let (x, y) = (&Q.x, &Q.y);
    let x_sq = x * x;
    let x_cube = x_sq * x;
    let three_x_cu = x_cube * Fq2::from(3);
    let y_sq = y * y;
    let two_y_sq = y_sq * Fq2::from(2);
    let out0_left = three_x_cu - two_y_sq;
    let out0 = out0_left * Fq2::new(Fq::from(9), Fq::one());
    let x_sq_px: Fq2 = x_sq * Fq2::new(P.x, Fq::zero());
    let out4 = x_sq_px * Fq2::from(-3);
    let y_py = y * Fq2::new(P.y, Fq::zero());
    let out3 = y_py * Fq2::from(2);
    vec![Some(out0), None, None, Some(out3), Some(out4), None]
}

fn sparse_fp12_multiply_native(a: &MyFq12, b: Vec<Option<Fq2>>) -> MyFq12 {
    let mut a_fp2_coeffs = Vec::with_capacity(6);
    for i in 0..6 {
        a_fp2_coeffs.push(Fq2::new(a.coeffs[i].clone(), a.coeffs[i + 6].clone()));
    }
    // a * b as element of Fp2[w] without evaluating w^6 = (XI_0 + u)
    let mut prod_2d: Vec<Option<Fq2>> = vec![None; 11];
    for i in 0..6 {
        for j in 0..6 {
            prod_2d[i + j] = match (prod_2d[i + j].clone(), &a_fp2_coeffs[i], b[j].as_ref()) {
                (a, _, None) => a,
                (None, a, Some(b)) => {
                    let ab = a * b;
                    Some(ab)
                }
                (Some(a), b, Some(c)) => {
                    let bc = b * c;
                    let out = a + bc;
                    Some(out)
                }
            };
        }
    }
    let mut out_fp2 = Vec::with_capacity(6);
    for i in 0..6 {
        let prod = if i != 5 {
            let eval_w6 = prod_2d[i + 6]
                .as_ref()
                .map(|a| a * Fq2::new(Fq::from(9), Fq::one()));
            match (prod_2d[i].as_ref(), eval_w6) {
                (None, b) => b.unwrap(),
                (Some(a), None) => a.clone(),
                (Some(a), Some(b)) => a + b,
            }
        } else {
            prod_2d[i].clone().unwrap()
        };
        out_fp2.push(prod);
    }

    let mut out_coeffs = Vec::with_capacity(12);
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.c0.clone());
    }
    for fp2_coeff in &out_fp2 {
        out_coeffs.push(fp2_coeff.c1.clone());
    }
    MyFq12 {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

fn fp12_multiply_with_line_unequal_native(
    g: &MyFq12,
    Q: (&G2Affine, &G2Affine),
    P: &G1Affine,
) -> MyFq12 {
    let line: Vec<Option<Fq2>> = sparse_line_function_unequal_native(Q, P);
    sparse_fp12_multiply_native(g, line)
}

fn fp12_multiply_with_line_equal_native(g: &MyFq12, Q: &G2Affine, P: &G1Affine) -> MyFq12 {
    let line: Vec<Option<Fq2>> = sparse_line_function_equal_native(Q, P);
    sparse_fp12_multiply_native(g, line)
}

fn miller_loop_BN_native(Q: &G2Affine, P: &G1Affine, pseudo_binary_encoding: &[i8]) -> MyFq12 {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert!(pseudo_binary_encoding[i] == 1 || pseudo_binary_encoding[i] == -1);
    let mut R = if pseudo_binary_encoding[i] == 1 {
        Q.clone()
    } else {
        -Q.clone()
    };
    i -= 1;

    // initialize the first line function into Fq12 point
    let sparse_f = sparse_line_function_equal_native(&R, P);
    assert_eq!(sparse_f.len(), 6);

    let zero_fp = Fq::zero();
    let mut f_coeffs = Vec::with_capacity(12);
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.c0);
        } else {
            f_coeffs.push(zero_fp);
        }
    }
    for coeff in &sparse_f {
        if let Some(fp2_point) = coeff {
            f_coeffs.push(fp2_point.c1);
        } else {
            f_coeffs.push(zero_fp);
        }
    }

    let mut f = MyFq12 {
        coeffs: f_coeffs.try_into().unwrap(),
    };

    loop {
        if i != last_index - 1 {
            let f_sq = f * f;
            f = fp12_multiply_with_line_equal_native(&f_sq, &R, P);
        }

        R = (R + R).into();

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            let sign_Q = if pseudo_binary_encoding[i] == 1 {
                Q.clone()
            } else {
                -Q.clone()
            };
            f = fp12_multiply_with_line_unequal_native(&f, (&R, &sign_Q), P);
            R = (R + sign_Q).into();
        }
        if i == 0 {
            break;
        }
        i -= 1;
    }
    let mut R: G2Affine = R;

    let neg_one: BigUint = Fq::from(-1).into();
    let k = neg_one / BigUint::from(6u32);
    let expected_c = Fq2::new(Fq::from(9), Fq::one()).pow(k.to_u64_digits());

    let c2 = expected_c * expected_c;
    let c3 = c2 * expected_c;

    let Q_1 = twisted_frobenius(Q, c2, c3);
    let neg_Q_2 = neg_twisted_frobenius(&Q_1, c2, c3);
    f = fp12_multiply_with_line_unequal_native(&f, (&R, &Q_1), P);
    R = (R + Q_1).into();
    f = fp12_multiply_with_line_unequal_native(&f, (&R, &neg_Q_2), P);

    f
}

fn multi_miller_loop_BN_native(
    pairs: Vec<(&G1Affine, &G2Affine)>,
    pseudo_binary_encoding: &[i8],
) -> MyFq12 {
    let mut i = pseudo_binary_encoding.len() - 1;
    while pseudo_binary_encoding[i] == 0 {
        i -= 1;
    }
    let last_index = i;
    assert_eq!(pseudo_binary_encoding[last_index], 1);

    let neg_b: Vec<G2Affine> = pairs.iter().map(|pair| -pair.1.clone()).collect();

    // initialize the first line function into Fq12 point
    let mut f = {
        let sparse_f = sparse_line_function_equal_native(pairs[0].1, pairs[0].0);
        assert_eq!(sparse_f.len(), 6);

        let zero_fp = Fq::zero();
        let mut f_coeffs = Vec::with_capacity(12);
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.c0);
            } else {
                f_coeffs.push(zero_fp);
            }
        }
        for coeff in &sparse_f {
            if let Some(fp2_point) = coeff {
                f_coeffs.push(fp2_point.c1);
            } else {
                f_coeffs.push(zero_fp);
            }
        }
        MyFq12 {
            coeffs: f_coeffs.try_into().unwrap(),
        }
    };

    for &(a, b) in pairs.iter().skip(1) {
        f = fp12_multiply_with_line_equal_native(&f, b, a);
    }

    i -= 1;
    let mut r = pairs.iter().map(|pair| pair.1.clone()).collect::<Vec<_>>();
    loop {
        if i != last_index - 1 {
            f = f * f;
            for (r, &(a, _)) in r.iter().zip(pairs.iter()) {
                f = fp12_multiply_with_line_equal_native(&f, r, a);
            }
        }
        for r in r.iter_mut() {
            *r = (r.clone() + r.clone()).into();
        }

        assert!(pseudo_binary_encoding[i] <= 1 && pseudo_binary_encoding[i] >= -1);
        if pseudo_binary_encoding[i] != 0 {
            for ((r, neg_b), &(a, b)) in r.iter_mut().zip(neg_b.iter()).zip(pairs.iter()) {
                let sign_b = if pseudo_binary_encoding[i] == 1 {
                    b
                } else {
                    neg_b
                };
                f = fp12_multiply_with_line_unequal_native(&f, (r, sign_b), a);
                *r = (r.clone() + sign_b.clone()).into();
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

    // finish multiplying remaining line functions outside the loop
    for (r, &(a, b)) in r.iter_mut().zip(pairs.iter()) {
        let b_1 = twisted_frobenius(b, c2, c3);
        let neg_b_2 = neg_twisted_frobenius(&b_1, c2, c3);
        f = fp12_multiply_with_line_unequal_native(&f, (r, &b_1), a);
        *r = (r.clone() + b_1).into();
        f = fp12_multiply_with_line_unequal_native(&f, (r, &neg_b_2), a);
    }
    f
}

pub fn conjugate_fp2(x: Fq2) -> Fq2 {
    Fp2 {
        c0: x.c0,
        c1: -x.c1,
    }
}

pub fn neg_conjugate_fp2(x: Fq2) -> Fq2 {
    Fp2 {
        c0: -x.c0,
        c1: x.c1,
    }
}

fn twisted_frobenius(Q: &G2Affine, c2: Fq2, c3: Fq2) -> G2Affine {
    let frob_x = conjugate_fp2(Q.x);
    let frob_y = conjugate_fp2(Q.y);
    let out_x = c2 * frob_x;
    let out_y = c3 * frob_y;
    G2Affine::new(out_x, out_y)
}

fn neg_twisted_frobenius(Q: &G2Affine, c2: Fq2, c3: Fq2) -> G2Affine {
    let frob_x = conjugate_fp2(Q.x);
    let neg_frob_y = neg_conjugate_fp2(Q.y);
    let out_x = c2 * frob_x;
    let out_y = c3 * neg_frob_y;
    G2Affine::new(out_x, out_y)
}

pub const SIX_U_PLUS_2_NAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0,
    1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0,
    0, 1, 0, 1, 1,
];

pub fn miller_loop_native(Q: &G2Affine, P: &G1Affine) -> MyFq12 {
    miller_loop_BN_native(Q, P, &SIX_U_PLUS_2_NAF)
}

pub fn multi_miller_loop_native(pairs: Vec<(&G1Affine, &G2Affine)>) -> MyFq12 {
    multi_miller_loop_BN_native(pairs, &SIX_U_PLUS_2_NAF)
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fq12, G1Affine, G2Affine};
    use ark_ec::{pairing::Pairing, AffineRepr};
    use ark_std::UniformRand;

    use super::{miller_loop_native, multi_miller_loop_native};

    #[test]
    fn test_multi_miller_loop_native() {
        let rng = &mut rand::thread_rng();
        let P0 = G1Affine::rand(rng);
        let P1 = G1Affine::rand(rng);
        let Q0 = G2Affine::rand(rng);
        let Q1 = G2Affine::rand(rng);
        let r0 = miller_loop_native(&Q0, &P0);
        let r1 = miller_loop_native(&Q1, &P1);
        let r_expected = r0 * r1;
        let r = multi_miller_loop_native(vec![(&P0, &Q0), (&P1, &Q1)]);
        assert_eq!(r, r_expected);
    }

    #[test]
    fn test_miller_loop_comparison() {
        let mock_pairing = |p: G1Affine, q: G2Affine| -> Fq12 {
            let r0: Fq12 = Bn254::miller_loop(G1Affine::generator(), G2Affine::generator())
                .0
                .into();
            let r1: Fq12 =
                miller_loop_native(&G2Affine::generator(), &G1Affine::generator()).into();
            let r: Fq12 = miller_loop_native(&q, &p).into();
            r * r0 / r1
        };

        let mut rng = rand::thread_rng();
        let P0 = G1Affine::rand(&mut rng);
        let P1 = G2Affine::rand(&mut rng);
        let r: Fq12 = Bn254::miller_loop(P0, P1).0;
        let r_native = mock_pairing(P0, P1);
        assert_eq!(r, r_native);
    }

    // #[test]
    // fn test_pairing() {
    //     use bn::{pairing, AffineG1, AffineG2, Fq, Fq2, G1};

    //     let g1_generator = G1Affine::generator();
    //     let g2_generator = G2Affine::generator();

    //     let p = AffineG1::new(Fq::one(), Fq::from_str("2").unwrap()).unwrap();

    //     let x_c0 = BigUint::from(g2_generator.x.c0).to_str_radix(10);
    //     let x_c1 = BigUint::from(g2_generator.x.c1).to_str_radix(10);
    //     let y_c0 = BigUint::from(g2_generator.y.c0).to_str_radix(10);
    //     let y_c1 = BigUint::from(g2_generator.y.c1).to_str_radix(10);
    //     let x = Fq2::new(Fq::from_str(&x_c0).unwrap(), Fq::from_str(&x_c1).unwrap());
    //     let y = Fq2::new(Fq::from_str(&y_c0).unwrap(), Fq::from_str(&y_c1).unwrap());
    //     let q = AffineG2::new(x, y).unwrap();
    //     let r = pairing(p.into(), q.into());
    //     // r
    //     // dbg!(r);
    // }
}
