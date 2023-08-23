#![allow(non_snake_case)]
use std::{ops::Div, vec};

use ark_bn254::{Fq, Fq12, Fq2};
use ark_ff::Field;
use ark_std::Zero;
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::One;

use plonky2_bn254::fields::native::MyFq12;

use crate::miller_loop_native::conjugate_fp2;

pub const BN_X: u64 = 4965661367192848881;

pub fn frobenius_map(a: MyFq12, power: usize) -> MyFq12 {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus = neg_one + BigUint::from(1u64);
    assert_eq!(modulus.clone() % 4u64, BigUint::from(3u64));
    assert_eq!(modulus % 6u64, BigUint::from(1u64));
    let pow = power % 12;

    let mut out_fp2 = Vec::with_capacity(6);

    for i in 0..6 {
        let frob_coeff = frob_coeffs(pow).pow([i as u64]);
        let mut a_fp2 = Fq2::new(a.coeffs[i].clone(), a.coeffs[i + 6].clone());
        if pow % 2 != 0 {
            a_fp2 = conjugate_fp2(a_fp2);
        }

        if frob_coeff == Fq2::one() {
            out_fp2.push(a_fp2);
        } else if frob_coeff.c1 == Fq::zero() {
            let frob_fixed = Fq2::new(frob_coeff.c0, Fq::zero());
            let out_nocarry = a_fp2 * frob_fixed;
            out_fp2.push(out_nocarry);
        } else {
            let frob_fixed = Fq2::new(frob_coeff.c0, frob_coeff.c1);
            out_fp2.push(a_fp2 * frob_fixed);
        }
    }

    let out_coeffs = out_fp2
        .iter()
        .map(|x| x.c0.clone())
        .chain(out_fp2.iter().map(|x| x.c1.clone()))
        .collect_vec();

    MyFq12 {
        coeffs: out_coeffs.try_into().unwrap(),
    }
}

pub fn pow(a: MyFq12, exp: Vec<u64>) -> MyFq12 {
    let mut res = a.clone();
    let mut is_started = false;
    let naf = get_naf(exp);

    for &z in naf.iter().rev() {
        if is_started {
            res = res * res;
        }

        if z != 0 {
            assert!(z == 1 || z == -1);
            if is_started {
                res = if z == 1 {
                    res * a
                } else {
                    let res_fp12: Fq12 = res.into();
                    let a_fp12: Fq12 = a.into();
                    let divided = res_fp12 / a_fp12;
                    divided.into()
                };
            } else {
                assert_eq!(z, 1);
                is_started = true;
            }
        }
    }
    res
}

pub fn get_naf(mut exp: Vec<u64>) -> Vec<i8> {
    // https://en.wikipedia.org/wiki/Non-adjacent_form
    // NAF for exp:
    let mut naf: Vec<i8> = Vec::with_capacity(64 * exp.len());
    let len = exp.len();

    // generate the NAF for exp
    for idx in 0..len {
        let mut e: u64 = exp[idx];
        for _ in 0..64 {
            if e & 1 == 1 {
                let z = 2i8 - (e % 4) as i8;
                e /= 2;
                if z == -1 {
                    e += 1;
                }
                naf.push(z);
            } else {
                naf.push(0);
                e /= 2;
            }
        }
        if e != 0 {
            assert_eq!(e, 1);
            let mut j = idx + 1;
            while j < exp.len() && exp[j] == u64::MAX {
                exp[j] = 0;
                j += 1;
            }
            if j < exp.len() {
                exp[j] += 1;
            } else {
                exp.push(1);
            }
        }
    }
    if exp.len() != len {
        assert_eq!(len, exp.len() + 1);
        assert!(exp[len] == 1);
        naf.push(1);
    }
    naf
}

pub fn hard_part_BN(m: MyFq12) -> MyFq12 {
    let mp = frobenius_map(m, 1);
    let mp2 = frobenius_map(m, 2);
    let mp3 = frobenius_map(m, 3);

    let mp2_mp3 = mp2 * mp3;
    let y0 = mp * mp2_mp3;
    let y1 = conjugate_fp12(m);
    let mx = pow(m, vec![BN_X]);
    let mxp = frobenius_map(mx, 1);
    let mx2 = pow(mx.clone(), vec![BN_X]);
    let mx2p = frobenius_map(mx2, 1);
    let y2 = frobenius_map(mx2, 2);
    let y5 = conjugate_fp12(mx2);
    let mx3 = pow(mx2, vec![BN_X]);
    let mx3p = frobenius_map(mx3, 1);

    let y3 = conjugate_fp12(mxp);
    let mx_mx2p = mx * mx2p;
    let y4 = conjugate_fp12(mx_mx2p);
    let mx3_mx3p = mx3 * mx3p;
    let y6 = conjugate_fp12(mx3_mx3p);

    let mut T0 = y6 * y6;
    T0 = T0 * y4;
    T0 = T0 * y5;

    let mut T1 = y3 * y5;
    T1 = T1 * T0;
    T0 = y2 * T0;
    T1 = T1 * T1;
    T1 = T1 * T0;
    T1 = T1 * T1;
    T0 = T1 * y1;
    T1 = T1 * y0;
    T0 = T0 * T0;
    T0 = T0 * T1;

    T0
}

fn conjugate_fp12(a: MyFq12) -> MyFq12 {
    let coeffs: Vec<Fq> = a
        .coeffs
        .iter()
        .enumerate()
        .map(|(i, c)| if i % 2 == 0 { c.clone() } else { -c.clone() })
        .collect();
    MyFq12 {
        coeffs: coeffs.try_into().unwrap(),
    }
}

pub fn frob_coeffs(index: usize) -> Fq2 {
    let neg_one: BigUint = Fq::from(-1).into();
    let modulus = neg_one + 1u64;

    let num: BigUint = modulus.pow(index as u32) - 1u64;
    let k: BigUint = num.div(6u64);

    let c = Fq2::new(Fq::from(9), Fq::one());
    c.pow(k.to_u64_digits())
}

// out = in^{ (q^6 - 1)*(q^2 + 1) }
pub fn easy_part<'v>(a: MyFq12) -> MyFq12 {
    let f1 = conjugate_fp12(a);
    let f2 = {
        let f1_fp12: Fq12 = f1.into();
        let a_fp12: Fq12 = a.into();
        let divided = f1_fp12 / a_fp12;
        divided.into()
    };
    let f3 = frobenius_map(f2, 2);
    let f = f3 * f2;
    f
}

// out = in^{(q^12 - 1)/r}
pub fn final_exp(a: MyFq12) -> MyFq12 {
    let f0 = easy_part(a);

    let f = hard_part_BN(f0);
    f
}

#[cfg(test)]
mod tests {
    use std::ops::Mul;

    use ark_bn254::{Fr, G1Affine, G2Affine};
    use ark_ec::AffineRepr;

    use crate::miller_loop_native::{miller_loop, multi_miller_loop};
    use plonky2_bn254::fields::debug_tools::print_ark_fq;

    use super::final_exp;

    #[test]
    fn test_pairing_final() {
        let Q = G2Affine::generator();
        let P = G1Affine::generator();
        let m = miller_loop(&Q, &P);
        let r = final_exp(m);
        print_ark_fq(r.coeffs[0], "r.coeffs[0]".to_string());
    }

    #[test]
    fn test_to_one() {
        let G1 = G1Affine::generator();
        let G2 = G2Affine::generator();

        let s = Fr::from(5u64);
        let t = Fr::from(6u64);
        let P0: G1Affine = G1.mul(s).into();
        let Q0: G2Affine = G2.mul(t).into();

        let P1: G1Affine = G1.mul(s * t).into();
        let Q1 = -G2;

        let m = multi_miller_loop(vec![(&P0, &Q0), (&P1, &Q1)]);

        let m0 = miller_loop(&Q0, &P0);
        let m1 = miller_loop(&Q1, &P1);

        assert_eq!(m, m0 * m1);
        let r0 = final_exp(m0);
        let r1 = final_exp(m1);
        let r_sep = r0 * r1;
        let r_mul = final_exp(m);
        assert_eq!(r_sep, r_mul);
    }
}
