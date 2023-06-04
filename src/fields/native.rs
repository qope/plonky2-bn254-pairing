use std::ops::{Add, Mul};

use ark_bn254::{Fq, Fq12, Fq2, Fq6};
use ark_ff::{BigInt, PrimeField};
use ark_std::Zero;
use num_bigint::BigUint;

use crate::pairing::final_exp_native::get_naf;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MyFq12 {
    pub coeffs: [Fq; 12],
}

// impl from trait
impl From<Fq12> for MyFq12 {
    fn from(fq12: Fq12) -> Self {
        let c0: Fq6 = fq12.c0;
        let c1: Fq6 = fq12.c1;

        let c00 = c0.c0;
        let c01 = c0.c1;
        let c02 = c0.c2;
        let c10 = c1.c0;
        let c11 = c1.c1;
        let c12 = c1.c2;

        let c000 = c00.c0; // w^0 u^0
        let c001 = c00.c1; // w^0 u^1
        let c010 = c01.c0; // w^2 u^0
        let c011 = c01.c1; // w^2 u^1
        let c020 = c02.c0; // w^4 u^0
        let c021 = c02.c1; // w^4 u^1
        let c100 = c10.c0; // w^1 u^0
        let c101 = c10.c1; // w^1 u^1
        let c110 = c11.c0; // w^3 u^0
        let c111 = c11.c1; // w^3 u^1
        let c120 = c12.c0; // w^5 u^0
        let c121 = c12.c1; // w^5 u^1

        let coeffs = [
            c000, c100, c010, c110, c020, c120, c001, c101, c011, c111, c021, c121,
        ];
        Self { coeffs }
    }
}

// from myfq12 to fq12
impl From<MyFq12> for Fq12 {
    fn from(fq12: MyFq12) -> Self {
        let coeffs = fq12.coeffs;
        let c000 = coeffs[0]; // w^0 u^0
        let c001 = coeffs[6]; // w^0 u^1
        let c010 = coeffs[2]; // w^2 u^0
        let c011 = coeffs[8]; // w^2 u^1
        let c020 = coeffs[4]; // w^4 u^0
        let c021 = coeffs[10]; // w^4 u^1
        let c100 = coeffs[1]; // w^1 u^0
        let c101 = coeffs[7]; // w^1 u^1
        let c110 = coeffs[3]; // w^3 u^0
        let c111 = coeffs[9]; // w^3 u^1
        let c120 = coeffs[5]; // w^5 u^0
        let c121 = coeffs[11]; // w^5 u^1

        let c0 = Fq6::new(
            Fq2::new(c000, c001),
            Fq2::new(c010, c011),
            Fq2::new(c020, c021),
        );

        let c1 = Fq6::new(
            Fq2::new(c100, c101),
            Fq2::new(c110, c111),
            Fq2::new(c120, c121),
        );
        Fq12::new(c0, c1)
    }
}

impl Add for MyFq12 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut coeffs = [Fq::zero(); 12];
        for i in 0..12 {
            coeffs[i] = self.coeffs[i] + rhs.coeffs[i];
        }
        Self { coeffs }
    }
}

impl Mul for MyFq12 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let a = self;
        let b = rhs;
        let mut a0b0_coeffs = Vec::with_capacity(11);
        let mut a0b1_coeffs = Vec::with_capacity(11);
        let mut a1b0_coeffs = Vec::with_capacity(11);
        let mut a1b1_coeffs = Vec::with_capacity(11);
        for i in 0..6 {
            for j in 0..6 {
                let coeff00 = a.coeffs[i] * b.coeffs[j];
                let coeff01 = a.coeffs[i] * b.coeffs[j + 6];
                let coeff10 = a.coeffs[i + 6] * b.coeffs[j];
                let coeff11 = a.coeffs[i + 6] * b.coeffs[j + 6];
                if i + j < a0b0_coeffs.len() {
                    a0b0_coeffs[i + j] += coeff00;
                    a0b1_coeffs[i + j] += coeff01;
                    a1b0_coeffs[i + j] += coeff10;
                    a1b1_coeffs[i + j] += coeff11;
                } else {
                    a0b0_coeffs.push(coeff00);
                    a0b1_coeffs.push(coeff01);
                    a1b0_coeffs.push(coeff10);
                    a1b1_coeffs.push(coeff11);
                }
            }
        }

        let mut a0b0_minus_a1b1 = Vec::with_capacity(11);
        let mut a0b1_plus_a1b0 = Vec::with_capacity(11);
        for i in 0..11 {
            let a0b0_minus_a1b1_entry = a0b0_coeffs[i] - a1b1_coeffs[i];
            let a0b1_plus_a1b0_entry = a0b1_coeffs[i] + a1b0_coeffs[i];
            a0b0_minus_a1b1.push(a0b0_minus_a1b1_entry);
            a0b1_plus_a1b0.push(a0b1_plus_a1b0_entry);
        }
        let mut out_coeffs: Vec<Fq> = Vec::with_capacity(12);
        for i in 0..6 {
            if i < 5 {
                let coeff: Fq = a0b0_minus_a1b1[i] + Fq::from(9) * a0b0_minus_a1b1[i + 6]
                    - a0b1_plus_a1b0[i + 6];
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b0_minus_a1b1[i].clone());
            }
        }
        for i in 0..6 {
            if i < 5 {
                let coeff: Fq = a0b1_plus_a1b0[i]
                    + a0b0_minus_a1b1[i + 6]
                    + Fq::from(9) * a0b1_plus_a1b0[i + 6];
                out_coeffs.push(coeff);
            } else {
                out_coeffs.push(a0b1_plus_a1b0[i].clone());
            }
        }
        Self {
            coeffs: out_coeffs.try_into().unwrap(),
        }
    }
}

pub fn from_biguint_to_fq(x: BigUint) -> Fq {
    let x: BigInt<4> = x.try_into().unwrap();
    Fq::from_bigint(x).unwrap()
}

pub fn sgn0_fq(x: Fq) -> bool {
    let y: BigUint = x.into();
    y.to_u32_digits()[0] & 1 == 1
}

pub fn sgn0_fq2(x: Fq2) -> bool {
    let sgn0_x = sgn0_fq(x.c0);
    let zero_0 = x.c0.is_zero();
    let sgn0_y = sgn0_fq(x.c1);
    sgn0_x || (zero_0 && sgn0_y)
}

pub fn pow_fq(a: Fq, exp: Vec<u64>) -> Fq {
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
                res = if z == 1 { res * a } else { res / a };
            } else {
                assert_eq!(z, 1);
                is_started = true;
            }
        }
    }
    res
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fq12;
    use ark_std::UniformRand;

    use crate::fields::native::MyFq12;

    #[test]
    fn test_myfq12() {
        let rng = &mut rand::thread_rng();
        let a: Fq12 = Fq12::rand(rng);
        let b: Fq12 = Fq12::rand(rng);
        let c_expected: Fq12 = a + b;
        let d_expected: Fq12 = a * b;

        let am: MyFq12 = a.into();
        let bm: MyFq12 = b.into();

        let cm = am + bm;
        let dm = am * bm;

        let c: Fq12 = cm.into();
        let d: Fq12 = dm.into();

        assert_eq!(c_expected, c);
        assert_eq!(d_expected, d);
    }
}
