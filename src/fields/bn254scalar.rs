use core::fmt::{self, Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_bn254::Fr;
use itertools::Itertools;
use num::bigint::BigUint;
use num::{Integer, One};
use serde::{Deserialize, Serialize};

use plonky2::field::types::{Field, PrimeField, Sample};

/// The base field of the secp256k1 elliptic curve.
///
/// Its order is
/// ```ignore
/// P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
/// ```
#[derive(Copy, Clone, Serialize, Deserialize)]
pub struct Bn254Scalar(pub [u64; 4]);

fn biguint_from_array(arr: [u64; 4]) -> BigUint {
    BigUint::from_slice(&[
        arr[0] as u32,
        (arr[0] >> 32) as u32,
        arr[1] as u32,
        (arr[1] >> 32) as u32,
        arr[2] as u32,
        (arr[2] >> 32) as u32,
        arr[3] as u32,
        (arr[3] >> 32) as u32,
    ])
}

impl Default for Bn254Scalar {
    fn default() -> Self {
        Self::ZERO
    }
}

impl PartialEq for Bn254Scalar {
    fn eq(&self, other: &Self) -> bool {
        self.to_canonical_biguint() == other.to_canonical_biguint()
    }
}

impl Eq for Bn254Scalar {}

impl Hash for Bn254Scalar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_canonical_biguint().hash(state)
    }
}

impl Display for Bn254Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.to_canonical_biguint(), f)
    }
}

impl Debug for Bn254Scalar {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.to_canonical_biguint(), f)
    }
}

impl Sample for Bn254Scalar {
    #[inline]
    fn sample<R>(rng: &mut R) -> Self
    where
        R: rand::RngCore + ?Sized,
    {
        use num::bigint::RandBigInt;
        Self::from_noncanonical_biguint(rng.gen_biguint_below(&Self::order()))
    }
}

impl Field for Bn254Scalar {
    const ZERO: Self = Self([0; 4]);
    const ONE: Self = Self([1, 0, 0, 0]);
    const TWO: Self = Self([2, 0, 0, 0]);
    const NEG_ONE: Self = Self([
        0x43E1F593F0000000,
        0x2833E84879B97091,
        0xB85045B68181585D,
        0x30644E72E131A029,
    ]);

    const TWO_ADICITY: usize = 28;
    const CHARACTERISTIC_TWO_ADICITY: usize = Self::TWO_ADICITY;

    // Sage: `g = GF(p).multiplicative_generator()`
    const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self([5, 0, 0, 0]);

    // Sage: `g_2 = power_mod(g, (p - 1) // 2^6), p)`
    // 19103219067921713944291392827692070036145651957329286315305642004821462161904
    const POWER_OF_TWO_GENERATOR: Self = Self([
        0x9BD61B6E725B19F0,
        0x402D111E41112ED4,
        0xE0A7EB8EF62ABC,
        0x2A3C09F0A58A7E85,
    ]);

    const BITS: usize = 256;

    fn order() -> BigUint {
        BigUint::from_slice(&[
            0xF0000001, 0x43E1F593, 0x79B97091, 0x2833E848, 0x8181585D, 0xB85045B6, 0xE131A029,
            0x30644E72,
        ])
    }
    fn characteristic() -> BigUint {
        Self::order()
    }

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // Fermat's Little Theorem
        Some(self.exp_biguint(&(Self::order() - BigUint::one() - BigUint::one())))
    }

    fn from_noncanonical_biguint(val: BigUint) -> Self {
        Self(
            val.to_u64_digits()
                .into_iter()
                .pad_using(4, |_| 0)
                .collect::<Vec<_>>()[..]
                .try_into()
                .expect("error converting to u64 array"),
        )
    }

    #[inline]
    fn from_canonical_u64(n: u64) -> Self {
        Self([n, 0, 0, 0])
    }

    #[inline]
    fn from_noncanonical_u128(n: u128) -> Self {
        Self([n as u64, (n >> 64) as u64, 0, 0])
    }

    #[inline]
    fn from_noncanonical_u96(n: (u64, u32)) -> Self {
        Self([n.0, n.1 as u64, 0, 0])
    }
}

impl PrimeField for Bn254Scalar {
    fn to_canonical_biguint(&self) -> BigUint {
        let mut result = biguint_from_array(self.0);
        if result >= Self::order() {
            result -= Self::order();
        }
        result
    }
}

impl Neg for Bn254Scalar {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.is_zero() {
            Self::ZERO
        } else {
            Self::from_noncanonical_biguint(Self::order() - self.to_canonical_biguint())
        }
    }
}

impl Add for Bn254Scalar {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let mut result = self.to_canonical_biguint() + rhs.to_canonical_biguint();
        if result >= Self::order() {
            result -= Self::order();
        }
        Self::from_noncanonical_biguint(result)
    }
}

impl AddAssign for Bn254Scalar {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sum for Bn254Scalar {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl Sub for Bn254Scalar {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}

impl SubAssign for Bn254Scalar {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for Bn254Scalar {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::from_noncanonical_biguint(
            (self.to_canonical_biguint() * rhs.to_canonical_biguint()).mod_floor(&Self::order()),
        )
    }
}

impl MulAssign for Bn254Scalar {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Product for Bn254Scalar {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ONE)
    }
}

impl Div for Bn254Scalar {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl DivAssign for Bn254Scalar {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl From<Fr> for Bn254Scalar {
    fn from(value: Fr) -> Self {
        let biguint = value.into();
        Bn254Scalar::from_noncanonical_biguint(biguint)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use plonky2::{
        field::types::Sample,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };
    use plonky2_ecdsa::gadgets::nonnative::CircuitBuilderNonNative;

    use super::Bn254Scalar;
    #[test]
    fn test_add_scalar_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_ecc_config();

        let pw = PartialWitness::<F>::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        for _ in 0..100 {
            let a = Bn254Scalar::rand();
            let b = Bn254Scalar::rand();
            let x = builder.constant_nonnative(a);
            let y = builder.constant_nonnative(b);
            let z = builder.add_nonnative(&x, &y);
            let expected_z = builder.constant_nonnative(a + b);
            builder.connect_nonnative(&z, &expected_z);
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)?;

        Ok(())
    }
}
