use ark_bn254::{Fq12, G1Affine, G2Affine};

use crate::{final_exp_native::final_exp_native, miller_loop_native::miller_loop_native};

pub fn pairing(p: G1Affine, q: G2Affine) -> Fq12 {
    final_exp_native(miller_loop_native(&q, &p)).into()
}

#[cfg(test)]
mod test {
    use ark_bn254::{G1Affine, G2Affine};
    use ark_ec::pairing::Pairing;
    use ark_std::UniformRand;

    #[test]
    fn test_pairing() {
        let rng = &mut rand::thread_rng();
        let p = G1Affine::rand(rng);
        let q = G2Affine::rand(rng);

        let expected = ark_bn254::Bn254::pairing(p, q).0;
        let actual = super::pairing(p, q);
        assert_eq!(expected, actual);
    }
}
