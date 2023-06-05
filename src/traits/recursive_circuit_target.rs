use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{target::Target, witness::PartialWitness},
    plonk::circuit_builder::CircuitBuilder,
};

pub trait RecursiveCircuitTarget<F: RichField + Extendable<D>, const D: usize, V> {
    fn to_vec(&self) -> Vec<Target>;

    fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self;

    fn set_witness(&self, pw: &mut PartialWitness<F>, value: &V);
}
