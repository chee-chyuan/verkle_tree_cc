use std::collections::BTreeMap;

use ark_ec::models::{short_weierstrass_jacobian::GroupAffine as SWAffine, SWModelParameters};
use ark_ec::PairingEngine;
use ark_ff::{Field, PrimeField};
use ark_poly::EvaluationDomain;
use ark_poly::{univariate::DensePolynomial, Evaluations, GeneralEvaluationDomain};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment, QuerySet};
use rand::rngs::StdRng;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

const LEAF_LABEL: &str = "leaf label";

fn hash_commit_field_element<F: Field>(to_hash: Vec<F>) -> F {
    to_hash[0] + to_hash[1]
}

fn create_hashed_commit_from_leaves<F, PC>(
    leaves: Vec<F>,
    branching_factor: usize,
    comm_key: PC::CommitterKey,
    evaluation_domain: GeneralEvaluationDomain<F>,
) -> Vec<F>
where
    F: Field + ark_ff::FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PC::Commitment: ToFieldElements<F>,
{
    let mut start_index: usize = 0;
    let mut end_index = branching_factor;
    let mut hashed_commit: Vec<F> = Vec::new();

    loop {
        if end_index > leaves.len() {
            break;
        }

        let to_interpolate = leaves[start_index..end_index].to_vec();
        let evaluation = Evaluations::from_vec_and_domain(to_interpolate, evaluation_domain);
        let poly = evaluation.interpolate();

        let rng = &mut StdRng::from_seed([0u8; 32]);
        let label_poly = LabeledPolynomial::new(LEAF_LABEL.to_string(), poly.clone(), None, None);

        // poly -> Commit -> to 2 field elements -> hash to single field element
        let multi_label_poly = vec![label_poly];

        let poly_commit = PC::commit(&comm_key, &multi_label_poly, Some(rng))
            .unwrap()
            .0;
        let commit_field_element = ToFieldElements::to_field_elements(poly_commit[0].commitment());
        let commit_single_field_element = hash_commit_field_element(commit_field_element);

        hashed_commit.push(commit_single_field_element);

        start_index += branching_factor;
        end_index += branching_factor;
    }

    hashed_commit
}

fn generate_full_verkle_tree<F, PC>(
    tree: &mut Vec<F>,
    branching_factor: usize,
    comm_key: PC::CommitterKey,
    evaluation_domain: GeneralEvaluationDomain<F>,
) -> PC::Commitment
where
    F: Field + ark_ff::FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PC::Commitment: ToFieldElements<F>,
{
    let mut start_index: usize = 0;
    let mut end_index = branching_factor;
    let mut root: PC::Commitment;

    let rng = &mut StdRng::from_seed([0u8; 32]);

    loop {
        // get from start_index to end_index (non including)
        let to_interpolate = tree[start_index..end_index].to_vec();
        let evaluation = Evaluations::from_vec_and_domain(to_interpolate, evaluation_domain);
        let poly = evaluation.interpolate();
        let label_poly = LabeledPolynomial::new(LEAF_LABEL.to_string(), poly.clone(), None, None);

        // poly -> Commit -> to 2 field elements -> hash to single field element
        let multi_label_poly = vec![label_poly];
        let poly_commit = PC::commit(&comm_key, &multi_label_poly, Some(rng))
            .unwrap()
            .0;
        let commit_field_element = ToFieldElements::to_field_elements(poly_commit[0].commitment());
        let commit_single_field_element = hash_commit_field_element(commit_field_element);
        root = poly_commit[0].commitment().clone();

        // append to end of tree
        tree.push(commit_single_field_element);

        // check condition after appending to tree vec
        if tree.len() == end_index + 1 {
            break;
        }

        // update start_index and end_index
        start_index += branching_factor;
        end_index += branching_factor;
    }

    root
}

fn generate_proof<F, PC>(
    position: usize,
    branching_factor: usize,
    depth: usize,
    leaves: Vec<F>,
    tree: Vec<F>,
    comm_key: PC::CommitterKey,
    evaluation_domain: GeneralEvaluationDomain<F>,
) -> (
    F,
    PC::BatchProof,
    Vec<LabeledCommitment<PC::Commitment>>,
    QuerySet<F>,
    BTreeMap<(String, F), F>,
)
where
    F: Field + ark_ff::FftField + ark_ff::PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PC::Commitment: ToFieldElements<F>,
{
    // position of leaf in between 0 to depth**branch_size (non_inclusive)

    // get range of leaf
    let start_index_multiplier = position / branching_factor;
    // let start_index = position % branching_factor;
    let start_index = start_index_multiplier * branching_factor;
    let end_index = start_index + branching_factor;

    let to_interpolate = leaves[start_index..end_index].to_vec();
    // interpolate and hash
    let evaluation = Evaluations::from_vec_and_domain(to_interpolate, evaluation_domain);
    let leaf_poly = evaluation.interpolate();
    let leaf_position = position % branching_factor; // evaluation leaf_poly at leaf_position will return us our desired leaf node value
    let value = leaves[position];

    let label_poly = LabeledPolynomial::new(LEAF_LABEL.to_string(), leaf_poly.clone(), None, None);

    let mut label_polys: Vec<LabeledPolynomial<F, DensePolynomial<F>>> = Vec::new();
    let mut evaluations: BTreeMap<(String, F), F> = BTreeMap::new();
    let mut query_set = QuerySet::<F>::new();

    let evaluation_point = evaluation_domain.element(leaf_position);

    label_polys.push(label_poly);
    evaluations.insert((LEAF_LABEL.to_string(), evaluation_point), value);
    query_set.insert((
        LEAF_LABEL.to_string(),
        (format!("{}", depth), evaluation_point),
    ));

    let res = get_commitment_tree_proof::<F, PC>(
        start_index_multiplier,
        tree,
        branching_factor,
        depth - 1,
        comm_key,
        &mut label_polys,
        &mut evaluations,
        &mut query_set,
        evaluation_domain,
    );

    (value, res.0, res.1, query_set, evaluations)
}

fn get_commitment_tree_proof<F, PC>(
    mut position: usize,
    tree: Vec<F>,
    branching_factor: usize,
    mut current_depth: usize,
    comm_key: PC::CommitterKey,
    label_polys_leaf: &mut Vec<LabeledPolynomial<F, DensePolynomial<F>>>,
    evaluations: &mut BTreeMap<(String, F), F>,
    query_set: &mut QuerySet<F>,
    evaluation_domain: GeneralEvaluationDomain<F>,
) -> (PC::BatchProof, Vec<LabeledCommitment<PC::Commitment>>)
where
    F: Field + ark_ff::FftField + ark_ff::PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PC::Commitment: ToFieldElements<F>,
{
    let mut offset: usize = 0;
    let rng = &mut StdRng::from_seed([0u8; 32]);

    loop {
        if current_depth == 0 {
            break;
        }

        let label_poly_str = format!("commit_depth_{}", current_depth);

        let start_index_multiplier = position / branching_factor;
        let start_index = start_index_multiplier * branching_factor + offset;
        let end_index = start_index + branching_factor;

        let evaluated_val = tree[position + offset];
        // some interpolate logic here
        let to_interpolate = tree[start_index..end_index].to_vec();
        // interpolate and hash
        let evaluation = Evaluations::from_vec_and_domain(to_interpolate, evaluation_domain);
        let poly = evaluation.interpolate();
        let label_poly = LabeledPolynomial::new(label_poly_str.clone(), poly.clone(), None, None);

        let evaluation_point = evaluation_domain.element(position);

        label_polys_leaf.push(label_poly);
        evaluations.insert((label_poly_str.clone(), evaluation_point), evaluated_val);
        query_set.insert((
            label_poly_str,
            (format!("{}", current_depth), evaluation_point),
        ));

        position = start_index_multiplier;
        offset += branching_factor.pow(current_depth.try_into().unwrap());
        current_depth -= 1;
    }

    let poly_commit = PC::commit(&comm_key, &label_polys_leaf.clone(), Some(rng)).unwrap();

    let rng_chacha = &mut ChaCha20Rng::from_rng(rng).unwrap();
    let random_opening_challenge = F::rand(rng_chacha);

    // batch_open
    let proof = PC::batch_open(
        &comm_key,
        &label_polys_leaf.clone(),
        &poly_commit.0,
        &query_set,
        random_opening_challenge,
        &poly_commit.1,
        None,
    )
    .unwrap();

    (proof, poly_commit.0)
}

fn verify_proof<F, PC>(
    batch_proof: PC::BatchProof,
    ver_key: PC::VerifierKey,
    poly_commit: Vec<LabeledCommitment<PC::Commitment>>,
    query_set: QuerySet<F>,
    evaluations: BTreeMap<(String, F), F>,
    random_opening_challenge: F,
) -> bool
where
    F: Field + ark_ff::FftField + ark_ff::PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    PC::Commitment: ToFieldElements<F>,
{
    let rng = &mut StdRng::from_seed([0u8; 32]); // not sure if this is correct

    PC::batch_check(
        &ver_key,
        &poly_commit,
        &query_set,
        &evaluations,
        &batch_proof,
        random_opening_challenge,
        rng,
    )
    .unwrap()
}

impl<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>> VerkleTree<F, PC>
where
    F: ark_ff::FftField + ark_ff::PrimeField,
    PC::Commitment: ToFieldElements<F>,
{
    /// Create a verkle tree with the given depth and branching factor
    pub fn new(comm_key: PC::CommitterKey, depth: usize, branching_factor: usize) -> Self {
        let total_size = branching_factor.pow(depth.try_into().unwrap());
        let leaves = vec![F::zero(); total_size];

        let evaluation_domain = GeneralEvaluationDomain::<F>::new(branching_factor).unwrap();
        let mut tree = create_hashed_commit_from_leaves::<F, PC>(
            leaves.clone(),
            branching_factor,
            comm_key.clone(),
            evaluation_domain,
        );

        let root = generate_full_verkle_tree::<F, PC>(
            &mut tree,
            branching_factor,
            comm_key.clone(),
            evaluation_domain,
        );

        VerkleTree::Leaf {
            root,
            leaf: leaves,
            tree,
            depth,
            branching_factor,
            comm_key,
        }
    }

    /// Returns the depth of the tree
    pub fn depth(&self) -> usize {
        let VerkleTree::Leaf {
            root: _,
            leaf: _,
            tree: _,
            depth,
            branching_factor: _,
            comm_key: _,
        } = self;

        depth.clone()
    }

    /// Returns the polynomial commitment at the root of the tree
    pub fn root(&self) -> PC::Commitment {
        let VerkleTree::Leaf {
            root,
            leaf: _,
            tree: _,
            depth: _,
            branching_factor: _,
            comm_key: _,
        } = self;

        root.clone()
    }

    /// Add an element to the tree at the given position
    pub fn insert(&mut self, position: usize, x: F) {
        let VerkleTree::Leaf {
            ref mut root,
            ref mut leaf,
            ref mut tree,
            depth,
            branching_factor,
            comm_key,
        } = self;

        leaf[position] = x;
        let branching_factor = *branching_factor;
        let evaluation_domain = GeneralEvaluationDomain::<F>::new(branching_factor).unwrap();
        // calculate new commitment associated with the leaf
        let start_index_multiplier = position / branching_factor;
        let start_index = start_index_multiplier * branching_factor;
        let end_index = start_index + branching_factor;

        let to_interpolate = leaf[start_index..end_index].to_vec();
        let evaluation = Evaluations::from_vec_and_domain(to_interpolate, evaluation_domain);
        let poly = evaluation.interpolate();

        let rng = &mut StdRng::from_seed([0u8; 32]);
        let label_poly = LabeledPolynomial::new(LEAF_LABEL.to_string(), poly.clone(), None, None);

        // poly -> Commit -> to 2 field elements -> hash to single field element
        let multi_label_poly = vec![label_poly];

        let poly_commit = PC::commit(&comm_key, &multi_label_poly, Some(rng))
            .unwrap()
            .0;
        let commit_field_element = ToFieldElements::to_field_elements(poly_commit[0].commitment());
        let commit_single_field_element = hash_commit_field_element(commit_field_element);
        tree[start_index_multiplier] = commit_single_field_element;

        let mut current_depth = *depth - 1;
        let mut offset = 0;
        let mut position = start_index_multiplier;
        // let mut last_commitment: PC::Commitment;
        loop {
            if current_depth == 0 {
                break;
            }

            let label_poly_str = format!("commit_depth_{}", current_depth);

            let start_index_multiplier = position / branching_factor;
            let start_index = start_index_multiplier * branching_factor + offset;
            let end_index = start_index + branching_factor;

            let to_interpolate = tree[start_index..end_index].to_vec();
            // interpolate and hash
            let evaluation = Evaluations::from_vec_and_domain(to_interpolate, evaluation_domain);
            let poly = evaluation.interpolate();
            let label_poly =
                LabeledPolynomial::new(label_poly_str.clone(), poly.clone(), None, None);

            let multi_label_poly = vec![label_poly];

            let poly_commit = PC::commit(&comm_key, &multi_label_poly, Some(rng))
                .unwrap()
                .0;
            let commit_field_element =
                ToFieldElements::to_field_elements(poly_commit[0].commitment());
            let commit_single_field_element = hash_commit_field_element(commit_field_element);
            *root = poly_commit[0].commitment().clone();

            offset = branching_factor.pow(current_depth.try_into().unwrap());
            position = start_index_multiplier + offset;
            tree[position] = commit_single_field_element;
            current_depth -= 1;
        }

        // *root = last_commitment;
    }

    /// Batch-open the verkle tree at the given set of positions
    pub fn open(&self, position: Vec<usize>) -> Option<(Vec<F>, VerkleProof<F, PC>)> {
        let VerkleTree::Leaf {
            root: _,
            leaf,
            tree,
            depth,
            branching_factor,
            comm_key,
        } = self;

        let mut values = Vec::new();
        let mut proofs = Vec::new();

        let evaluation_domain = GeneralEvaluationDomain::<F>::new(*branching_factor).unwrap();
        for p in position {
            let (value, batch_proof, poly_commit, query_set, evaluations) = generate_proof::<F, PC>(
                p,
                *branching_factor,
                *depth,
                leaf.to_vec(),
                tree.to_vec(),
                comm_key.clone(),
                evaluation_domain,
            );

            let leaf_position = p % *branching_factor;
            let evaluation_point = evaluation_domain.element(leaf_position);

            values.push(value);
            proofs.push(Proof::<F, PC> {
                batch_proof,
                poly_commit,
                query_set,
                evaluations,
                position: evaluation_point,
            });
        }

        let verkle_proof = VerkleProof::<F, PC> { proofs };

        Some((values, verkle_proof))
    }

    /// Check the correctness of an opening
    pub fn check(
        root: PC::Commitment,
        vk: PC::VerifierKey,
        (x, proof): (Vec<F>, VerkleProof<F, PC>),
    ) -> bool {
        for (val, mut p) in x.iter().zip(proof.proofs.into_iter()) {
            p.replace_poly_commit_with_root(root.clone());

            // check value
            let evaluation = p.evaluations.get(&(LEAF_LABEL.to_string(), p.position));
            if evaluation.is_none() {
                return false;
            }

            let evaluation = evaluation.unwrap();
            if val != evaluation {
                return false;
            }

            // batch_check proof
            let rng = &mut StdRng::from_seed([0u8; 32]);
            let rng_chacha = &mut ChaCha20Rng::from_rng(rng).unwrap();
            let random_opening_challenge = F::rand(rng_chacha);
            let is_valid_batch_check = verify_proof::<F, PC>(
                p.batch_proof.clone(),
                vk.clone(),
                p.poly_commit.clone(),
                p.query_set.clone(),
                p.evaluations.clone(),
                random_opening_challenge,
            );

            if !is_valid_batch_check {
                return false;
            }
        }

        true
    }
}

pub trait ToFieldElements<F: Field> {
    // Just stipulates a method for converting a polynomial commitment into an vector of field
    // elements.
    fn to_field_elements(&self) -> Vec<F>;
}

impl<'a, 'b, P, E> ToFieldElements<P::ScalarField>
    for ark_poly_commit::marlin::marlin_pc::Commitment<E>
where
    P: SWModelParameters,
    E: PairingEngine<Fq = P::BaseField, G1Affine = SWAffine<P>>,
    P::ScalarField: PrimeField,
    P::BaseField: PrimeField<BigInt = <P::ScalarField as PrimeField>::BigInt>,
{
    fn to_field_elements(&self) -> Vec<P::ScalarField> {
        // We don't use degree bounds, and so ignore the shifted part of the commitments
        let _ = self.shifted_comm;
        [self.comm.0.x, self.comm.0.y]
            .iter()
            .map(|a| P::ScalarField::from_repr(a.into_repr()).unwrap())
            .collect()
    }
}

enum VerkleTree<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    Leaf {
        root: PC::Commitment,
        leaf: Vec<F>,
        tree: Vec<F>,
        depth: usize,
        branching_factor: usize,
        comm_key: PC::CommitterKey,
    },
}

struct Proof<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    batch_proof: PC::BatchProof,
    poly_commit: Vec<LabeledCommitment<PC::Commitment>>,
    query_set: QuerySet<F>,
    evaluations: BTreeMap<(String, F), F>,
    position: F,
}

impl<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>> Proof<F, PC> {
    pub fn replace_poly_commit_with_root(&mut self, root: PC::Commitment) {
        self.poly_commit.pop();

        let label_poly_str = format!("commit_depth_{}", 1);
        let root_commit = LabeledCommitment::new(label_poly_str, root, None);
        self.poly_commit.push(root_commit);
    }
}

struct VerkleProof<F: Field, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    // Just here to get rid of the unused variable warning
    proofs: Vec<Proof<F, PC>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Bn254, Fr};
    use ark_poly_commit::marlin_pc::MarlinKZG10;

    type Bn254KZG = MarlinKZG10<Bn254, DensePolynomial<Fr>>;

    #[test]
    fn test_verify() {
        type F = Fr;

        let branching_factor: usize = 2048;
        let depth: usize = 2;

        let mut rng = rand::thread_rng();
        let max_degree = branching_factor;
        let setup = Bn254KZG::setup(max_degree, None, &mut rng).unwrap();
        let (comm_key, verifier_key) =
            Bn254KZG::trim(&setup, branching_factor, branching_factor, None).unwrap();
        let mut verkle_tree: VerkleTree<F, Bn254KZG> =
            VerkleTree::new(comm_key, depth, branching_factor);

        let num_entries = 1024;

        // Insert x^2 at position x for x in 0..1024
        for x in 0..num_entries {
            verkle_tree.insert(x, Fr::from(x as u64).square());
        }

        // Open only at even entries.
        let open_at: Vec<usize> = (0..(num_entries / 2)).map(|x| 2 * x).collect();

        let (opening_values, opening_proof) = verkle_tree.open(open_at.clone()).unwrap();

        assert_eq!(open_at.len(), opening_values.len());
        for (x, y) in open_at.iter().zip(opening_values.iter()) {
            assert_eq!(Fr::from(*x as u64).square(), *y);
        }

        let root = verkle_tree.root();

        assert!(VerkleTree::<Fr, Bn254KZG>::check(
            root,
            verifier_key,
            (opening_values, opening_proof)
        ));
    }
}
