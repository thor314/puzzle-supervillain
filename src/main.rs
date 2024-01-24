#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(non_snake_case)]
#![allow(clippy::clone_on_copy)]
use ark_bls12_381::{g2::Config, Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{
    hashing::{curve_maps::wb::WBMap, map_to_curve_hasher::MapToCurveBasedHasher, HashToCurve},
    pairing::Pairing,
    AffineRepr, CurveGroup, Group,
};
use ark_ff::field_hashers::DefaultFieldHasher;
use ark_std::One;

use ark_serialize::{CanonicalDeserialize, Read};

use log::{debug, LevelFilter};
use prompt::{puzzle, welcome};

use sha2::Sha256;
use std::fs::File;
use std::io::Cursor;
use std::ops::{Mul, Neg};

use ark_std::{rand::SeedableRng, UniformRand, Zero};

fn derive_point_for_pok(i: usize) -> G2Affine {
    let rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(20399u64);
    G2Affine::rand(rng).mul(Fr::from(i as u64 + 1)).into()
}

#[allow(dead_code)]
fn pok_prove(sk: Fr, i: usize) -> G2Affine {
    derive_point_for_pok(i).mul(sk).into()
}

fn pok_verify(pk: G1Affine, i: usize, proof: G2Affine) {
    assert!(Bls12_381::multi_pairing(
        [pk, G1Affine::generator()],
        [derive_point_for_pok(i).neg(), proof]
    )
    .is_zero());
}

fn hasher() -> MapToCurveBasedHasher<G2Projective, DefaultFieldHasher<Sha256, 128>, WBMap<Config>> {
    MapToCurveBasedHasher::<G2Projective, DefaultFieldHasher<Sha256, 128>, WBMap<Config>>::new(&[
        1, 3, 3, 7,
    ])
    .unwrap()
}

#[allow(dead_code)]
fn bls_sign(sk: Fr, msg: &[u8]) -> G2Affine {
    hasher().hash(msg).unwrap().mul(sk).into_affine()
}

fn bls_verify(pk: G1Affine, sig: G2Affine, msg: &[u8]) {
    assert!(Bls12_381::multi_pairing(
        [pk, G1Affine::generator()],
        [hasher().hash(msg).unwrap().neg(), sig]
    )
    .is_zero());
}

fn from_file<T: CanonicalDeserialize>(path: &str) -> T {
    let mut file = File::open(path).unwrap();
    let mut buffer = Vec::new();
    file.read_to_end(&mut buffer).unwrap();
    T::deserialize_uncompressed_unchecked(Cursor::new(&buffer)).unwrap()
}

fn main() {
    env_logger::builder()
        .filter_level(LevelFilter::Debug)
        .init();
    welcome();
    puzzle(PUZZLE_DESCRIPTION);

    let public_keys: Vec<(G1Affine, G2Affine)> = from_file("public_keys.bin");

    public_keys
        .iter()
        .enumerate()
        .for_each(|(i, (pk, proof))| pok_verify(*pk, i, *proof));

    let new_key_index = public_keys.len();
    let message = b"thor314";

    /* Enter solution here */
    let (new_key, new_proof, aggregate_signature) = get_hack(public_keys.clone(), message);
    /* End of solution */

    pok_verify(new_key, new_key_index, new_proof);
    debug!("pok verified successfully");

    let aggregate_key = public_keys
        .iter()
        .fold(G1Projective::from(new_key), |acc, (pk, _)| acc + pk)
        .into_affine();
    debug!("agg key created successfully");
    bls_verify(aggregate_key, aggregate_signature, message)
}

const PUZZLE_DESCRIPTION: &str = r"
Bob has been designing a new optimized signature scheme for his L1 based on BLS signatures. Specifically, he wanted to be able to use the most efficient form of BLS signature aggregation, where you just add the signatures together rather than having to delinearize them. In order to do that, he designed a proof-of-possession scheme based on the B-KEA assumption he found in the the Sapling security analysis paper by Mary Maller [1]. Based the reasoning in the Power of Proofs-of-Possession paper [2], he concluded that his scheme would be secure. After he deployed the protocol, he found it was attacked and there was a malicious block entered the system, fooling all the light nodes...

[1] https://github.com/zcash/sapling-security-analysis/blob/master/MaryMallerUpdated.pdf
[2] https://rist.tech.cornell.edu/papers/pkreg.pdf
";

// so as discovered below, the crux is that if I start by defining *my secret key*, we will fail the
// bls verification with overwhelming probability.
// however, if we start by defining the aggregate secret key, we struggle to work backwards to construct the PoP.
// struggling is not the same as failing though, so this feels like the right track.
//
// It seems like the PoP is well defined, but we have all the freedom defining our own proof, as long as it equals sk_9*R_9.
pub fn get_hack(pks: Vec<(G1Affine, G2Affine)>, msg: &[u8]) -> (G1Affine, G2Affine, G2Affine) {
    let new_key = pks
        .iter()
        .fold(G1Projective::zero(), |acc, (pk, _)| acc - pk)
        .into();
    let pis = pks
        .iter()
        .cloned()
        .map(|(_, proof)| proof)
        .collect::<Vec<_>>();
    let new_proof: G2Affine = extract_proof(&new_key, pis);
    let aggregate_signature = G2Affine::zero();
    debug!("new_key: {:?}", new_key);
    (new_key, new_proof, aggregate_signature)
}

/// given pks, R, G st Z=e(sk_9 * G, R_9)
/// find pi_9 such that Z=e(G, sk_9 * R_9)=e(G, pi_9)
//
// Maller's paper says that, by the BKEA assumption, this is suppposedly hard, and equivalent to knowledge of $s$.
// does there exist a homomorphic or isomorphic map from G1 to G2? No.
//
// ...hmm on second look that randomness seems a lot more malleable than I thought.
// pi_9 = sum_1^8(pi_i *(10/(i+1)))
fn extract_proof(new_key: &G1Affine, pis: Vec<G2Affine>) -> G2Affine {
    use ark_ff::Field;
    let pi_sum = pis
        .into_iter()
        .enumerate()
        .map(|(i, pi_i)| {
            let coef = {
                debug!("i+1: {}", i + 1);
                let inv = Fr::from(i as u32 + 1u32).inverse().unwrap();
                Fr::from(10) * inv
            };
            pi_i * coef
        })
        .sum::<G2Projective>()
        .into_affine();

    // pi_9 = -sum(pi_i * (10/(i+1))
    -pi_sum
}

/////////////////////////////////////////////////////////////
// To Kobi and friends: from here on, are just my notes 😉 //
/////////////////////////////////////////////////////////////

// on second glance, the random nonces are less random than they once seemed 🙊
#[test]
fn test_rng() {
    // let G = G1Projective::generator().into_affine();
    let rng = &mut ark_std::rand::rngs::StdRng::seed_from_u64(20399u64);
    let R = G2Affine::rand(rng);
    let R_1 = R.mul(Fr::from(2));
    let R_9 = R.mul(Fr::from(10));
    assert_eq!(derive_point_for_pok(1), R_1); // pass
    assert_eq!(derive_point_for_pok(9), R_9); // pass
    use ark_ff::Field;
    let five_inv = Fr::from(5u64).inverse().unwrap();
    let R_9_to_1 = R_9.into_affine().mul(five_inv).into_affine();
    assert_eq!(R_1, R_9_to_1); // pass
                               // oh fun, we nearly done
                               //
                               // we can construct stuff.
}

// e(pk_agg, -(H(m)) == e(G, sig_agg)
// -(sk_agg) * e(G, H(m)) == sk_agg * e(G, H(m)) => 2 * sk_agg = 0
// try sk_agg = 0
//
// sk_agg = 0 => pk
// pk_agg = 0*G = my_pk + sum(pks) = O
// my_pk = O - sum(pks)
// sig_agg = (sk_agg) * -H(m) = O
//
// pi and my_sk... not sure. pok check:
// e(my_pk, -R_9) == e(G, pi) = e(O-sum(pks), -R_9) => pi = R_9 * (n-sum(sks))?
//
/// this passes the aggregation check, but not pok_verify
pub fn get_hack_only_agg(
    pks: Vec<(G1Affine, G2Affine)>,
    msg: &[u8],
) -> (G1Affine, G2Affine, G2Affine) {
    let new_key = pks
        .iter()
        .fold(G1Projective::zero(), |acc, (pk, _)| acc - pk)
        .into();
    let new_proof = G2Projective::generator().mul(Fr::zero()).into_affine();
    let aggregate_signature = G2Affine::zero();
    debug!("new_key: {:?}", new_key);
    (new_key, new_proof, aggregate_signature)
}

// e(pk_agg, -(H(m)) == e(G, sig_agg)
// -(sk_agg) * e(G, H(m)) == sk_agg * e(G, H(m)) => 2 * sk_agg = 0
// try sk_agg = n/2
// this shouldn't work, since n is supposedly a large odd prime, but try it anyways
//
// sk_agg = n/2
// pk_agg = sk_agg * G
// my_pk = pk_agg - sum(pks)
// sig_agg = sk_agg * -H(m)
//
// pi... not sure about pi.
// pi and my_sk... not sure.
//
/// this doesn't pass the aggregation check
pub fn get_hack_(pks: Vec<(G1Affine, G2Affine)>, msg: &[u8]) -> (G1Affine, G2Affine, G2Affine) {
    use ark_ff::BigInteger;
    use ark_ff::PrimeField;
    let mut n = Fr::MODULUS;
    n.div2();
    let sk_agg: Fr = n.into();
    let pk_agg = G1Projective::generator().mul(sk_agg);
    let new_key = (pk_agg
        - pks
            .iter()
            .fold(G1Projective::zero(), |acc, (pk, _)| acc + pk))
    .into_affine();
    let aggregate_signature = hasher().hash(msg).unwrap().mul(-sk_agg).into_affine();

    let new_proof = G2Projective::generator().mul(Fr::zero()).into_affine();

    // let aggregate_signature = G2Affine::zero();
    debug!("new_key: {:?}", new_key);
    (new_key, new_proof, aggregate_signature)
}

// try something
pub fn get_hack_obvious(
    pks: Vec<(G1Affine, G2Affine)>,
    msg: &[u8],
) -> (G1Affine, G2Affine, G2Affine) {
    let sk = Fr::one();
    let pk = G1Projective::generator().mul(sk).into_affine();
    let new_key = pk;
    let new_proof = pok_prove(sk, pks.len());
    let sig = hasher().hash(msg).unwrap().mul(sk);
    let aggregate_signature = pks
        .iter()
        .fold(-sig, |acc, (_, sig_i)| acc + sig_i)
        .into_affine();

    debug!("new_key: {:?}", new_key);
    (new_key, new_proof, aggregate_signature)
}
