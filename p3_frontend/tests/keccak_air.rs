// #[global_allocator]
// static ALLOC: dhat::Alloc = dhat::Alloc;

use p3_air::BaseAir;
use p3_keccak_air::{generate_trace_rows, KeccakAir, NUM_ROUNDS};
use p3_util::log2_ceil_usize;

use halo2_backend::poly::commitment::ParamsProver;
use halo2_backend::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_backend::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_backend::poly::kzg::strategy::SingleStrategy;
use halo2_backend::{
    plonk::{
        keygen::{keygen_pk_v2, keygen_vk_v2},
        prover::ProverV2Single,
        verifier::verify_proof_single,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use halo2_middleware::circuit::CompiledCircuitV2;
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use p3_frontend::{check_witness, compile_circuit_cs, compile_preprocessing, trace_to_wit, FWrap};
use rand::random;
use rand_core::block::BlockRng;
use rand_core::block::BlockRngCore;
use std::time::Instant;

// One number generator, that can be used as a deterministic Rng, outputing fixed values.
struct OneNg {}

impl BlockRngCore for OneNg {
    type Item = u32;
    type Results = [u32; 16];

    fn generate(&mut self, results: &mut Self::Results) {
        for elem in results.iter_mut() {
            *elem = 1;
        }
    }
}

#[test]
fn test_keccak() {
    // let profiler = Some(dhat::Profiler::new_heap());
    let profiler = None;
    let num_hashes = 4;
    let inputs = (0..num_hashes).map(|_| random()).collect::<Vec<_>>();
    let size = inputs.len() * NUM_ROUNDS;
    // TODO: 6 must be bigger than unusable rows.  Add a helper function to calculate this
    let n = (size + 6).next_power_of_two();
    let k = log2_ceil_usize(n) as u32;
    println!("k = {k}");
    println!("n = {n}");
    println!("size = {size}");
    let air = KeccakAir {};
    println!("columns = {}", <KeccakAir as BaseAir<Fr>>::width(&air));
    let num_public_values = 0;
    println!("compile circuit cs...");
    let (cs, preprocessing_info) = compile_circuit_cs::<Fr, _>(&air, num_public_values, profiler);
    println!(
        "degree = {}",
        cs.gates.iter().map(|g| g.poly.degree()).max().unwrap()
    );
    // println!("{:?}", cs.gates[0]);

    println!("compile preprocessing...");
    let preprocessing = compile_preprocessing::<Fr, _>(k, size, &preprocessing_info, &air);
    // println!("{:#?}", cs);
    // println!("{:?}", preprocessing);
    let compiled_circuit = CompiledCircuitV2 { cs, preprocessing };
    // TODO: Replace `random()` with a pseudorandom generator with known seed for deterministic
    // results.
    println!("generate trace rows...");
    let trace = generate_trace_rows::<FWrap<Fr>>(inputs);
    println!("trace to wit...");
    let witness = trace_to_wit(k, trace);
    // let pis = get_public_inputs(&preprocessing_info, size, &witness);

    check_witness(&compiled_circuit, k, &witness, &[]);
    // println!("{:?}", witness);

    // Setup
    let mut rng = BlockRng::new(OneNg {});
    let params = ParamsKZG::<Bn256>::setup(k, &mut rng);
    let verifier_params = params.verifier_params();
    let start = Instant::now();
    let vk = keygen_vk_v2(&params, &compiled_circuit).expect("keygen_vk should not fail");
    let pk =
        keygen_pk_v2(&params, vk.clone(), &compiled_circuit).expect("keygen_pk should not fail");
    println!("Keygen: {:?}", start.elapsed());
    drop(compiled_circuit);

    // Proving
    println!("Proving...");
    let start = Instant::now();
    let instances_slice: &[&[Fr]] = &[];
    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    let mut prover =
        ProverV2Single::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _>::new(
            &params,
            &pk,
            instances_slice,
            &mut rng,
            &mut transcript,
        )
        .unwrap();
    println!("phase 0");
    prover.commit_phase(0, witness).unwrap();
    prover.create_proof().unwrap();
    let proof = transcript.finalize();
    println!("Prove: {:?}", start.elapsed());

    // Verify
    let start = Instant::now();
    println!("Verifying...");
    let mut verifier_transcript =
        Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof.as_slice());
    let strategy = SingleStrategy::new(verifier_params);

    verify_proof_single::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
        &params,
        &vk,
        strategy,
        instances_slice,
        &mut verifier_transcript,
    )
    .expect("verify succeeds");
    println!("Verify: {:?}", start.elapsed());
}
