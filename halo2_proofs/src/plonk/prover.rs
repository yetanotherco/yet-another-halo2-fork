use crate::plonk::{Error, ErrorBack};
use crate::poly::commitment::{self, CommitmentScheme, Params};
use crate::transcript::{EncodedChallenge, TranscriptWrite};
use halo2_backend::helpers::SerdeFormat;
use halo2_backend::plonk::{prover::Prover, ProvingKey};
use halo2_backend::poly::VerificationStrategy;
use halo2_backend::transcript::TranscriptWriterBuffer;
use halo2_frontend::circuit::WitnessCalculator;
use halo2_frontend::plonk::{Circuit, ConstraintSystem};
use halo2_middleware::ff::{FromUniformBytes, WithSmallOrderMulGroup};
use halo2_middleware::zal::{
    impls::{PlonkEngine, PlonkEngineConfig},
    traits::MsmAccel,
};
use rand_core::RngCore;
use std::collections::HashMap;
use std::fs::File;
use std::io::BufWriter;

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_proof_with_engine<
    'params,
    Scheme: CommitmentScheme,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
    M: MsmAccel<Scheme::Curve>,
>(
    engine: PlonkEngine<Scheme::Curve, M>,
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[Vec<Vec<Scheme::Scalar>>],
    rng: R,
    transcript: &mut T,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    if circuits.len() != instances.len() {
        return Err(Error::Backend(ErrorBack::InvalidInstances));
    }

    let mut cs = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut cs, circuits[0].params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut cs);
    let cs = cs;

    let mut witness_calcs: Vec<_> = circuits
        .iter()
        .enumerate()
        .map(|(i, circuit)| {
            WitnessCalculator::new(params.k(), circuit, &config, &cs, instances[i].as_slice())
        })
        .collect();
    let mut prover = Prover::<Scheme, P, _, _, _, _>::new_with_engine(
        engine, params, pk, instances, rng, transcript,
    )?;
    let mut challenges = HashMap::new();
    let phases = prover.phases().to_vec();
    for phase in phases.iter() {
        let mut witnesses = Vec::with_capacity(circuits.len());
        for witness_calc in witness_calcs.iter_mut() {
            witnesses.push(witness_calc.calc(*phase, &challenges)?);
        }
        challenges = prover.commit_phase(*phase, witnesses).unwrap();
    }
    Ok(prover.create_proof()?)
}
/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally.
pub fn create_proof<
    'params,
    Scheme: CommitmentScheme,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWrite<Scheme::Curve, E>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[Vec<Vec<Scheme::Scalar>>],
    rng: R,
    transcript: &mut T,
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let engine = PlonkEngineConfig::build_default();
    create_proof_with_engine::<Scheme, P, _, _, _, _, _>(
        engine, params, pk, circuits, instances, rng, transcript,
    )
}

/// This creates a proof for the provided `circuit` when given the public
/// parameters `params` and the proving key [`ProvingKey`] that was
/// generated previously for the same circuit. The provided `instances`
/// are zero-padded internally. Writes the resulting proof, parameters, verifier key, and instances to files for use in aligned.
pub fn prove_and_serialize_circuit_ipa<
    'params,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let vk = pk.get_vk(); 
    let cs = vk.clone().cs;
    let pk = keygen_pk(&params, vk.clone(), &circuit).expect("pk should not fail");

    let instances: &[&[Fr]] = &[&[circuit.0]];
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        IPACommitmentScheme<G1Affine>,
        ProverIPA<G1Affine>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(
        &params,
        &pk,
        &[circuit.clone()],
        &[instances],
        OsRng,
        &mut transcript,
    )
    .expect("prover should not fail");
    let proof = transcript.finalize();

    assert!(verify_proof::<
        IPACommitmentScheme<G1Affine>,
        VerifierIPA<G1Affine>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<G1Affine>,
    >(
        &params,
        &vk,
        strategy,
        &[&[instances]],
        &mut transcript
    )
    .is_ok());

    //write proof
    std::fs::write("proof_files/proof.bin", &proof[..])
    .expect("should succeed to write new proof");

    //write instances
    let f = File::create("proof_files/pub_input.bin").unwrap();
    let mut writer = BufWriter::new(f);
    instances.to_vec().into_iter().flatten().for_each(|fp| { writer.write(&fp.to_repr()).unwrap(); });
    writer.flush().unwrap();

    let mut vk_buf = Vec::new();
    vk.write(&mut vk_buf, SerdeFormat::RawBytes).unwrap();
    let vk_len = vk_buf.len();
    let mut ipa_params_buf = Vec::new();
    params.write(&mut ipa_params_buf).unwrap();
    let ipa_params_len = ipa_params_buf.len();

    //Write everything to parameters file
    let params_file = File::create("proof_files/params.bin").unwrap();
    let mut writer = BufWriter::new(params_file);
    let cs_buf = bincode::serialize(&cs).unwrap();
    //Write Parameter Lengths as u32
    writer.write_all(&(cs_buf.len() as u32).to_le_bytes()).unwrap();
    writer.write_all(&(vk_len as u32).to_le_bytes()).unwrap();
    writer.write_all(&(ipa_params_len as u32).to_le_bytes()).unwrap();
    //Write Parameters
    writer.write_all(&cs_buf).unwrap();
    writer.write_all(&vk_buf).unwrap();
    writer.write_all(&ipa_params_buf).unwrap();
    writer.flush().unwrap();
    Ok(())
}

pub fn prove_and_serialize_circuit_kzg<
    'params,
    P: commitment::Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    ConcreteCircuit: Circuit<Scheme::Scalar>,
>(
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: &[ConcreteCircuit],
    instances: &[&[&[Scheme::Scalar]]],
) -> Result<(), Error>
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(
        &params,
        &pk,
        &[circuit.clone()],
        &[instances],
        OsRng,
        &mut transcript,
    )
    .expect("prover should not fail");
    let proof = transcript.finalize();

    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(&params, &vk, strategy, &[&[instances]], &mut transcript)
    .is_ok());

    //write proof
    std::fs::write("proof_files/proof.bin", &proof[..])
    .expect("should succeed to write new proof");

    //write instances
    let f = File::create("proof_files/pub_input.bin").unwrap();
    let mut writer = BufWriter::new(f);
    instances.to_vec().into_iter().flatten().for_each(|fp| { writer.write(&fp.to_repr()).unwrap(); });
    writer.flush().unwrap();

    let mut vk_buf = Vec::new();
    vk.write(&mut vk_buf, SerdeFormat::RawBytes).unwrap();
    let vk_len = vk_buf.len();
    let mut kzg_params_buf = Vec::new();
    params.write(&mut kzg_params_buf).unwrap();
    let kzg_params_len = kzg_params_buf.len();

    //Write everything to parameters file
    let params_file = File::create("proof_files/params.bin").unwrap();
    let mut writer = BufWriter::new(params_file);
    let cs_buf = bincode::serialize(&cs).unwrap();
    //Write Parameter Lengths as u32
    writer.write_all(&(cs_buf.len() as u32).to_le_bytes()).unwrap();
    writer.write_all(&(vk_len as u32).to_le_bytes()).unwrap();
    writer.write_all(&(kzg_params_len as u32).to_le_bytes()).unwrap();
    //Write Parameters
    writer.write_all(&cs_buf).unwrap();
    writer.write_all(&vk_buf).unwrap();
    writer.write_all(&kzg_params_buf).unwrap();
    writer.flush().unwrap();
    Ok(())
}



#[test]
fn test_create_proof() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk, keygen_vk, ConstraintSystem, ErrorFront},
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverSHPLONK,
        },
        transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer},
    };
    use halo2_middleware::ff::Field;
    use halo2curves::bn256::Bn256;
    use rand_core::OsRng;

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), ErrorFront> {
            Ok(())
        }
    }

    let params: ParamsKZG<Bn256> = ParamsKZG::setup(3, OsRng);
    let vk = keygen_vk(&params, &MyCircuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &MyCircuit).expect("keygen_pk should not fail");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    // Create proof with wrong number of instances
    let proof = create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _, _>(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[],
        OsRng,
        &mut transcript,
    );
    assert!(matches!(
        proof.unwrap_err(),
        Error::Backend(ErrorBack::InvalidInstances)
    ));

    // Create proof with correct number of instances
    create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _, _>(
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[vec![], vec![]],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
}

#[test]
fn test_create_proof_custom() {
    use crate::{
        circuit::SimpleFloorPlanner,
        plonk::{keygen_pk_custom, keygen_vk_custom, ConstraintSystem, ErrorFront},
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverSHPLONK,
        },
        transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer},
    };
    use halo2_middleware::ff::Field;
    use halo2curves::bn256::Bn256;
    use rand_core::OsRng;

    #[derive(Clone, Copy)]
    struct MyCircuit;

    impl<F: Field> Circuit<F> for MyCircuit {
        type Config = ();
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            *self
        }

        fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {}

        fn synthesize(
            &self,
            _config: Self::Config,
            _layouter: impl crate::circuit::Layouter<F>,
        ) -> Result<(), ErrorFront> {
            Ok(())
        }
    }

    let params: ParamsKZG<Bn256> = ParamsKZG::setup(3, OsRng);
    let compress_selectors = true;
    let vk = keygen_vk_custom(&params, &MyCircuit, compress_selectors)
        .expect("keygen_vk_custom should not fail");
    let pk = keygen_pk_custom(&params, vk, &MyCircuit, compress_selectors)
        .expect("keygen_pk_custom should not fail");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    let engine = PlonkEngineConfig::build_default();

    create_proof_with_engine::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _, _, _>(
        engine,
        &params,
        &pk,
        &[MyCircuit, MyCircuit],
        &[vec![], vec![]],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
}
