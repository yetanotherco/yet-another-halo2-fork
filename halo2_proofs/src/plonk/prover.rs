use crate::plonk::{keygen_pk, verify_proof, Error, ErrorBack, ErrorFront};
use crate::poly::commitment::{self, CommitmentScheme, Params};
use crate::transcript::{EncodedChallenge, TranscriptWrite};
use group::ff::PrimeField;
use halo2_backend::helpers::SerdeFormat;
use halo2_backend::plonk::circuit::ConstraintSystemBack;
use halo2_backend::plonk::VerifyingKey;
use halo2_backend::plonk::{prover::Prover, ProvingKey};
use halo2_backend::poly::ipa::{
    commitment::{IPACommitmentScheme, ParamsIPA},
    multiopen::{ProverIPA, VerifierIPA},
    strategy::SingleStrategy as IPAStrategy,
};
use halo2_backend::poly::{
    kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG},
        multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy as KZGStrategy,
    },
    VerificationStrategy,
};
use halo2_backend::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
};
use halo2_frontend::plonk::{Circuit, ConstraintSystem};
use halo2_frontend::{
    circuit::{Layouter, SimpleFloorPlanner, Value, WitnessCalculator},
    plonk::{Advice, Column, Fixed, Instance},
};
use halo2_middleware::{
    ff::{FromUniformBytes, WithSmallOrderMulGroup},
    poly::Rotation,
    zal::{
        impls::{PlonkEngine, PlonkEngineConfig},
        traits::MsmAccel,
    },
};
use halo2curves::bn256::{Bn256, Fr, G1Affine};
use log::error;
use rand_core::{OsRng, RngCore};
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{BufWriter, ErrorKind, Read, Write};
use std::path::Path;

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

// Reads all parameters
/// Writes ConstraintSystemBack, VerifyingKey, and ProverParams to a file to be sent to aligned.
pub fn write_params(
    params_buf: &[u8],
    cs: ConstraintSystemBack<Fr>,
    vk_buf: &[u8],
    params_path: &str,
) -> Result<(), Error> {
    let vk_len = vk_buf.len();
    let params_len = params_buf.len();

    //Write everything to parameters file
    let params_file = File::create(params_path).unwrap();
    let mut writer = BufWriter::new(params_file);
    let cs_buf = bincode::serialize(&cs).unwrap();
    //Write Parameter Lengths as u32
    writer
        .write_all(&(cs_buf.len() as u32).to_le_bytes())
        .unwrap();
    writer.write_all(&(vk_len as u32).to_le_bytes()).unwrap();
    writer
        .write_all(&(params_len as u32).to_le_bytes())
        .unwrap();
    //Write Parameters
    writer.write_all(&cs_buf).unwrap();
    writer.write_all(vk_buf).unwrap();
    writer.write_all(params_buf).unwrap();
    writer.flush().unwrap();
    Ok(())
}

/// Reads Public inputs values from a data buffer
pub fn read_fr(mut buf: &[u8]) -> Result<Vec<Fr>, ErrorKind> {
    let mut instances = Vec::with_capacity(buf.len() / 32);
    // Buffer to store each 32-byte slice
    let mut buffer = [0; 32];

    loop {
        // Read 32 bytes into the buffer
        match buf.read_exact(&mut buffer) {
            Ok(_) => {
                instances.push(Fr::from_bytes(&buffer).unwrap());
            }
            Err(ref e) if e.kind() == ErrorKind::UnexpectedEof => {
                // If end of file reached, break the loop
                break;
            }
            Err(e) => {
                eprintln!("Error Deserializing Public Inputs: {}", e);
                return Err(ErrorKind::Other);
            }
        }
    }

    Ok(instances)
}

/// Reads parameter values from data buffer and splits them into separate buffers for deserialization
pub fn read_params(buf: &[u8]) -> Result<(&[u8], &[u8], &[u8]), ErrorKind> {
    // Deserialize
    let cs_len_buf: [u8; 4] = buf[..4]
        .try_into()
        .map_err(|_| "Failed to convert slice to [u8; 4]")
        .unwrap();
    let cs_len = u32::from_le_bytes(cs_len_buf) as usize;
    let vk_len_buf: [u8; 4] = buf[4..8]
        .try_into()
        .map_err(|_| "Failed to convert slice to [u8; 4]")
        .unwrap();
    let vk_len = u32::from_le_bytes(vk_len_buf) as usize;
    let params_len_buf: [u8; 4] = buf[8..12]
        .try_into()
        .map_err(|_| "Failed to convert slice to [u8; 4]")
        .unwrap();
    let params_len = u32::from_le_bytes(params_len_buf) as usize;

    //Verify declared lengths are less than total length.
    if (12 + cs_len + vk_len + params_len) > buf.len() {
        error!("Serialized parameter lengths greater than parameter bytes length");
        return Err(ErrorKind::Other);
    }

    // Select Constraint System Bytes
    let cs_offset = 12;
    let cs_buffer = &buf[cs_offset..(cs_offset + cs_len)];

    // Select Verifier Key Bytes
    let vk_offset = cs_offset + cs_len;
    let vk_buffer = &buf[vk_offset..(vk_offset + vk_len)];

    // Select ipa Params Bytes
    let params_offset = vk_offset + vk_len;
    let params_buffer = &buf[params_offset..(params_offset + params_len)];

    Ok((cs_buffer, vk_buffer, params_buffer))
}

/// Proves, serializes, and writes the resulting proof, parameters, verifier key, and instances to local files to be sent to Aligned.
pub fn prove_and_serialize_ipa_circuit<ConcreteCircuit: Circuit<Fr>>(
    params: &ParamsIPA<G1Affine>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    public_inputs: &[Vec<Vec<Fr>>],
) -> Result<(), Error> {
    let vk = pk.get_vk();
    let cs = vk.clone().cs;
    let pk = keygen_pk(params, vk.clone(), &circuit).expect("pk should not fail");

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        IPACommitmentScheme<G1Affine>,
        ProverIPA<G1Affine>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(
        params,
        &pk,
        &[circuit],
        public_inputs,
        OsRng,
        &mut transcript,
    )
    .expect("prover should not fail");
    let proof = transcript.finalize();

    let strategy = IPAStrategy::new(params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        IPACommitmentScheme<G1Affine>,
        VerifierIPA<G1Affine>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        IPAStrategy<G1Affine>,
    >(params, vk, strategy, public_inputs, &mut transcript)
    .is_ok());

    if !Path::new("./proof_files").exists() {
        fs::create_dir_all("./proof_files").unwrap();
    }

    std::fs::write("proof_files/proof.bin", &proof[..]).expect("should succeed to write new proof");

    let f = File::create("proof_files/public_input.bin").unwrap();
    let mut writer = BufWriter::new(f);
    public_inputs.iter().flatten().cloned().for_each(|f| {
        f.into_iter().for_each(|fp| {
            writer.write_all(&fp.to_repr()).unwrap();
        })
    });
    writer.flush().unwrap();

    let mut vk_buf = Vec::new();
    vk.write(&mut vk_buf, SerdeFormat::RawBytes).unwrap();

    let mut params_buf = Vec::new();
    params.write(&mut params_buf).unwrap();

    write_params(&params_buf, cs, &vk_buf, "proof_files/params.bin").unwrap();
    Ok(())
}

/// Proves, serializes, and writes the resulting proof, parameters, verifier key, and instances to local files to be sent to Aligned.
pub fn prove_and_serialize_kzg_circuit<ConcreteCircuit: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    vk: &VerifyingKey<G1Affine>,
    circuit: ConcreteCircuit,
    public_inputs: &[Vec<Vec<Fr>>],
) -> Result<(), Error> {
    let cs = vk.clone().cs;
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(
        params,
        pk,
        &[circuit],
        public_inputs,
        OsRng,
        &mut transcript,
    )
    .expect("prover should not fail");
    let proof = transcript.finalize();

    let verifier_params = params.verifier_params();
    let strategy = KZGStrategy::new(&verifier_params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        KZGStrategy<Bn256>,
    >(
        &verifier_params,
        vk,
        strategy,
        public_inputs,
        &mut transcript
    )
    .is_ok());

    if !Path::new("./proof_files").exists() {
        fs::create_dir_all("./proof_files").unwrap();
    }

    std::fs::write("proof_files/proof.bin", &proof[..]).expect("should succeed to write new proof");

    let f = File::create("proof_files/public_input.bin").unwrap();
    let mut writer = BufWriter::new(f);
    public_inputs.iter().flatten().cloned().for_each(|f| {
        f.into_iter().for_each(|fp| {
            writer.write_all(&fp.to_repr()).unwrap();
        })
    });
    writer.flush().unwrap();

    let mut vk_buf = Vec::new();
    vk.write(&mut vk_buf, SerdeFormat::RawBytes).unwrap();

    let mut params_buf = Vec::new();
    verifier_params.write(&mut params_buf).unwrap();

    write_params(&params_buf, cs, &vk_buf, "proof_files/params.bin").unwrap();
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

// HALO2 Circuit Example
/// StandardPlonk Circuit Configuration
#[derive(Clone, Copy, Debug)]
pub struct StandardPlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    q_a: Column<Fixed>,
    q_b: Column<Fixed>,
    q_c: Column<Fixed>,
    q_ab: Column<Fixed>,
    constant: Column<Fixed>,
    #[allow(dead_code)]
    instance: Column<Instance>,
}

impl StandardPlonkConfig {
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
        let [a, b, c] = [(); 3].map(|_| meta.advice_column());
        let [q_a, q_b, q_c, q_ab, constant] = [(); 5].map(|_| meta.fixed_column());
        let instance = meta.instance_column();

        [a, b, c].map(|column| meta.enable_equality(column));

        meta.create_gate(
            "q_a·a + q_b·b + q_c·c + q_ab·a·b + constant + instance = 0",
            |meta| {
                let [a, b, c] = [a, b, c].map(|column| meta.query_advice(column, Rotation::cur()));
                let [q_a, q_b, q_c, q_ab, constant] = [q_a, q_b, q_c, q_ab, constant]
                    .map(|column| meta.query_fixed(column, Rotation::cur()));
                let instance = meta.query_instance(instance, Rotation::cur());
                Some(
                    q_a * a.clone()
                        + q_b * b.clone()
                        + q_c * c
                        + q_ab * a * b
                        + constant
                        + instance,
                )
            },
        );

        StandardPlonkConfig {
            a,
            b,
            c,
            q_a,
            q_b,
            q_c,
            q_ab,
            constant,
            instance,
        }
    }
}

/// StandardPlonk Circuit for testing
#[derive(Clone, Default, Debug)]
pub struct StandardPlonk(pub Fr);

impl Circuit<Fr> for StandardPlonk {
    type Config = StandardPlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        StandardPlonkConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), ErrorFront> {
        layouter.assign_region(
            || "",
            |mut region| {
                region.assign_advice(|| "", config.a, 0, || Value::known(self.0))?;
                region.assign_fixed(|| "", config.q_a, 0, || Value::known(-Fr::one()))?;

                region.assign_advice(|| "", config.a, 1, || Value::known(-Fr::from(5u64)))?;
                for (idx, column) in (1..).zip([
                    config.q_a,
                    config.q_b,
                    config.q_c,
                    config.q_ab,
                    config.constant,
                ]) {
                    region.assign_fixed(|| "", column, 1, || Value::known(Fr::from(idx as u64)))?;
                }

                let a = region.assign_advice(|| "", config.a, 2, || Value::known(Fr::one()))?;
                a.copy_advice(|| "", &mut region, config.b, 3)?;
                a.copy_advice(|| "", &mut region, config.c, 4)?;
                Ok(())
            },
        )
    }
}

#[test]
fn test_proof_serialization() {
    use crate::{plonk::keygen_vk_custom, poly::kzg::commitment::ParamsKZG};
    use halo2_backend::poly::commitment::ParamsProver;
    use halo2_backend::poly::kzg::strategy::SingleStrategy;
    use halo2_middleware::ff::Field;
    use std::io::BufReader;

    let circuit = StandardPlonk(Fr::random(OsRng));
    let params = ParamsKZG::setup(4, OsRng);
    let compress_selectors = true;
    let vk = keygen_vk_custom(&params, &circuit, compress_selectors).expect("vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &circuit).expect("pk should not fail");
    let instances: Vec<Vec<Fr>> = vec![vec![circuit.0]];
    prove_and_serialize_kzg_circuit(&params, &pk, &vk, circuit.clone(), &vec![instances.clone()])
        .unwrap();

    let proof = std::fs::read("proof_files/proof.bin").expect("should succeed to read proof");
    let pub_input = std::fs::read("proof_files/public_input.bin").unwrap();
    let instances = read_fr(&pub_input).unwrap();

    let mut f = File::open("proof_files/params.bin").unwrap();
    let mut params_buf = Vec::new();
    f.read_to_end(&mut params_buf).unwrap();

    let (cs_bytes, vk_bytes, vk_params_bytes) = read_params(&params_buf).unwrap();

    let cs = bincode::deserialize(&cs_bytes).unwrap();
    let vk = VerifyingKey::<G1Affine>::read(
        &mut BufReader::new(vk_bytes),
        SerdeFormat::RawBytes,
        cs,
    )
    .unwrap();
    let vk_params =
        Params::read::<_>(&mut BufReader::new(vk_params_bytes)).unwrap();

    let strategy = SingleStrategy::new(&vk_params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<Bn256>,
    >(
        &vk_params,
        &vk,
        strategy,
        &[vec![instances]],
        &mut transcript
    )
    .is_ok());

    let params = ParamsIPA::<G1Affine>::new(4);
    let compress_selectors = true;
    let vk = keygen_vk_custom(&params, &circuit, compress_selectors).expect("vk should not fail");
    let pk = keygen_pk(&params, vk.clone(), &circuit).expect("pk should not fail");
    let public_inputs: Vec<Vec<Fr>> = vec![vec![circuit.0]];
    prove_and_serialize_ipa_circuit(&params, &pk, circuit, &vec![public_inputs]).unwrap()
}
