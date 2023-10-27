#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, create_proof, Error, Fixed, keygen_pk, keygen_vk, verify_proof};
use halo2_proofs::halo2curves::bls12_381::{Bls12, G1Affine, Scalar};
use halo2_proofs::halo2curves::ff::Field;
use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::dev::MockProver;
use halo2_proofs::poly::commitment::Verifier;
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
use halo2_proofs::poly::Rotation;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer};
use rand_core::OsRng;

#[derive(Clone)]
struct PlonkConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    sa: Column<Fixed>,
    sb: Column<Fixed>,
    sc: Column<Fixed>,
    sm: Column<Fixed>,
}

struct StandardPlonk {
    config: PlonkConfig,
}

impl StandardPlonk {
    fn new(config: PlonkConfig) -> Self {
        Self {
            config
        }
    }

    fn multiply(
        &self,
        layouter: &mut impl Layouter<Scalar>,
        a: Value<Scalar>,
        b: Value<Scalar>,
    ) -> Result<AssignedCell<Scalar, Scalar>, Error> {
        layouter.assign_region(
            || "Multiply region",
            |mut region| {
                let lhs = region.assign_advice(
                    || "lhs multiplication",
                    self.config.a,
                    0,
                    || a
                );

                let rhs = region.assign_advice(
                    || "rhs multiplication",
                    self.config.b,
                    0,
                    || b,
                );

                let result = a * b;

                let out = region.assign_advice(
                    || "out mult",
                    self.config.c,
                    0,
                    || result
                );

                region.assign_fixed(
                    || "selector a",
                    self.config.sa,
                    0,
                    || Value::known(Scalar::ZERO),
                )?;
                region.assign_fixed(
                    || "selector b",
                    self.config.sb,
                    0,
                    || Value::known(Scalar::ZERO),
                )?;
                region.assign_fixed(
                    || "selector c",
                    self.config.sc,
                    0,
                    || Value::known(-Scalar::ONE),
                )?;

                region.assign_fixed(
                    || "selector c",
                    self.config.sm,
                    0,
                    || Value::known(Scalar::ONE),
                )?;

                out
            }
        )
    }

    fn add(
        &self,
        layouter: &mut impl Layouter<Scalar>,
        a: Value<Scalar>,
        b: Value<Scalar>,
    ) -> Result<AssignedCell<Scalar, Scalar>, Error> {
        layouter.assign_region(
            || "Add region",
            |mut region| {
                let lhs = region.assign_advice(
                    || "lhs add",
                    self.config.a,
                    0,
                    || a
                );

                let rhs = region.assign_advice(
                    || "rhs add",
                    self.config.b,
                    0,
                    || b,
                );

                let result = a + b;

                let out = region.assign_advice(
                    || "out add",
                    self.config.c,
                    0,
                    || result
                );

                region.assign_fixed(
                    || "selector a",
                    self.config.sa,
                    0,
                    || Value::known(Scalar::ONE),
                )?;
                region.assign_fixed(
                    || "selector b",
                    self.config.sb,
                    0,
                    || Value::known(Scalar::ONE),
                )?;
                region.assign_fixed(
                    || "selector c",
                    self.config.sc,
                    0,
                    || Value::known(-Scalar::ONE),
                )?;

                region.assign_fixed(
                    || "selector c",
                    self.config.sm,
                    0,
                    || Value::known(Scalar::ZERO),
                )?;

                out
            }
        )
    }

    fn assert_equal(
        &self,
        layouter: &mut impl Layouter<Scalar>,
        lhs: AssignedCell<Scalar, Scalar>,
        rhs: AssignedCell<Scalar, Scalar>,
    ) -> Result<(), Error> {
        layouter.assign_region(|| "equality", |mut region| region.constrain_equal(lhs.cell(), rhs.cell()))
    }
}

#[derive(Default, Debug)]
struct ExampleCircuit {
    secret_a: Scalar,
    secret_b: Scalar,
}

impl Circuit<Scalar> for ExampleCircuit {
    type Config = PlonkConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        ExampleCircuit::default()
    }

    fn configure(meta: &mut ConstraintSystem<Scalar>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();

        meta.enable_equality(c);

        let sa = meta.fixed_column();
        let sb = meta.fixed_column();
        let sc = meta.fixed_column();
        let sm = meta.fixed_column();


        // f(x) = Q_L(x)a(x) + Q_r(x)b(x) + Qo(x)c(x) + Qm(x)a(x)b(x)
        meta.create_gate(
            "Plonk gate",
            |meta| {
                let a = meta.query_advice(a, Rotation::cur());
                let b = meta.query_advice(b, Rotation::cur());
                let c = meta.query_advice(c, Rotation::cur());

                let sa = meta.query_fixed(sa, Rotation::cur());
                let sb = meta.query_fixed(sb, Rotation::cur());
                let sc = meta.query_fixed(sc, Rotation::cur());
                let sm = meta.query_fixed(sm, Rotation::cur());

                vec![sa * a.clone() + sb * b.clone() + sm * a * b + sc * c]
            }
        );

        PlonkConfig {
            a,
            b,
            c,
            sa,
            sb,
            sc,
            sm
        }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Scalar>) -> Result<(), Error> {
        let plonk = StandardPlonk::new(config);

        let input_a = Value::known(self.secret_a.clone());
        let input_b = Value::known(self.secret_b.clone());

        let mul = plonk.multiply(&mut layouter, input_a, input_b)?;
        let add = plonk.add(&mut layouter, input_a, input_b)?;

        // assert mul = add
        plonk.assert_equal(&mut layouter, mul, add)?;

        Ok(())
    }
}


fn main() {
    // proving that we know a tuple (a,b) s.t a * b = a + b (only solutions are (2,2) and (0,0))
    let example = ExampleCircuit { secret_a: Scalar::from(0), secret_b: Scalar::from(0) };
    // println!("Example: {:?}", example);

    let mut rng = OsRng;
    let params: ParamsKZG<Bls12> = ParamsKZG::setup(3, &mut rng);
    // println!("Params: {:?}", params);
    let vk = keygen_vk(&params, &example).expect("VK failed to generate");
    // println!("VK: {:?}", vk);
    let pk = keygen_pk(&params, vk, &example).expect("PK failed to generate");
    // println!("PK: {:?}", pk);

    let mut transcript = Blake2bWrite::<_, _, Challenge255<G1Affine>>::init(vec![]);
    // println!("Transcript0: {:?}", transcript);

    create_proof::<KZGCommitmentScheme<Bls12>, ProverGWC<Bls12>, _, _, _, _>(
        &params,
        &pk,
        &[example],
        &[&[]],
        rng,
        &mut transcript,
    ).expect("Proof generation failed");
 
    // println!("Transcript1: {:?}", transcript);

    let proof = transcript.finalize();
    // println!("Proof: {:?}", proof);

    let verifier = SingleStrategy::new(&params);
    let mut transcriptt = Blake2bRead::<_, _, Challenge255<G1Affine>>::init(proof.as_slice());
    // println!("Transcript2: {:?}", transcriptt);

    // println!("Transcript: {:?}", transcript);
    verify_proof::<_, VerifierGWC<Bls12>, _, _, _>(
        &params,
        &pk.get_vk(),
        verifier,
        &[&[]],
        &mut transcriptt
    ).expect("Verification failed");
    // println!("Transcript: {:?}", transcript);
    // let pi: Vec<Vec<_>> = vec![vec![];0]; // instead of vec![vec![]]
    // let circuit = MockProver::run(3, &example, pi).expect("Prover failed");
    
    // circuit.assert_satisfied_par();

    println!("Passed");
}