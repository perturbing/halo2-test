#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]
use core::num;

use halo2_proofs::halo2curves::bn256::G1;
use halo2_proofs::plonk::{Advice, vanishing, Circuit, Column, ConstraintSystem, create_proof, Error, Fixed, keygen_pk, keygen_vk, verify_proof};
use halo2_proofs::halo2curves::bls12_381::{Bls12, G1Affine, Scalar};
use halo2_proofs::halo2curves::ff::Field;
use halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::dev::MockProver;
use halo2_proofs::poly::commitment::Verifier;
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverGWC, VerifierGWC};
use halo2_proofs::poly::Rotation;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer, TranscriptRead};
use halo2_proofs::transcript::Transcript;
use halo2_proofs::poly::commitment::Params;
// use rand_core::{OsRng, RngCore};
use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;


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

    // let mut rng = OsRng;
    let seed = [0u8; 32];  // Choose a fixed seed for testing
    let mut rng: StdRng = SeedableRng::from_seed(seed);

    let params: ParamsKZG<Bls12> = ParamsKZG::setup(3, &mut rng);

    let vk = keygen_vk(&params, &example).expect("VK failed to generate");
    // println!("VK: {:?}", vk.permutation());
    let pk = keygen_pk(&params, vk, &example).expect("PK failed to generate");
    // println!("PK: {:?}", pk);

    let mut transcript = Blake2bWrite::<_, _, Challenge255<G1Affine>>::init(vec![]);

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
    let mut transcript2 = Blake2bRead::<_, _, Challenge255<G1Affine>>::init(proof.as_slice());
    // println!("Transcript2: {:?}", transcript2);

    verify_proof::<_, VerifierGWC<Bls12>, _, _, _>(
        &params,
        &pk.get_vk(),
        verifier,
        &[&[]],
        &mut transcript2
    ).expect("Verification failed");

    // mimic the verifier from this point

    let mut transcript3 = Blake2bRead::<_, _, Challenge255<G1Affine>>::init(proof.as_slice());
    // println!("Transcript3: {:?}", transcript3);

    // add verifiers key hash to hash buffer
    pk.get_vk().hash_into(&mut transcript3).expect("Failed to hash into");

    // add first three point to hash buffer and remove from transcript
    let advice_commitments: Vec<G1Affine> = (0..3)
        .map(|_| transcript3.read_point().expect("Failed to read point"))
        .collect();
    // println!("advice_commitments1: {:?}", advice_commitments);

    let challenges: Vec<G1Affine> = [].to_vec();
    // println!("challenges: {:?}", challenges);

    let theta = transcript3.squeeze_challenge_scalar::<()>();
    // println!("theta1: {:?}", theta);

    let lookups_permuted: Vec<Vec<G1Affine>> = [[].to_vec()].to_vec();
    // println!("lookups_permuted: {:?}", lookups_permuted);

    let beta = transcript3.squeeze_challenge_scalar::<()>();
    // println!("beta1: {:?}", beta);

    let gamma = transcript3.squeeze_challenge_scalar::<()>();
    // println!("gamma1: {:?}", gamma);

    let permutations_committed = transcript3.read_point().expect("Failed to read point");
    // println!("permutations_committed1: {:?}", permutations_committed);

    let lookups_committed: Vec<Vec<G1Affine>> = [[].to_vec()].to_vec();
    // println!("lookups_committed1: {:?}", lookups_committed);

    // this is part of vanishing object
    let random_poly_commitment = transcript3.read_point().expect("Failed to read point");
    // println!("random_poly_commitment: {:?}", random_poly_commitment);
    
    let y = transcript3.squeeze_challenge_scalar::<()>();
    // println!("y1: {:?}", y);

    // this is part of vanishing object
    let h_commitments: Vec<G1Affine> = (0..2)
        .map(|_| transcript3.read_point().expect("Failed to read point"))
        .collect();
    // println!("h_commitments1: {:?}", h_commitments);

    let x = transcript3.squeeze_challenge_scalar::<()>();
    // println!("x1: {:?}", x);

    let xn = x.pow(&[params.n() as u64, 0, 0, 0]);
    // println!("xn1: {:?}", xn);

    let min_rotation: i32 = 0;
    let max_rotation: i32 = 0;
    let max_instance_len: i32 = 0;

    // there are no public inputs (instances), so it makes sense that this is []
    let l_i_s = pk.get_vk().get_domain().l_i_range(
        *x,
        xn,
        -max_rotation..max_instance_len as i32 + min_rotation.abs());
    
    let instances: Vec<Vec<Scalar>> = [[].to_vec()].to_vec();
    // println!("instances1: {:?}", instances);

    let advice_evals = (0..3)
        .map(|_| transcript3.read_scalar().expect(""))
        .collect::<Vec<_>>();
    // println!("advice_evals1: {:?}", advice_evals);

    let fixed_evals = (0..4)
        .map(|_| transcript3.read_scalar().expect(""))
        .collect::<Vec<_>>();
    // println!("fixed_evals1: {:?}", fixed_evals);
    
    // part of vanishing object
    let random_eval : Scalar = transcript3.read_scalar().expect("");
    // println!("random_eval1: {:?}", random_eval);

    // this is contained in the permutatuins_common object
    let permutation_evals = (0..1)
        .map(|_| transcript3.read_scalar().expect(""))
        .collect::<Vec<_>>();
    // println!("permutation_evals1: {:?}", permutation_evals);

    // note that the permuatuins_evaluated objectet also has the commited G1 point 
    // for the permutation
    let permutation_product_eval = transcript3.read_scalar().expect("");
    // println!("permutation_product_eval1: {:?}", permutation_product_eval);

    let permutation_product_next_eval = transcript3.read_scalar().expect("");
    // println!("permutation_product_next_eval1: {:?}", permutation_product_next_eval);

    let lookups_evaluated: Vec<Vec<Scalar>> = [[].to_vec()].to_vec();
    // println!("lookups_evaluated1: {:?}", lookups_evaluated);

    // TODO: Understand construction of queries and below link with pairing check

    // this is inside the gwc verifier https://github.com/perturbing/halo2/blob/main/halo2_proofs/src/poly/kzg/multiopen/gwc/verifier.rs
    let v = transcript3.squeeze_challenge_scalar::<()>();
    println!("v1: {:?}", v);

    let w: Vec<G1Affine> = (0..2)
        .map(|_| transcript3.read_point().expect(""))
        .collect::<Vec<_>>();
    // println!("w1: {:?}", w);

    let u = transcript3.squeeze_challenge_scalar::<()>();
    println!("u1: {:?}", u);
    
    println!("Passed");
}

    // let permutations_common_non_evaluated  = pk.get_vk().permutation();
    // println!("permutations_common_non_evaluated: {:?}", permutations_common_non_evaluated);