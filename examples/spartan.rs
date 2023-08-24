use clap::Parser;
use halo2_base::gates::{GateChip, GateInstructions};
use halo2_base::utils::ScalarField;
use halo2_base::AssignedValue;
#[allow(unused_imports)]
use halo2_base::{
    Context,
    QuantumCell::{Constant, Existing, Witness},
};
use halo2_scaffold::scaffold::cmd::Cli;
use halo2_scaffold::scaffold::run_builder_on_inputs;
use serde::{Deserialize, Serialize};

use bellperson::gadgets::num::AllocatedNum;
use bellperson::{Circuit, ConstraintSystem, SynthesisError};
use pasta_curves::group::ff::PrimeField;
use spartan2::traits::snark::RelaxedR1CSSNARKTrait;
use spartan2::traits::Group;
use spartan2::{provider, spartan, SNARK};
use std::marker::PhantomData;

#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CircuitInput<G, S, C>
where
    G: Group,
    S: RelaxedR1CSSNARKTrait<G>,
    C: Circuit<G::Scalar>,
{
    pub snark: SNARK<G, S, C>,
    pub x: String,
}

// this algorithm takes a public input x, computes x^2 + 72, and outputs the result as public output
fn spartan_recursion<
    F: ScalarField,
    G: Group,
    S: RelaxedR1CSSNARKTrait<G>,
    C: Circuit<G::Scalar>,
>(
    ctx: &mut Context<F>,
    input: CircuitInput<G, S, C>,
    make_public: &mut Vec<AssignedValue<F>>,
) {
    let x = F::from_str_vartime(&input.x).expect("deserialize field element should not fail");
    // `Context` can roughly be thought of as a single-threaded execution trace of a program we want to ZK prove. We do some post-processing on `Context` to optimally divide the execution trace into multiple columns in a PLONKish arithmetization
    // More advanced usage with multi-threaded witness generation is possible, but we do not explain it here

    // first we load a number `x` into as system, as a "witness"
    let x = ctx.load_witness(x);
    // by default, all numbers in the system are private
    // we can make it public like so:
    make_public.push(x);

    // create a Gate chip that contains methods for basic arithmetic operations
    let gate = GateChip::<F>::default();

    // ===== way 1 =====
    // now we can perform arithmetic operations almost like a normal program using halo2-lib API functions
    // square x
    let x_sq = gate.mul(ctx, x, x);

    // x^2 + 72
    let c = F::from(72);
    // the implicit type of most variables is an "Existing" assigned value
    // a known constant is a separate type that we specify by `Constant(c)`:
    let out = gate.add(ctx, x_sq, Constant(c));
    // Halo2 does not distinguish between public inputs vs outputs because the verifier seems them all at the same time
    // However in traditional terms, `out` is our output number. It is currently still private.
    // Let's make it public:
    make_public.push(out);
    // ==== way 2 =======
    // here is a more optimal way to compute x^2 + 72 using the lower level `assign_region` API:
    let val = *x.value() * x.value() + c;
    let _val_assigned =
        ctx.assign_region_last([Constant(c), Existing(x), Existing(x), Witness(val)], [0]);
    // the `[0]` tells us to turn on a vertical `a + b * c = d` gate at row position 0.
    // this imposes the constraint c + x * x = val

    // ==== way 3 ======
    // this does the exact same thing as way 2, but with a pre-existing function
    let _val_assigned = gate.mul_add(ctx, x, x, Constant(c));

    println!("x: {:?}", x.value());
    println!("val_assigned: {:?}", out.value());
    assert_eq!(*x.value() * x.value() + c, *out.value());
}

#[derive(Clone, Debug, Default)]
struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
}

impl<F> Circuit<F> for CubicCircuit<F>
where
    F: PrimeField,
{
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
        let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(F::ONE + F::ONE))?;
        let x_sq = x.square(cs.namespace(|| "x_sq"))?;
        let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), &x)?;
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
            Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
        })?;

        cs.enforce(
            || "y = x^3 + x + 5",
            |lc| {
                lc + x_cu.get_variable()
                    + x.get_variable()
                    + CS::one()
                    + CS::one()
                    + CS::one()
                    + CS::one()
                    + CS::one()
            },
            |lc| lc + CS::one(),
            |lc| lc + y.get_variable(),
        );

        let _ = y.inputize(cs.namespace(|| "output"));

        Ok(())
    }
}

fn main() {
    env_logger::init();
    type G = pasta_curves::pallas::Point;
    type EE = provider::ipa_pc::EvaluationEngine<G>;
    type S = spartan::snark::RelaxedR1CSSNARK<G, EE>;

    let circuit = CubicCircuit::default();

    // produce keys
    let (pk, vk) =
        SNARK::<G, S, CubicCircuit<<G as Group>::Scalar>>::setup(circuit.clone()).unwrap();

    // produce a SNARK
    let res: Result<
        SNARK<
            pasta_curves::Ep,
            spartan::snark::RelaxedR1CSSNARK<
                pasta_curves::Ep,
                provider::ipa_pc::EvaluationEngine<pasta_curves::Ep>,
            >,
            CubicCircuit<pasta_curves::Fq>,
        >,
        spartan2::errors::SpartanError,
    > = SNARK::prove(&pk, circuit);
    assert!(res.is_ok());
    let snark: SNARK<
        pasta_curves::Ep,
        spartan::snark::RelaxedR1CSSNARK<
            pasta_curves::Ep,
            provider::ipa_pc::EvaluationEngine<pasta_curves::Ep>,
        >,
        CubicCircuit<pasta_curves::Fq>,
    > = res.unwrap();

    // verify the SNARK
    let res = snark.verify(&vk);
    assert!(res.is_ok());

    let io = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(io, vec![<G as Group>::Scalar::from(15u64)]);

    let args = Cli::parse();

    let input = CircuitInput { snark, x: String::from("10") };
    run_builder_on_inputs(
        |builder, input, public| spartan_recursion(builder.main(0), input, public),
        args,
        input,
    );
}
