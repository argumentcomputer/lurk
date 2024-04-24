mod calculator;
mod dummy_hasher;
mod pointers;
mod store;

use p3_baby_bear::BabyBear;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::time::Instant;
use wp1_core::{
    stark::StarkGenericConfig,
    utils::{
        uni_stark_prove_with_public_values as prove, uni_stark_verify_with_public_values as verify,
        BabyBearPoseidon2,
    },
};

use crate::{calculator::Calculator, store::Store};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let store = Store::<BabyBear>::default();
    let nil = store.nil();

    let mut editor = DefaultEditor::new()?;
    loop {
        match editor.readline("> ") {
            Ok(input) => {
                let entry = store.parse(&input);
                let now = Instant::now();
                let mut frames = Calculator::compute_frames(entry, nil, &store);
                let elapsed = now.elapsed().as_micros();
                let last_frame = frames.last().unwrap();
                let resulting_stack = last_frame.o_stack;
                let [car, _] = store.decons(&resulting_stack);
                let result = store.core.expect_digest(car.val().get_atom_idx().unwrap());
                println!("Result: {result} ({elapsed}μs)");

                Calculator::pad_frames(&mut frames, &store);
                store.core.hydrate_z_cache();

                let now = Instant::now();
                let trace = Calculator::compute_trace(&frames, &store);
                let elapsed = now.elapsed().as_micros();
                println!("Trace computed ({elapsed}μs)");

                let public_values = store.to_scalar_vector(&[entry, nil, nil, resulting_stack]);
                let config = BabyBearPoseidon2::new();
                let calculator = Calculator::default();

                let challenger = &mut config.challenger();
                let now = Instant::now();
                let proof = prove(&config, &calculator, challenger, trace, &public_values);
                let elapsed = now.elapsed().as_millis();
                println!("Proof generated ({elapsed}ms)");

                let challenger = &mut config.challenger();
                let now = Instant::now();
                verify(&config, &calculator, challenger, &proof, &public_values).unwrap();
                let elapsed = now.elapsed().as_millis();
                println!("Proof verified ({elapsed}ms)");
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                println!("Exiting...");
                break;
            }
            Err(e) => {
                eprintln!("Read line error: {e}");
                break;
            }
        }
    }
    Ok(())
}
