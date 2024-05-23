mod calculator;
mod dummy_hasher;
mod pointers;
mod store;

use loam::air::debug::debug_constraints_collecting_interactions;
use p3_baby_bear::BabyBear;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::time::Instant;

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

                let now = Instant::now();
                let public_values = store.to_scalar_vector(&[entry, nil, nil, resulting_stack]);
                let _ = debug_constraints_collecting_interactions(
                    &Calculator::default(),
                    &public_values,
                    &trace,
                );
                let elapsed = now.elapsed().as_millis();
                println!("Verify constraints ({elapsed}ms)");
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
