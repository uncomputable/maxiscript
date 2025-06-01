#![no_main]

use libfuzzer_sys::fuzz_target;
use maxiscript::stack::{find_shortest_transformation, StackOp};

fuzz_target!(|input: (&[u8], &[u8])| {
    let (source_stack, target) = input;

    // Bail out to prevent exponential time and memory use.
    if 5 < target.len() {
        return;
    }
    // Target contains item that is not contained in source stack.
    // There is no transformation from source to target, so bail out early.
    if target.iter().any(|x| !source_stack.contains(x)) {
        return;
    }

    let state = find_shortest_transformation(source_stack, target)
        .expect("there should be a transformation");
    let script = state.reversed_script.into_iter().rev();
    let mut stack = Vec::from(source_stack);
    StackOp::apply(&mut stack, script).expect("transformation script should not fail");
    assert!(
        state.script_bytes <= target.len() * 2,
        "maximum transformation cost should be 2 * N for N target items"
    );
    assert!(
        target.len() <= stack.len(),
        "result stack should be long enough to include target"
    );
    assert_eq!(
        &stack[stack.len() - target.len()..],
        target,
        "result stack top should be equal to target"
    );
});
