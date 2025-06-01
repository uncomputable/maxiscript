#![no_main]

use libfuzzer_sys::fuzz_target;
use maxiscript::parse_program_string;

// TODO: Use arbitrary
fuzz_target!(|src: &str| {
    let program_string_pass1 = match parse_program_string(src) {
        Some(x) => x,
        None => return,
    };
    let program_string_pass2 = match parse_program_string(&program_string_pass1) {
        Some(x) => x,
        None => return,
    };
    assert_eq!(program_string_pass1, program_string_pass2);
});
