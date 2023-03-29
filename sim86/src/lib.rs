use std::io::{Read, Write};

pub mod execute;
pub mod model;
pub mod parse;

pub fn disassemble<R: Read, W: Write>(input: R, output: &mut W) {
    let mut input = input.bytes();

    loop {
        let b1: u8 = match input.next() {
            Some(Ok(b)) => b,
            Some(Err(e)) => panic!("Failed to get next byte due to IO error - {}", e),
            None => return,
        };
        let instruction =
            parse::parse_complete_instruction(b1, &mut input, parse::parse_instruction);
        writeln!(output, "{}", instruction).unwrap();
    }
}

pub fn disassemble_via_jump_table<R: Read, W: Write>(input: R, output: &mut W) {
    let jump_table: [parse::ParseFunc<R>; 256] = parse::construct_jump_table::<R>();

    let mut input = input.bytes();

    loop {
        let b1: u8 = match input.next() {
            Some(Ok(b)) => b,
            Some(Err(e)) => panic!("Failed to get next byte due to IO error - {}", e),
            None => return,
        };
        let instruction = parse::parse_complete_instruction(b1, &mut input, |b1, input| {
            let parse_function: parse::ParseFunc<R> = jump_table[b1 as usize];
            parse_function(b1, input)
        });
        writeln!(output, "{}", instruction).unwrap();
    }
}

pub fn execute_with_trace<R: Read, W: Write>(input: R, output: &mut W) -> execute::MachineState {
    let mut machine_state = execute::MachineState::default();
    let mut input = input.bytes();
    loop {
        let b1: u8 = match input.next() {
            Some(Ok(b)) => b,
            Some(Err(e)) => panic!("Failed to get next byte due to IO error - {}", e),
            None => break,
        };
        let instruction =
            parse::parse_complete_instruction(b1, &mut input, parse::parse_instruction);

        write!(output, "{}", instruction).unwrap();

        let prev_machine_state = machine_state.clone();
        machine_state.execute_instruction(instruction);

        execute::MachineStateDiff::diff(&prev_machine_state, &machine_state, |diff| {
            write!(output, " ; {}", diff).unwrap();
        });

        writeln!(output).unwrap();
    }

    machine_state
}
