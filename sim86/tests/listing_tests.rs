use std::{
    io::{Cursor, Write},
    process::{Command, Stdio},
};

use console::Style;
use similar::{ChangeTag, TextDiff};

use sim86::{
    disassemble, disassemble_via_jump_table, execute_with_trace,
    model::{Reg, SegmentReg, WordReg},
};

// NOTE(photobaric): In order to run most of these tests, nasm and xxd must be installed

fn normalize_asm(asm: &str) -> String {
    asm.split('\n')
        .filter(|line| !line.starts_with(';'))
        .filter(|line| !line.chars().all(|c| c.is_whitespace()))
        .collect::<Vec<&str>>()
        .join("\n")
}

fn normalize_trace(asm: &str) -> String {
    asm.split('\n')
        .filter(|line| !line.starts_with(';'))
        .map(|line| line.trim())
        .filter(|line| !line.is_empty())
        .collect::<Vec<&str>>()
        .join("\n")
}

fn print_diff(s1: &str, s2: &str) {
    let diff = TextDiff::from_lines(s1.trim(), s2.trim());
    let mut stdout = ::std::io::stdout().lock();
    for change in diff.iter_all_changes() {
        let (sign, style) = match change.tag() {
            ChangeTag::Delete => ("-", Style::new().red()),
            ChangeTag::Insert => ("+", Style::new().green()),
            ChangeTag::Equal => (" ", Style::new()),
        };
        write!(
            stdout,
            "{}{}",
            style.apply_to(sign).bold(),
            style.apply_to(change)
        )
        .unwrap();
    }
    stdout.flush().unwrap();
    drop(stdout);
}

fn test_disassembly(binary: &[u8], expected_asm: &str) {
    fn verify(output_vec: Vec<u8>, expected_asm: &str) {
        let output_asm: String = String::from_utf8(output_vec).unwrap();
        let output_asm_normalized: String = normalize_asm(&output_asm);
        let expected_asm_normalized: String = normalize_asm(expected_asm);
        if output_asm_normalized != expected_asm_normalized {
            print_diff(&expected_asm_normalized, &output_asm_normalized);
            panic!();
        }
    }

    {
        let mut write: Cursor<Vec<u8>> = Cursor::new(Vec::new());
        write.write_all(b"bits 16\n\n").unwrap();
        disassemble(binary, &mut write);
        let output_vec: Vec<u8> = write.into_inner();
        verify(output_vec, expected_asm);
    }

    {
        let mut write: Cursor<Vec<u8>> = Cursor::new(Vec::new());
        write.write_all(b"bits 16\n\n").unwrap();
        disassemble_via_jump_table(binary, &mut write);
        let output_vec: Vec<u8> = write.into_inner();
        verify(output_vec, expected_asm);
    }
}

fn nasm_assemble(asm: &str) -> Vec<u8> {
    struct Autodelete<'a>(&'a str);

    impl<'a> Drop for Autodelete<'a> {
        fn drop(&mut self) {
            let _ = ::std::fs::remove_file(self.0);
        }
    }

    // generate unique files to allow tests to run in parallel
    let filename = format!("/tmp/nasm-buffer-{}.asm", uuid::Uuid::new_v4());
    let _autodelete = Autodelete(&filename);
    ::std::fs::write(&filename, asm).unwrap();

    let child = Command::new("nasm")
        .arg(&filename)
        .arg("-o")
        .arg("/dev/stdout")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let output = child.wait_with_output().unwrap();
    if !output.status.success() {
        eprintln!("nasm failed with output: {:?}", output);
        eprintln!("asm:");
        eprintln!("{}", asm);
        panic!();
    }

    output.stdout
}

fn xxd_binary_dump(bytes: &[u8]) -> String {
    let mut child = Command::new("xxd")
        .arg("-b")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let child_stdin = child.stdin.as_mut().unwrap();
    child_stdin.write_all(bytes).unwrap();
    drop(child_stdin);

    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());

    String::from_utf8(output.stdout).unwrap()
}

fn test_reassembly(binary: &[u8], _expected_asm: &str) {
    {
        let mut write: Cursor<Vec<u8>> = Cursor::new(Vec::new());
        write.write_all(b"bits 16\n\n").unwrap();
        disassemble(binary, &mut write);
        let output_vec: Vec<u8> = write.into_inner();
        let output_string: String = String::from_utf8(output_vec).unwrap();
        let reassembled: Vec<u8> = nasm_assemble(&output_string);
        if binary != reassembled {
            let original_dump = xxd_binary_dump(binary);
            let reassembled_dump = xxd_binary_dump(&reassembled);
            print_diff(&original_dump, &reassembled_dump);
            panic!();
        }
    }

    {
        let mut write: Cursor<Vec<u8>> = Cursor::new(Vec::new());
        write.write_all(b"bits 16\n\n").unwrap();
        disassemble_via_jump_table(binary, &mut write);
        let output_vec: Vec<u8> = write.into_inner();
        let output_string: String = String::from_utf8(output_vec).unwrap();
        let reassembled: Vec<u8> = nasm_assemble(&output_string);
        if binary != reassembled {
            let original_dump = xxd_binary_dump(binary);
            let reassembled_dump = xxd_binary_dump(&reassembled);
            print_diff(&original_dump, &reassembled_dump);
            panic!();
        }
    }
}

fn test_execution(binary: &[u8], expected_trace: &str, header: &str, print_registers: &[Reg]) {
    let mut write: Cursor<Vec<u8>> = Cursor::new(Vec::new());

    writeln!(write, "{}", header).unwrap();

    let final_machine_state = execute_with_trace(binary, &mut write);

    writeln!(write).unwrap();
    writeln!(write, "Final registers:").unwrap();
    final_machine_state
        .print_registers("      ", print_registers, &mut write)
        .unwrap();

    let output_vec: Vec<u8> = write.into_inner();
    let output_trace: String = String::from_utf8(output_vec).unwrap();
    let output_trace_normalized: String = normalize_trace(&output_trace);
    let expected_trace_normalized: String = normalize_trace(expected_trace);
    if output_trace_normalized != expected_trace_normalized {
        print_diff(&expected_trace_normalized, &output_trace_normalized);
        panic!();
    }
}

#[test]
fn listing_0037_single_register_mov() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0037_single_register_mov");
    const ASM: &str = include_str!("./testdata/listing_0037_single_register_mov.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn listing_0038_many_register_mov() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0038_many_register_mov");
    const ASM: &str = include_str!("./testdata/listing_0038_many_register_mov.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn listing_0039_more_movs() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0039_more_movs");
    const ASM: &str = include_str!("./testdata/listing_0039_more_movs.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn listing_0040_challenge_movs() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0040_challenge_movs");
    const ASM: &str = include_str!("./testdata/listing_0040_challenge_movs.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn listing_0041_add_sub_cmp_jnz() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0041_add_sub_cmp_jnz");
    const ASM: &str = include_str!("./testdata/listing_0041_add_sub_cmp_jnz.asm");

    test_reassembly(BINARY, ASM);
}

#[test]
fn listing_0042_completionist_decode() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0042_completionist_decode");
    const ASM: &str = include_str!("./testdata/listing_0042_completionist_decode.asm");

    test_reassembly(BINARY, ASM);
}

const AX: Reg = Reg::WordReg(WordReg::AX);
const BX: Reg = Reg::WordReg(WordReg::BX);
const CX: Reg = Reg::WordReg(WordReg::CX);
const DX: Reg = Reg::WordReg(WordReg::DX);
const SP: Reg = Reg::WordReg(WordReg::SP);
const BP: Reg = Reg::WordReg(WordReg::BP);
const SI: Reg = Reg::WordReg(WordReg::SI);
const DI: Reg = Reg::WordReg(WordReg::DI);
const ES: Reg = Reg::SegmentReg(SegmentReg::ES);
const SS: Reg = Reg::SegmentReg(SegmentReg::SS);
const DS: Reg = Reg::SegmentReg(SegmentReg::DS);

#[test]
fn listing_0043_immediate_movs() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0043_immediate_movs");
    const ASM: &str = include_str!("./testdata/listing_0043_immediate_movs.asm");
    const TRACE: &str = include_str!("./testdata/listing_0043_immediate_movs.txt");

    test_reassembly(BINARY, ASM);
    test_execution(
        BINARY,
        TRACE,
        r"--- test\listing_0043_immediate_movs execution ---",
        &[AX, BX, CX, DX, SP, BP, SI, DI],
    );
}

#[test]
fn listing_0044_register_movs() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0044_register_movs");
    const ASM: &str = include_str!("./testdata/listing_0044_register_movs.asm");
    const TRACE: &str = include_str!("./testdata/listing_0044_register_movs.txt");

    test_reassembly(BINARY, ASM);
    test_execution(
        BINARY,
        TRACE,
        r"--- test\listing_0044_register_movs execution ---",
        &[AX, BX, CX, DX, SP, BP, SI, DI],
    );
}

#[test]
fn listing_0045_challenge_register_movs() {
    const BINARY: &[u8] = include_bytes!("./testdata/listing_0045_challenge_register_movs");
    const ASM: &str = include_str!("./testdata/listing_0045_challenge_register_movs.asm");
    const TRACE: &str = include_str!("./testdata/listing_0045_challenge_register_movs.txt");

    test_reassembly(BINARY, ASM);
    test_execution(
        BINARY,
        TRACE,
        r"--- test\listing_0045_challenge_register_movs execution ---",
        &[AX, BX, CX, DX, SP, BP, SI, DI, ES, SS, DS],
    );
}

#[test]
fn test_mov_acc_mem() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_mov_acc_mem");
    const ASM: &str = include_str!("./testdata/test_mov_acc_mem.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn test_mov_sr() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_mov_sr");
    const ASM: &str = include_str!("./testdata/test_mov_sr.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn test_0041_no_jumps() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_0041_no_jumps");
    const ASM: &str = include_str!("./testdata/test_0041_no_jumps.asm");

    test_reassembly(BINARY, ASM);
}

#[test]
fn test_jumps() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_jumps");
    const ASM: &str = include_str!("./testdata/test_jumps.asm");

    test_reassembly(BINARY, ASM);
}

#[test]
fn test_test_instruction() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_test_instruction");
    const ASM: &str = include_str!("./testdata/test_test_instruction.asm");

    test_reassembly(BINARY, ASM);
}

#[test]
fn test_jmp_call_direct_relative() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_jmp_call_direct_relative");
    const ASM: &str = include_str!("./testdata/test_jmp_call_direct_relative.asm");

    test_disassembly(BINARY, ASM);
    test_reassembly(BINARY, ASM);
}

#[test]
fn test_jmp_call_direct_absolute() {
    const BINARY: &[u8] = include_bytes!("./testdata/test_jmp_call_direct_absolute");
    const ASM: &str = include_str!("./testdata/test_jmp_call_direct_absolute.asm");

    test_reassembly(BINARY, ASM);
}
