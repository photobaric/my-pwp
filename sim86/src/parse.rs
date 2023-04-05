#![allow(clippy::unusual_byte_groupings)]

use std::{
    io::{ErrorKind, Read},
    slice,
};

use crate::model::{
    BaseReg, ByteOrWord, ByteReg, IndexReg, Instruction, MemAddressingMode, MemOperand,
    PrefixState, PrefixedInstruction, RegMemOperand, RegOperand, SegmentReg, WordReg,
};

pub fn next_byte<R: Read>(input: &mut R) -> Option<Result<u8, ::std::io::Error>> {
    let mut byte: u8 = 0;
    loop {
        return match input.read(slice::from_mut(&mut byte)) {
            Ok(0) => None,
            Ok(..) => Some(Ok(byte)),
            Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
            Err(e) => Some(Err(e)),
        };
    }
}

macro_rules! next_byte_or_err {
    ($input:ident, $error:expr) => {
        match next_byte($input) {
            Some(Ok(b)) => b,
            Some(Err(e)) => return Err(e.into()),
            None => return Err($error.into()),
        }
    };
}

fn next_byte_or_panic<R: Read>(input: &mut R) -> u8 {
    let byte = next_byte(input);
    match byte {
        Some(Ok(b)) => b,
        Some(Err(e)) => panic!("Failed to get next byte due to IO error - {}", e),
        None => panic!("Failed to get next byte where required"),
    }
}

fn parse_general_purpose_reg(is_word: bool, reg: u8) -> RegOperand {
    if is_word {
        RegOperand::Reg16(reg.try_into().unwrap())
    } else {
        RegOperand::Reg8(reg.try_into().unwrap())
    }
}

fn parse_accumulator_reg(is_word: bool) -> RegOperand {
    if is_word {
        RegOperand::Reg16(WordReg::AX)
    } else {
        RegOperand::Reg8(ByteReg::AL)
    }
}

macro_rules! impl_display_via_debug {
    ($typ:ty) => {
        impl ::std::fmt::Display for $typ {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self)
            }
        }
    };
}

#[derive(::thiserror::Error, Debug)]
enum ParseModRMError {
    Io(#[from] ::std::io::Error),
    DirectAddressingMissingDispLoByte,
    DirectAddressingMissingDispHiByte,
    EightBitDisplacementMissingDispLoByte,
    SixteenBitDisplacementMissingDispLoByte,
    SixteenBitDisplacementMissingDispHiByte,
}
impl_display_via_debug!(ParseModRMError);

fn parse_modrm<R: Read>(
    is_word: bool,
    b2: u8,
    input: &mut R,
) -> Result<RegMemOperand, ParseModRMError> {
    let mode = b2 >> 6;
    let rm = b2 & 0b00000111;
    let modrm: RegMemOperand = match mode {
        0b00 => {
            let mem_addressing_mode = match rm {
                0b000 => MemAddressingMode::BasedIndexedAddressingNoDisp(BaseReg::BX, IndexReg::SI),
                0b001 => MemAddressingMode::BasedIndexedAddressingNoDisp(BaseReg::BX, IndexReg::DI),
                0b010 => MemAddressingMode::BasedIndexedAddressingNoDisp(BaseReg::BP, IndexReg::SI),
                0b011 => MemAddressingMode::BasedIndexedAddressingNoDisp(BaseReg::BP, IndexReg::DI),
                0b100 => MemAddressingMode::RegisterIndirectAddressingViaIndexReg(IndexReg::SI),
                0b101 => MemAddressingMode::RegisterIndirectAddressingViaIndexReg(IndexReg::DI),
                0b110 => {
                    // Direct addressing special case
                    let disp_lo = next_byte_or_err!(
                        input,
                        ParseModRMError::DirectAddressingMissingDispLoByte
                    );
                    let disp_hi = next_byte_or_err!(
                        input,
                        ParseModRMError::DirectAddressingMissingDispHiByte
                    );
                    let direct_address = (disp_hi as u16) << 8 | (disp_lo as u16);
                    MemAddressingMode::DirectAddressing(direct_address)
                }
                0b111 => MemAddressingMode::RegisterIndirectAddressingViaBaseReg(BaseReg::BX),
                _ => unreachable!(),
            };
            let mem_operand = if is_word {
                MemOperand::Mem16(mem_addressing_mode)
            } else {
                MemOperand::Mem8(mem_addressing_mode)
            };
            RegMemOperand::Mem(mem_operand)
        }
        0b01 => {
            let d8 = next_byte_or_err!(
                input,
                ParseModRMError::EightBitDisplacementMissingDispLoByte
            );
            let d16 = if d8 & 0b10000000 == 0 {
                d8 as u16
            } else {
                // This cast will sign-extend according to the Rust Reference:
                // https://doc.rust-lang.org/reference/expressions/operator-expr.html#numeric-cast
                //
                // Here is the generated machine code:
                // sub	rsp, 1
                // mov	al, dil
                // mov	byte ptr [rsp], al
                // movsx	eax, al
                // add	rsp, 1
                // ret
                d8 as i8 as u16
            };
            let mem_addressing_mode = match rm {
                0b000 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BX, IndexReg::SI, d16),
                0b001 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BX, IndexReg::DI, d16),
                0b010 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BP, IndexReg::SI, d16),
                0b011 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BP, IndexReg::DI, d16),
                0b100 => MemAddressingMode::IndexedAddressing(IndexReg::SI, d16),
                0b101 => MemAddressingMode::IndexedAddressing(IndexReg::DI, d16),
                0b110 => MemAddressingMode::BasedAddressing(BaseReg::BP, d16),
                0b111 => MemAddressingMode::BasedAddressing(BaseReg::BX, d16),
                _ => unreachable!(),
            };
            let mem_operand = if is_word {
                MemOperand::Mem16(mem_addressing_mode)
            } else {
                MemOperand::Mem8(mem_addressing_mode)
            };
            RegMemOperand::Mem(mem_operand)
        }
        0b10 => {
            let disp_lo = next_byte_or_err!(
                input,
                ParseModRMError::SixteenBitDisplacementMissingDispLoByte
            );
            let disp_hi = next_byte_or_err!(
                input,
                ParseModRMError::SixteenBitDisplacementMissingDispHiByte
            );
            let d16 = (disp_hi as u16) << 8 | (disp_lo as u16);
            let mem_addressing_mode = match rm {
                0b000 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BX, IndexReg::SI, d16),
                0b001 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BX, IndexReg::DI, d16),
                0b010 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BP, IndexReg::SI, d16),
                0b011 => MemAddressingMode::BasedIndexedAddressing(BaseReg::BP, IndexReg::DI, d16),
                0b100 => MemAddressingMode::IndexedAddressing(IndexReg::SI, d16),
                0b101 => MemAddressingMode::IndexedAddressing(IndexReg::DI, d16),
                0b110 => MemAddressingMode::BasedAddressing(BaseReg::BP, d16),
                0b111 => MemAddressingMode::BasedAddressing(BaseReg::BX, d16),
                _ => unreachable!(),
            };
            let mem_operand = if is_word {
                MemOperand::Mem16(mem_addressing_mode)
            } else {
                MemOperand::Mem8(mem_addressing_mode)
            };
            RegMemOperand::Mem(mem_operand)
        }
        0b11 => {
            let reg_operand = parse_general_purpose_reg(is_word, rm);
            RegMemOperand::Reg(reg_operand)
        }
        _ => unreachable!(),
    };
    Ok(modrm)
}

#[derive(::thiserror::Error, Debug)]
enum ParseImmediateError {
    Io(#[from] ::std::io::Error),
    MissingDataLo,
    MissingDataHi,
}
impl_display_via_debug!(ParseImmediateError);

fn parse_immediate<R: Read>(
    is_word: bool,
    input: &mut R,
) -> Result<ByteOrWord, ParseImmediateError> {
    if is_word {
        parse_immediate_word(input).map(ByteOrWord::Word)
    } else {
        parse_immediate_byte(input).map(ByteOrWord::Byte)
    }
}

fn parse_immediate_byte<R: Read>(input: &mut R) -> Result<u8, ParseImmediateError> {
    let data_lo = next_byte_or_err!(input, ParseImmediateError::MissingDataLo);
    Ok(data_lo)
}

fn parse_immediate_word<R: Read>(input: &mut R) -> Result<u16, ParseImmediateError> {
    let data_lo = next_byte_or_err!(input, ParseImmediateError::MissingDataLo);
    let data_hi = next_byte_or_err!(input, ParseImmediateError::MissingDataHi);
    let data = (data_hi as u16) << 8 | (data_lo as u16);
    Ok(data)
}

fn fail_unimplemented<R: Read>(b1: u8, _: &mut R) -> Instruction {
    panic!("Unknown instruction - first byte {:#010b}", b1)
}

fn fail_unused<R: Read>(b1: u8, _: &mut R) -> Instruction {
    panic!("Invalid instruction - first byte {:#010b}", b1)
}

fn parse_0b100010xx_mov_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // MOV - Register/memory to/from register

    // semantics of D bit:
    // 1 = the REG field identifies the destination operand
    // 0 = the REG field identifies the source operand
    let is_reg_dst = b1 & 0b10 != 0;

    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::MovRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b1100011x_mov_immediate_to_rm<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // MOV - Immediate to register/memory

    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let rm = parse_modrm(is_word, b2, input).unwrap();
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::MovImmediateToRm { rm, immediate }
}

fn parse_0b1011xxxx_mov_immediate_to_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // MOV - Immediate to register

    let is_word = b1 & 0b1000 != 0;
    let reg = b1 & 0b111;

    let rm = RegMemOperand::Reg(parse_general_purpose_reg(is_word, reg));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::MovImmediateToRm { rm, immediate }
}

fn parse_0b101000xx_mov_mem_to_from_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // MOV - Memory to/from accumulator

    let is_reg_dst = b1 & 0b10 == 0;
    let is_word = b1 & 0b01 != 0;

    let reg = parse_accumulator_reg(is_word);
    let rm = {
        let addr_lo = next_byte_or_panic(input);
        let addr_hi = next_byte_or_panic(input);
        let direct_address = (addr_hi as u16) << 8 | (addr_lo as u16);
        let mem_addressing_mode = MemAddressingMode::DirectAddressing(direct_address);
        let mem_operand = if is_word {
            MemOperand::Mem16(mem_addressing_mode)
        } else {
            MemOperand::Mem8(mem_addressing_mode)
        };
        RegMemOperand::Mem(mem_operand)
    };

    Instruction::MovRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b100011x0_mov_rm_to_from_segment_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // MOV - Register/memory to/from segment register

    let is_segment_reg_dst = b1 & 0b10 != 0;

    let b2 = next_byte_or_panic(input);

    let sr = (b2 & 0b11000) >> 3;

    let segment_reg = SegmentReg::try_from(sr).unwrap();
    let rm = parse_modrm(true, b2, input).unwrap();

    Instruction::MovRmToFromSegmentReg {
        is_segment_reg_dst,
        segment_reg,
        rm,
    }
}

fn parse_0b000000xx_add_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // ADD - Register/memory to/from register

    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::AddRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b0000010x_add_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // ADD - Immediate to accumulator

    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::AddImmediateToRm { rm, immediate }
}

fn parse_0b000100xx_adc_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::AdcRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b0001010x_adc_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::AdcImmediateToRm { rm, immediate }
}

fn parse_0b01000xxx_inc_word_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let word_reg = WordReg::try_from(b1 & 0b111).unwrap();
    Instruction::Inc {
        rm: RegMemOperand::Reg(RegOperand::Reg16(word_reg)),
    }
}

fn parse_0b00110111_aaa<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Aaa
}

fn parse_0b00100111_daa<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Daa
}

fn parse_0b001010xx_sub_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // SUB - Register/memory to/from register

    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::SubRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b0010110x_sub_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // SUB - Immediate to accumulator

    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::SubImmediateToRm { rm, immediate }
}

fn parse_0b000110xx_sbb_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::SbbRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b0001110x_sbb_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::SbbImmediateToRm { rm, immediate }
}

fn parse_0b01001xxx_dec_word_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let word_reg = WordReg::try_from(b1 & 0b111).unwrap();
    Instruction::Dec {
        rm: RegMemOperand::Reg(RegOperand::Reg16(word_reg)),
    }
}

fn parse_0b001110xx_cmp_rm_to_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // SUB - Register/memory to/from register

    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::CmpRmToReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b0011110x_cmp_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    // SUB - Immediate to accumulator

    let is_word = b1 & 0b01 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::CmpImmediateToRm { rm, immediate }
}

fn parse_0b100000xx_combine_immediate_to_rm<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let b2 = next_byte_or_panic(input);

    let rm = parse_modrm(is_word, b2, input).unwrap();
    let immediate = {
        let sw = b1 & 0b11;
        match sw {
            0b00 => ByteOrWord::Byte(parse_immediate_byte(input).unwrap()),
            0b01 => ByteOrWord::Word(parse_immediate_word(input).unwrap()),
            0b10 => panic!("unused"), // Sign extension doesn't make sense for immediate byte operand, see Page 4-31.
            0b11 => {
                let b: u8 = parse_immediate_byte(input).unwrap();
                ByteOrWord::Word(b as i8 as u16)
            }
            _ => unreachable!(),
        }
    };

    let op = (0b00111000 & b2) >> 3;
    match op {
        0b000 => Instruction::AddImmediateToRm { rm, immediate },
        0b001 => Instruction::OrImmediateToRm { rm, immediate },
        0b010 => Instruction::AdcImmediateToRm { rm, immediate },
        0b011 => Instruction::SbbImmediateToRm { rm, immediate },
        0b100 => Instruction::AndImmediateToRm { rm, immediate },
        0b101 => Instruction::SubImmediateToRm { rm, immediate },
        0b110 => Instruction::XorImmediateToRm { rm, immediate },
        0b111 => Instruction::CmpImmediateToRm { rm, immediate },
        _ => unreachable!(),
    }
}

fn parse_0b00111111_aas<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Aas
}

fn parse_0b00101111_das<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Das
}

fn parse_0b1111011x_test_not_neg_mul_imul_div_idiv<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    let b2 = next_byte_or_panic(input);
    let rm = parse_modrm(is_word, b2, input).unwrap();
    match (b2 >> 3) & 0b111 {
        0b000 => {
            let immediate = parse_immediate(is_word, input).unwrap();
            Instruction::TestImmediateToRm { rm, immediate }
        }
        0b001 => panic!("unused"),
        0b010 => Instruction::Not { rm },
        0b011 => Instruction::Neg { rm },
        0b100 => Instruction::Mul { rm },
        0b101 => Instruction::Imul { rm },
        0b110 => Instruction::Div { rm },
        0b111 => Instruction::Idiv { rm },
        _ => unreachable!(),
    }
}

fn parse_0b11010100_aam<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let b2 = next_byte_or_panic(input);
    assert_eq!(b2, 0b00001010);
    Instruction::Aam
}

fn parse_0b11010101_aad<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let b2 = next_byte_or_panic(input);
    assert_eq!(b2, 0b00001010);
    Instruction::Aad
}

fn parse_0b10011000_cbw<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Cbw
}

fn parse_0b10011001_cwd<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Cwd
}

fn parse_0b110100xx_shift<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let count = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;
    let b2 = next_byte_or_panic(input);
    let rm = parse_modrm(is_word, b2, input).unwrap();
    match (b2 >> 3) & 0b111 {
        0b000 => Instruction::Rol { count, rm },
        0b001 => Instruction::Ror { count, rm },
        0b010 => Instruction::Rcl { count, rm },
        0b011 => Instruction::Rcr { count, rm },
        0b100 => Instruction::ShlSal { count, rm },
        0b101 => Instruction::Shr { count, rm },
        0b110 => panic!("unused"),
        0b111 => Instruction::Sar { count, rm },
        _ => unreachable!(),
    }
}

fn parse_0b001000xx_and_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::AndRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

// NOTE(photobaric): This opcode is based off Page 4-31, the opcode on Page 4-25 is wrong (that codes for ADC)
//  Also note that there is no direction bit as Page 4-25 implies.
//  This makes sense since the test instruction is commutative.
fn parse_0b1000010x_test_rm_with_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::TestRmWithReg { reg, rm }
}

fn parse_0b000010xx_or_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::OrRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b001100xx_xor_rm_to_from_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_reg_dst = b1 & 0b10 != 0;
    let is_word = b1 & 0b01 != 0;

    let b2 = next_byte_or_panic(input);

    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();

    Instruction::XorRmToFromReg {
        is_reg_dst,
        reg,
        rm,
    }
}

fn parse_0b0010010x_and_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::AndImmediateToRm { rm, immediate }
}

fn parse_0b1010100x_test_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::TestImmediateToRm { rm, immediate }
}

fn parse_0b0000110x_or_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::OrImmediateToRm { rm, immediate }
}

fn parse_0b0011010x_xor_immediate_to_acc_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;

    let rm = RegMemOperand::Reg(parse_accumulator_reg(is_word));
    let immediate = parse_immediate(is_word, input).unwrap();

    Instruction::XorImmediateToRm { rm, immediate }
}

fn parse_0b1010010x_movs<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::Movs { is_word }
}

fn parse_0b1010011x_cmps<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::Cmps { is_word }
}

fn parse_0b1010111x_scas<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::Scas { is_word }
}

fn parse_0b1010110x_lods<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::Lods { is_word }
}

fn parse_0b1010101x_stos<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::Stos { is_word }
}

fn parse_0b11101000_call_direct<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc16 = parse_immediate_word(input).unwrap() as i16;
    Instruction::CallDirect { ip_inc16 }
}

fn parse_0b10011010_call_direct_intersegment<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip = parse_immediate_word(input).unwrap();
    let cs = parse_immediate_word(input).unwrap();
    Instruction::CallDirectIntersegment { ip, cs }
}

fn parse_0b11101001_jmp_direct<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc16 = parse_immediate_word(input).unwrap() as i16;
    Instruction::JmpDirect { ip_inc16 }
}

fn parse_0b11101011_jmp_direct_short<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8 = parse_immediate_byte(input).unwrap() as i8;
    Instruction::JmpDirectShort { ip_inc8 }
}

fn parse_0b11101010_jmp_direct_intersegment<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip = parse_immediate_word(input).unwrap();
    let cs = parse_immediate_word(input).unwrap();
    Instruction::JmpDirectIntersegment { ip, cs }
}

fn parse_0b11000011_ret<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Ret { sp_add: 0 }
}

fn parse_0b11000010_ret_sp_add<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let sp_add = parse_immediate_word(input).unwrap();
    Instruction::Ret { sp_add }
}

fn parse_0b11001011_ret_intersegment<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::RetIntersegment { sp_add: 0 }
}

fn parse_0b11001010_ret_intersegment_sp_add<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let sp_add = parse_immediate_word(input).unwrap();
    Instruction::RetIntersegment { sp_add }
}

fn parse_0b01110000_jo<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::Jo { ip_inc8 }
}

fn parse_0b01110001_jno<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::Jno { ip_inc8 }
}

fn parse_0b01110010_jb_jnae_jc<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JbJnaeJc { ip_inc8 }
}

fn parse_0b01110011_jnb_jae_jnc<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JnbJaeJnc { ip_inc8 }
}

fn parse_0b01110100_je_jz<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JeJz { ip_inc8 }
}

fn parse_0b01110101_jne_jnz<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JneJnz { ip_inc8 }
}

fn parse_0b01110110_jbe_jna<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JbeJna { ip_inc8 }
}

fn parse_0b01110111_jnbe_ja<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JnbeJa { ip_inc8 }
}

fn parse_0b01111000_js<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::Js { ip_inc8 }
}

fn parse_0b01111001_jns<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::Jns { ip_inc8 }
}

fn parse_0b01111010_jp_jpe<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JpJpe { ip_inc8 }
}

fn parse_0b01111011_jnp_jpo<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JnpJpo { ip_inc8 }
}

fn parse_0b01111100_jl_jnge<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JlJnge { ip_inc8 }
}

fn parse_0b01111101_jnl_jge<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JnlJge { ip_inc8 }
}

fn parse_0b01111110_jle_jng<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JleJng { ip_inc8 }
}

fn parse_0b01111111_jnle_jg<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::JnleJg { ip_inc8 }
}

fn parse_0b11100000_loopne_loopnz<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::LoopneLoopnz { ip_inc8 }
}

fn parse_0b11100001_loope_loopz<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::LoopeLoopz { ip_inc8 }
}

fn parse_0b11100010_loop<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::Loop { ip_inc8 }
}

fn parse_0b11100011_jcxz<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let ip_inc8: i8 = next_byte_or_panic(input) as i8;
    Instruction::Jcxz { ip_inc8 }
}

fn parse_0b11001101_int<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let interrupt_type = parse_immediate_byte(input).unwrap();
    Instruction::Int { interrupt_type }
}

fn parse_0b11001100_int3<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Int3
}

fn parse_0b11001110_into<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Into
}

fn parse_0b11001111_iret<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Iret
}

fn parse_0b11111000_clc<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Clc
}

fn parse_0b11110101_cmc<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Cmc
}

fn parse_0b11111001_stc<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Stc
}

fn parse_0b11111100_cld<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Cld
}

fn parse_0b11111101_std<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Std
}

fn parse_0b11111010_cli<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Cli
}

fn parse_0b11111011_sti<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Sti
}

fn parse_0b11110100_hlt<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Hlt
}

fn parse_0b10011011_wait<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Wait
}

fn parse_0b11011xxx_esc<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let xxx = b1 & 0b111;
    let b2 = next_byte_or_panic(input);
    let yyy = b2 & 0b111_000;
    let external_opcode = yyy | xxx;
    let rm = parse_modrm(true, b2, input).unwrap();
    Instruction::Esc {
        external_opcode,
        rm,
    }
}

fn parse_0b01010xxx_push_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let word_reg = WordReg::try_from(b1 & 0b111).unwrap();
    Instruction::Push {
        rm: RegMemOperand::Reg(RegOperand::Reg16(word_reg)),
    }
}

fn parse_0b000xx110_push_segment_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let segment_reg = SegmentReg::try_from((b1 & 0b11000) >> 3).unwrap();
    Instruction::PushSegmentReg { segment_reg }
}

fn parse_0b10001111_pop_rm<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let b2 = next_byte_or_panic(input);
    let rm = parse_modrm(true, b2, input).unwrap();
    Instruction::Pop { rm }
}

fn parse_0b01011xxx_pop_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let word_reg = WordReg::try_from(b1 & 0b111).unwrap();
    Instruction::Pop {
        rm: RegMemOperand::Reg(RegOperand::Reg16(word_reg)),
    }
}

fn parse_0b000xx111_pop_segment_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let segment_reg = SegmentReg::try_from((b1 & 0b11000) >> 3).unwrap();
    Instruction::PopSegmentReg { segment_reg }
}

fn parse_0b1000011x_xchg_rm_to_reg<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    let b2 = next_byte_or_panic(input);
    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(is_word, reg);
    let rm = parse_modrm(is_word, b2, input).unwrap();
    Instruction::Xchg { reg, rm }
}

fn parse_0b10010xxx_xchg_reg_to_acc_reg<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let word_reg = WordReg::try_from(b1 & 0b111).unwrap();
    Instruction::Xchg {
        reg: RegOperand::Reg16(WordReg::AX),
        rm: RegMemOperand::Reg(RegOperand::Reg16(word_reg)),
    }
}

fn parse_0b1110010x_in_fixed<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    let port = parse_immediate_byte(input).unwrap();
    Instruction::InFixed { is_word, port }
}

fn parse_0b1110110x_in_variable<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::InVariable { is_word }
}

fn parse_0b1110011x_out_fixed<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    let port = parse_immediate_byte(input).unwrap();
    Instruction::OutFixed { is_word, port }
}

fn parse_0b1110111x_out_variable<R: Read>(b1: u8, _input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    Instruction::OutVariable { is_word }
}

fn parse_0b11010111_xlat<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Xlat
}

fn parse_0b10001101_lea<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let b2 = next_byte_or_panic(input);
    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(true, reg);
    let rm = parse_modrm(true, b2, input).unwrap();
    Instruction::Lea { reg, rm }
}

fn parse_0b11000101_lds<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let b2 = next_byte_or_panic(input);
    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(true, reg);
    let rm = parse_modrm(true, b2, input).unwrap();
    Instruction::Lds { reg, rm }
}

fn parse_0b11000100_les<R: Read>(_b1: u8, input: &mut R) -> Instruction {
    let b2 = next_byte_or_panic(input);
    let reg = (b2 & 0b00111000) >> 3;
    let reg = parse_general_purpose_reg(true, reg);
    let rm = parse_modrm(true, b2, input).unwrap();
    Instruction::Les { reg, rm }
}

fn parse_0b10011111_lahf<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Lahf
}

fn parse_0b10011110_sahf<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Sahf
}

fn parse_0b10011100_pushf<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Pushf
}

fn parse_0b10011101_popf<R: Read>(_b1: u8, _input: &mut R) -> Instruction {
    Instruction::Popf
}

fn parse_0b1111111x_inc_dec_call_jmp_push_rm<R: Read>(b1: u8, input: &mut R) -> Instruction {
    let is_word = b1 & 1 != 0;
    let b2 = next_byte_or_panic(input);
    let rm = parse_modrm(is_word, b2, input).unwrap();
    match (b2 >> 3) & 0b111 {
        0b000 => Instruction::Inc { rm },
        0b001 => Instruction::Dec { rm },
        0b010 => Instruction::CallIndirect { rm },
        0b011 => Instruction::CallIndirectIntersegment { rm },
        0b100 => Instruction::JmpIndirect { rm },
        0b101 => Instruction::JmpIndirectIntersegment { rm },
        0b110 => Instruction::Push { rm },
        0b111 => panic!("unused"),
        _ => unreachable!(),
    }
}

fn fail_0b11110000_lock_prefix<R: Read>(b1: u8, _: &mut R) -> Instruction {
    panic!(
        "Expecting instruction but found lock prefix - first byte {:#010b}",
        b1
    )
}

fn fail_0b1111001x_rep_prefix<R: Read>(b1: u8, _: &mut R) -> Instruction {
    panic!(
        "Expecting instruction but encountered rep prefix - first byte {:#010b}",
        b1
    )
}

fn fail_0b001xx110_segment_override_prefix<R: Read>(b1: u8, _: &mut R) -> Instruction {
    panic!(
        "Expecting instruction but encountered segment override prefix - first byte {:#010b}",
        b1
    )
}

macro_rules! generate_jump_tables {
    ($($bits:literal => $parse_func:ident),+ $(,)?) => {
        pub fn parse_instruction<R: Read>(b1: u8, input: &mut R) -> Instruction {
            match b1 {
                $($bits => $parse_func(b1, input)),*
            }
        }

        pub type ParseFunc<R> = fn(u8, &mut R) -> Instruction;

        pub fn construct_jump_table<R: Read>() -> [ParseFunc<R>; 256] {
            let mut t: [ParseFunc<R>; 256] = [fail_unimplemented; 256];

            $(
                t[$bits] = $parse_func::<R>;
            )*

            t
        }
    }
}

generate_jump_tables! {
    0b00000000 => parse_0b000000xx_add_rm_to_from_reg,
    0b00000001 => parse_0b000000xx_add_rm_to_from_reg,
    0b00000010 => parse_0b000000xx_add_rm_to_from_reg,
    0b00000011 => parse_0b000000xx_add_rm_to_from_reg,
    0b00000100 => parse_0b0000010x_add_immediate_to_acc_reg,
    0b00000101 => parse_0b0000010x_add_immediate_to_acc_reg,
    0b00000110 => parse_0b000xx110_push_segment_reg,
    0b00000111 => parse_0b000xx111_pop_segment_reg,
    0b00001000 => parse_0b000010xx_or_rm_to_from_reg,
    0b00001001 => parse_0b000010xx_or_rm_to_from_reg,
    0b00001010 => parse_0b000010xx_or_rm_to_from_reg,
    0b00001011 => parse_0b000010xx_or_rm_to_from_reg,
    0b00001100 => parse_0b0000110x_or_immediate_to_acc_reg,
    0b00001101 => parse_0b0000110x_or_immediate_to_acc_reg,
    0b00001110 => parse_0b000xx110_push_segment_reg,
    0b00001111 => fail_unused, // This would encode `pop cs`, but the manual says it's unused.
    0b00010000 => parse_0b000100xx_adc_rm_to_from_reg,
    0b00010001 => parse_0b000100xx_adc_rm_to_from_reg,
    0b00010010 => parse_0b000100xx_adc_rm_to_from_reg,
    0b00010011 => parse_0b000100xx_adc_rm_to_from_reg,
    0b00010100 => parse_0b0001010x_adc_immediate_to_acc_reg,
    0b00010101 => parse_0b0001010x_adc_immediate_to_acc_reg,
    0b00010110 => parse_0b000xx110_push_segment_reg,
    0b00010111 => parse_0b000xx111_pop_segment_reg,
    0b00011000 => parse_0b000110xx_sbb_rm_to_from_reg,
    0b00011001 => parse_0b000110xx_sbb_rm_to_from_reg,
    0b00011010 => parse_0b000110xx_sbb_rm_to_from_reg,
    0b00011011 => parse_0b000110xx_sbb_rm_to_from_reg,
    0b00011100 => parse_0b0001110x_sbb_immediate_to_acc_reg,
    0b00011101 => parse_0b0001110x_sbb_immediate_to_acc_reg,
    0b00011110 => parse_0b000xx110_push_segment_reg,
    0b00011111 => parse_0b000xx111_pop_segment_reg,
    0b00100000 => parse_0b001000xx_and_rm_to_from_reg,
    0b00100001 => parse_0b001000xx_and_rm_to_from_reg,
    0b00100010 => parse_0b001000xx_and_rm_to_from_reg,
    0b00100011 => parse_0b001000xx_and_rm_to_from_reg,
    0b00100100 => parse_0b0010010x_and_immediate_to_acc_reg,
    0b00100101 => parse_0b0010010x_and_immediate_to_acc_reg,
    0b00100110 => fail_0b001xx110_segment_override_prefix,
    0b00100111 => parse_0b00100111_daa,
    0b00101000 => parse_0b001010xx_sub_rm_to_from_reg,
    0b00101001 => parse_0b001010xx_sub_rm_to_from_reg,
    0b00101010 => parse_0b001010xx_sub_rm_to_from_reg,
    0b00101011 => parse_0b001010xx_sub_rm_to_from_reg,
    0b00101100 => parse_0b0010110x_sub_immediate_to_acc_reg,
    0b00101101 => parse_0b0010110x_sub_immediate_to_acc_reg,
    0b00101110 => fail_0b001xx110_segment_override_prefix,
    0b00101111 => parse_0b00101111_das,
    0b00110000 => parse_0b001100xx_xor_rm_to_from_reg,
    0b00110001 => parse_0b001100xx_xor_rm_to_from_reg,
    0b00110010 => parse_0b001100xx_xor_rm_to_from_reg,
    0b00110011 => parse_0b001100xx_xor_rm_to_from_reg,
    0b00110100 => parse_0b0011010x_xor_immediate_to_acc_reg,
    0b00110101 => parse_0b0011010x_xor_immediate_to_acc_reg,
    0b00110110 => fail_0b001xx110_segment_override_prefix,
    0b00110111 => parse_0b00110111_aaa,
    0b00111000 => parse_0b001110xx_cmp_rm_to_reg,
    0b00111001 => parse_0b001110xx_cmp_rm_to_reg,
    0b00111010 => parse_0b001110xx_cmp_rm_to_reg,
    0b00111011 => parse_0b001110xx_cmp_rm_to_reg,
    0b00111100 => parse_0b0011110x_cmp_immediate_to_acc_reg,
    0b00111101 => parse_0b0011110x_cmp_immediate_to_acc_reg,
    0b00111110 => fail_0b001xx110_segment_override_prefix,
    0b00111111 => parse_0b00111111_aas,
    0b01000000 => parse_0b01000xxx_inc_word_reg,
    0b01000001 => parse_0b01000xxx_inc_word_reg,
    0b01000010 => parse_0b01000xxx_inc_word_reg,
    0b01000011 => parse_0b01000xxx_inc_word_reg,
    0b01000100 => parse_0b01000xxx_inc_word_reg,
    0b01000101 => parse_0b01000xxx_inc_word_reg,
    0b01000110 => parse_0b01000xxx_inc_word_reg,
    0b01000111 => parse_0b01000xxx_inc_word_reg,
    0b01001000 => parse_0b01001xxx_dec_word_reg,
    0b01001001 => parse_0b01001xxx_dec_word_reg,
    0b01001010 => parse_0b01001xxx_dec_word_reg,
    0b01001011 => parse_0b01001xxx_dec_word_reg,
    0b01001100 => parse_0b01001xxx_dec_word_reg,
    0b01001101 => parse_0b01001xxx_dec_word_reg,
    0b01001110 => parse_0b01001xxx_dec_word_reg,
    0b01001111 => parse_0b01001xxx_dec_word_reg,
    0b01010000 => parse_0b01010xxx_push_reg,
    0b01010001 => parse_0b01010xxx_push_reg,
    0b01010010 => parse_0b01010xxx_push_reg,
    0b01010011 => parse_0b01010xxx_push_reg,
    0b01010100 => parse_0b01010xxx_push_reg,
    0b01010101 => parse_0b01010xxx_push_reg,
    0b01010110 => parse_0b01010xxx_push_reg,
    0b01010111 => parse_0b01010xxx_push_reg,
    0b01011000 => parse_0b01011xxx_pop_reg,
    0b01011001 => parse_0b01011xxx_pop_reg,
    0b01011010 => parse_0b01011xxx_pop_reg,
    0b01011011 => parse_0b01011xxx_pop_reg,
    0b01011100 => parse_0b01011xxx_pop_reg,
    0b01011101 => parse_0b01011xxx_pop_reg,
    0b01011110 => parse_0b01011xxx_pop_reg,
    0b01011111 => parse_0b01011xxx_pop_reg,
    0b01100000 => fail_unused,
    0b01100001 => fail_unused,
    0b01100010 => fail_unused,
    0b01100011 => fail_unused,
    0b01100100 => fail_unused,
    0b01100101 => fail_unused,
    0b01100110 => fail_unused,
    0b01100111 => fail_unused,
    0b01101000 => fail_unused,
    0b01101001 => fail_unused,
    0b01101010 => fail_unused,
    0b01101011 => fail_unused,
    0b01101100 => fail_unused,
    0b01101101 => fail_unused,
    0b01101110 => fail_unused,
    0b01101111 => fail_unused,
    0b01110000 => parse_0b01110000_jo,
    0b01110001 => parse_0b01110001_jno,
    0b01110010 => parse_0b01110010_jb_jnae_jc,
    0b01110011 => parse_0b01110011_jnb_jae_jnc,
    0b01110100 => parse_0b01110100_je_jz,
    0b01110101 => parse_0b01110101_jne_jnz,
    0b01110110 => parse_0b01110110_jbe_jna,
    0b01110111 => parse_0b01110111_jnbe_ja,
    0b01111000 => parse_0b01111000_js,
    0b01111001 => parse_0b01111001_jns,
    0b01111010 => parse_0b01111010_jp_jpe,
    0b01111011 => parse_0b01111011_jnp_jpo,
    0b01111100 => parse_0b01111100_jl_jnge,
    0b01111101 => parse_0b01111101_jnl_jge,
    0b01111110 => parse_0b01111110_jle_jng,
    0b01111111 => parse_0b01111111_jnle_jg,
    0b10000000 => parse_0b100000xx_combine_immediate_to_rm,
    0b10000001 => parse_0b100000xx_combine_immediate_to_rm,
    0b10000010 => parse_0b100000xx_combine_immediate_to_rm,
    0b10000011 => parse_0b100000xx_combine_immediate_to_rm,
    0b10000100 => parse_0b1000010x_test_rm_with_reg,
    0b10000101 => parse_0b1000010x_test_rm_with_reg,
    0b10000110 => parse_0b1000011x_xchg_rm_to_reg,
    0b10000111 => parse_0b1000011x_xchg_rm_to_reg,
    0b10001000 => parse_0b100010xx_mov_rm_to_from_reg,
    0b10001001 => parse_0b100010xx_mov_rm_to_from_reg,
    0b10001010 => parse_0b100010xx_mov_rm_to_from_reg,
    0b10001011 => parse_0b100010xx_mov_rm_to_from_reg,
    0b10001100 => parse_0b100011x0_mov_rm_to_from_segment_reg,
    0b10001101 => parse_0b10001101_lea,
    0b10001110 => parse_0b100011x0_mov_rm_to_from_segment_reg,
    0b10001111 => parse_0b10001111_pop_rm,
    0b10010000 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010001 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010010 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010011 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010100 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010101 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010110 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10010111 => parse_0b10010xxx_xchg_reg_to_acc_reg,
    0b10011000 => parse_0b10011000_cbw,
    0b10011001 => parse_0b10011001_cwd,
    0b10011010 => parse_0b10011010_call_direct_intersegment,
    0b10011011 => parse_0b10011011_wait,
    0b10011100 => parse_0b10011100_pushf,
    0b10011101 => parse_0b10011101_popf,
    0b10011110 => parse_0b10011110_sahf,
    0b10011111 => parse_0b10011111_lahf,
    0b10100000 => parse_0b101000xx_mov_mem_to_from_acc_reg,
    0b10100001 => parse_0b101000xx_mov_mem_to_from_acc_reg,
    0b10100010 => parse_0b101000xx_mov_mem_to_from_acc_reg,
    0b10100011 => parse_0b101000xx_mov_mem_to_from_acc_reg,
    0b10100100 => parse_0b1010010x_movs,
    0b10100101 => parse_0b1010010x_movs,
    0b10100110 => parse_0b1010011x_cmps,
    0b10100111 => parse_0b1010011x_cmps,
    0b10101000 => parse_0b1010100x_test_immediate_to_acc_reg,
    0b10101001 => parse_0b1010100x_test_immediate_to_acc_reg,
    0b10101010 => parse_0b1010101x_stos,
    0b10101011 => parse_0b1010101x_stos,
    0b10101100 => parse_0b1010110x_lods,
    0b10101101 => parse_0b1010110x_lods,
    0b10101110 => parse_0b1010111x_scas,
    0b10101111 => parse_0b1010111x_scas,
    0b10110000 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110001 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110010 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110011 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110100 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110101 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110110 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10110111 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111000 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111001 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111010 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111011 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111100 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111101 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111110 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b10111111 => parse_0b1011xxxx_mov_immediate_to_reg,
    0b11000000 => fail_unused,
    0b11000001 => fail_unused,
    0b11000010 => parse_0b11000010_ret_sp_add,
    0b11000011 => parse_0b11000011_ret,
    0b11000100 => parse_0b11000100_les,
    0b11000101 => parse_0b11000101_lds,
    0b11000110 => parse_0b1100011x_mov_immediate_to_rm,
    0b11000111 => parse_0b1100011x_mov_immediate_to_rm,
    0b11001000 => fail_unused,
    0b11001001 => fail_unused,
    0b11001010 => parse_0b11001010_ret_intersegment_sp_add,
    0b11001011 => parse_0b11001011_ret_intersegment,
    0b11001100 => parse_0b11001100_int3,
    0b11001101 => parse_0b11001101_int,
    0b11001110 => parse_0b11001110_into,
    0b11001111 => parse_0b11001111_iret,
    0b11010000 => parse_0b110100xx_shift,
    0b11010001 => parse_0b110100xx_shift,
    0b11010010 => parse_0b110100xx_shift,
    0b11010011 => parse_0b110100xx_shift,
    0b11010100 => parse_0b11010100_aam,
    0b11010101 => parse_0b11010101_aad,
    0b11010110 => fail_unused,
    0b11010111 => parse_0b11010111_xlat,
    0b11011000 => parse_0b11011xxx_esc,
    0b11011001 => parse_0b11011xxx_esc,
    0b11011010 => parse_0b11011xxx_esc,
    0b11011011 => parse_0b11011xxx_esc,
    0b11011100 => parse_0b11011xxx_esc,
    0b11011101 => parse_0b11011xxx_esc,
    0b11011110 => parse_0b11011xxx_esc,
    0b11011111 => parse_0b11011xxx_esc,
    0b11100000 => parse_0b11100000_loopne_loopnz,
    0b11100001 => parse_0b11100001_loope_loopz,
    0b11100010 => parse_0b11100010_loop,
    0b11100011 => parse_0b11100011_jcxz,
    0b11100100 => parse_0b1110010x_in_fixed,
    0b11100101 => parse_0b1110010x_in_fixed,
    0b11100110 => parse_0b1110011x_out_fixed,
    0b11100111 => parse_0b1110011x_out_fixed,
    0b11101000 => parse_0b11101000_call_direct,
    0b11101001 => parse_0b11101001_jmp_direct,
    0b11101010 => parse_0b11101010_jmp_direct_intersegment,
    0b11101011 => parse_0b11101011_jmp_direct_short,
    0b11101100 => parse_0b1110110x_in_variable,
    0b11101101 => parse_0b1110110x_in_variable,
    0b11101110 => parse_0b1110111x_out_variable,
    0b11101111 => parse_0b1110111x_out_variable,
    0b11110000 => fail_0b11110000_lock_prefix,
    0b11110001 => fail_unused,
    0b11110010 => fail_0b1111001x_rep_prefix,
    0b11110011 => fail_0b1111001x_rep_prefix,
    0b11110100 => parse_0b11110100_hlt,
    0b11110101 => parse_0b11110101_cmc,
    0b11110110 => parse_0b1111011x_test_not_neg_mul_imul_div_idiv,
    0b11110111 => parse_0b1111011x_test_not_neg_mul_imul_div_idiv,
    0b11111000 => parse_0b11111000_clc,
    0b11111001 => parse_0b11111001_stc,
    0b11111010 => parse_0b11111010_cli,
    0b11111011 => parse_0b11111011_sti,
    0b11111100 => parse_0b11111100_cld,
    0b11111101 => parse_0b11111101_std,
    0b11111110 => parse_0b1111111x_inc_dec_call_jmp_push_rm,
    0b11111111 => parse_0b1111111x_inc_dec_call_jmp_push_rm,
}

fn parse_0b11110000_lock_prefix(_b1: u8, prefix_state: PrefixState) -> PrefixState {
    prefix_state.activate_lock()
}

fn parse_0b1111001x_rep_prefix(b1: u8, prefix_state: PrefixState) -> PrefixState {
    let z = b1 & 1 != 0;
    prefix_state.activate_rep(z)
}

fn parse_0b001xx110_segment_override_prefix(b1: u8, prefix_state: PrefixState) -> PrefixState {
    let sr = (b1 & 0b11000) >> 3;
    let sr = SegmentReg::try_from(sr).unwrap();
    prefix_state.activate_segment_override_prefix(sr)
}

pub fn parse_prefixed_instruction<R: Read, F: FnMut(u8, &mut R) -> Instruction>(
    mut b1: u8,
    input: &mut R,
    mut parse_func: F,
) -> PrefixedInstruction {
    let mut prefix_state = PrefixState::default();
    loop {
        prefix_state = match b1 {
            0b11110000 => parse_0b11110000_lock_prefix(b1, prefix_state),

            0b1111001_0 => parse_0b1111001x_rep_prefix(b1, prefix_state),
            0b1111001_1 => parse_0b1111001x_rep_prefix(b1, prefix_state),

            0b001_00_110 => parse_0b001xx110_segment_override_prefix(b1, prefix_state),
            0b001_01_110 => parse_0b001xx110_segment_override_prefix(b1, prefix_state),
            0b001_10_110 => parse_0b001xx110_segment_override_prefix(b1, prefix_state),
            0b001_11_110 => parse_0b001xx110_segment_override_prefix(b1, prefix_state),

            b1 => {
                let instruction = parse_func(b1, input);
                return PrefixedInstruction(instruction, prefix_state);
            }
        };
        b1 = next_byte_or_panic(input);
    }
}

#[cfg(test)]
mod tests {
    // #[test]
    // fn print_match_table() {
    //     for i in 0b00000000..=0b11111111 {
    //         println!("{:#010b} => parse_unimplemented(b1, input),", i);
    //     }
    // }
}
