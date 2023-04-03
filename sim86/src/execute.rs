use std::io::Write;

use crate::model::{
    ByteOrWord, ByteReg, Instruction, PrefixedInstruction, RegMemOperand, RegOperand, SegmentReg,
    WordReg,
};

#[derive(Clone, Debug, Default)]
pub struct MachineState {
    pub gprs: [u16; 8],
    pub srs: [u16; 4],
}

impl MachineState {
    pub fn execute_instruction(&mut self, prefixed_instruction: PrefixedInstruction) {
        let PrefixedInstruction(instruction, _) = prefixed_instruction;
        match instruction {
            Instruction::MovRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => match rm {
                RegMemOperand::Reg(rm_reg) => {
                    if is_reg_dst {
                        self.mov_reg_to_reg(reg, rm_reg)
                    } else {
                        self.mov_reg_to_reg(rm_reg, reg)
                    }
                }
                RegMemOperand::Mem(_) => todo!(),
            },
            Instruction::MovImmediateToRm { rm, immediate } => match rm {
                RegMemOperand::Reg(dst_reg) => match (dst_reg, immediate) {
                    (RegOperand::Reg8(byte_reg), ByteOrWord::Byte(byte)) => {
                        self.write_byte_reg(byte_reg, byte);
                    }
                    (RegOperand::Reg16(word_reg), ByteOrWord::Word(word)) => {
                        self.gprs[word_reg as usize] = word;
                    }
                    (RegOperand::Reg8(_), ByteOrWord::Word(_)) => unreachable!(),
                    (RegOperand::Reg16(_), ByteOrWord::Byte(_)) => unreachable!(),
                },
                _ => todo!(),
            },
            Instruction::MovRmToFromSegmentReg {
                is_segment_reg_dst,
                rm,
                segment_reg,
            } => match rm {
                RegMemOperand::Reg(reg) => match reg {
                    RegOperand::Reg8(_) => unreachable!(),
                    RegOperand::Reg16(word_reg) => {
                        if is_segment_reg_dst {
                            self.write_segment_reg(segment_reg, self.read_word_reg(word_reg));
                        } else {
                            self.write_word_reg(word_reg, self.read_segment_reg(segment_reg));
                        }
                    }
                },
                RegMemOperand::Mem(_) => todo!(),
            },
            _ => todo!(),
        }
    }

    #[inline(always)]
    pub fn read_word_reg(&self, word_reg: WordReg) -> u16 {
        self.gprs[word_reg as usize]
    }

    #[inline(always)]
    pub fn write_word_reg(&mut self, word_reg: WordReg, word: u16) {
        self.gprs[word_reg as usize] = word;
    }

    pub fn read_byte_reg(&self, byte_reg: ByteReg) -> u8 {
        let byte_reg: u8 = byte_reg as u8;
        let gpr = byte_reg & 0b11;
        let is_high = (byte_reg & 0b100) != 0;
        if is_high {
            (self.gprs[gpr as usize] >> 8) as u8
        } else {
            (self.gprs[gpr as usize]) as u8
        }
    }

    pub fn write_byte_reg(&mut self, byte_reg: ByteReg, byte: u8) {
        let byte_reg: u8 = byte_reg as u8;
        let gpr = byte_reg & 0b11;
        let is_high = (byte_reg & 0b100) != 0;
        if is_high {
            let high_bits_cleared = self.gprs[gpr as usize] & 0x00FFu16;
            self.gprs[gpr as usize] = high_bits_cleared | ((byte as u16) << 8);
        } else {
            let low_bits_cleared = self.gprs[gpr as usize] & 0xFF00u16;
            self.gprs[gpr as usize] = low_bits_cleared | (byte as u16);
        }
    }

    #[inline(always)]
    pub fn read_segment_reg(&self, segment_reg: SegmentReg) -> u16 {
        self.srs[segment_reg as usize]
    }

    #[inline(always)]
    pub fn write_segment_reg(&mut self, segment_reg: SegmentReg, word: u16) {
        self.srs[segment_reg as usize] = word;
    }

    pub fn mov_reg_to_reg(&mut self, dst_reg: RegOperand, src_reg: RegOperand) {
        match (dst_reg, src_reg) {
            (RegOperand::Reg8(dst_byte_reg), RegOperand::Reg8(src_byte_reg)) => {
                self.write_byte_reg(dst_byte_reg, self.read_byte_reg(src_byte_reg));
            }
            (RegOperand::Reg16(dst_word_reg), RegOperand::Reg16(src_word_reg)) => {
                self.write_word_reg(dst_word_reg, self.read_word_reg(src_word_reg));
            }

            (RegOperand::Reg8(_), RegOperand::Reg16(_)) => unreachable!(),
            (RegOperand::Reg16(_), RegOperand::Reg8(_)) => unreachable!(),
        };
    }
}

#[derive(Clone, Debug)]
pub enum Reg {
    Reg8(ByteReg),
    Reg16(WordReg),
    SegmentReg(SegmentReg),
}

impl MachineState {
    pub fn print_registers<W: Write>(
        &self,
        prefix: &str,
        registers: &[Reg],
        output: &mut W,
    ) -> Result<(), anyhow::Error> {
        for reg in registers {
            match reg {
                Reg::Reg8(byte_reg) => {
                    let value = self.read_byte_reg(*byte_reg);
                    writeln!(
                        output,
                        "{} {}: {:#06x} ({})",
                        prefix, byte_reg, value, value
                    )?;
                }
                Reg::Reg16(word_reg) => {
                    let value = self.gprs[*word_reg as usize];
                    writeln!(
                        output,
                        "{} {}: {:#06x} ({})",
                        prefix, word_reg, value, value
                    )?;
                }
                Reg::SegmentReg(segment_reg) => {
                    let value = self.srs[*segment_reg as usize];
                    writeln!(
                        output,
                        "{} {}: {:#06x} ({})",
                        prefix, segment_reg, value, value
                    )?;
                }
            }
        }
        Ok(())
    }

    pub fn print_all_registers<W: Write>(&self, output: &mut W) -> Result<(), anyhow::Error> {
        for gpr in 0b000u8..=0b111u8 {
            let gpr: WordReg = WordReg::try_from(gpr).unwrap();
            let value = self.gprs[gpr as usize];
            writeln!(output, "{}: {:#06x} ({})", gpr, value, value)?;
        }
        for sr in 0b00u8..=0b11u8 {
            let sr: SegmentReg = SegmentReg::try_from(sr).unwrap();
            let value = self.srs[sr as usize];
            writeln!(output, "{}: {:#06x} ({})", sr, value, value)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum MachineStateDiff {
    Gpr(WordReg, u16, u16),
    Sr(SegmentReg, u16, u16),
}

impl ::std::fmt::Display for MachineStateDiff {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MachineStateDiff::Gpr(gpr, prev, next) => write!(f, "{}:{:#x}->{:#x}", gpr, prev, next),
            MachineStateDiff::Sr(sr, prev, next) => write!(f, "{}:{:#x}->{:#x}", sr, prev, next),
        }
    }
}

impl MachineStateDiff {
    pub fn diff<F: FnMut(MachineStateDiff) -> ()>(
        prev_state: &MachineState,
        next_state: &MachineState,
        mut process_diff: F,
    ) {
        for gpr in 0b000u8..=0b111u8 {
            let gpr: WordReg = WordReg::try_from(gpr).unwrap();
            let prev = prev_state.gprs[gpr as usize];
            let next = next_state.gprs[gpr as usize];
            if prev != next {
                let diff = MachineStateDiff::Gpr(gpr, prev, next);
                process_diff(diff);
            }
        }
        for sr in 0b00u8..=0b11u8 {
            let sr: SegmentReg = SegmentReg::try_from(sr).unwrap();
            let prev = prev_state.srs[sr as usize];
            let next = next_state.srs[sr as usize];
            if prev != next {
                let diff = MachineStateDiff::Sr(sr, prev, next);
                process_diff(diff);
            }
        }
    }
}
