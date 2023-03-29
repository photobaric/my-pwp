use std::io::Write;

use crate::model::{
    ByteOrWord, ByteReg, CompleteInstruction, Instruction, ModRM, Reg, SegmentReg, WordReg,
};

#[derive(Clone, Debug, Default)]
pub struct MachineState {
    pub gprs: [u16; 8],
    pub srs: [u16; 4],
}

impl MachineState {
    pub fn execute_instruction(&mut self, complete_instruction: CompleteInstruction) {
        let CompleteInstruction(instruction, _) = complete_instruction;
        match instruction {
            Instruction::MovRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if is_reg_dst {
                    match rm {
                        ModRM::Reg(src_reg) => self.mov_reg_to_reg(reg, src_reg),
                        _ => todo!(),
                    }
                } else {
                    match rm {
                        ModRM::Reg(dst_reg) => self.mov_reg_to_reg(dst_reg, reg),
                        _ => todo!(),
                    }
                }
            }
            Instruction::MovImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(dst_reg) => match (dst_reg, immediate) {
                    (Reg::ByteReg(byte_reg), ByteOrWord::Byte(byte)) => {
                        self.write_byte_to_byte_reg(byte_reg, byte);
                    }
                    (Reg::WordReg(word_reg), ByteOrWord::Word(word)) => {
                        self.gprs[word_reg as usize] = word;
                    }
                    (Reg::SegmentReg(_), _) => unreachable!(),
                    (Reg::ByteReg(_), ByteOrWord::Word(_)) => unreachable!(),
                    (Reg::WordReg(_), ByteOrWord::Byte(_)) => unreachable!(),
                },
                _ => todo!(),
            },
            _ => todo!(),
        }
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

    pub fn write_byte_to_byte_reg(&mut self, byte_reg: ByteReg, byte: u8) {
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

    pub fn mov_reg_to_reg(&mut self, dst_reg: Reg, src_reg: Reg) {
        match (dst_reg, src_reg) {
            (Reg::ByteReg(dst_byte_reg), Reg::ByteReg(src_byte_reg)) => {
                self.write_byte_to_byte_reg(dst_byte_reg, self.read_byte_reg(src_byte_reg));
            }
            (Reg::WordReg(dst_word_reg), Reg::WordReg(src_word_reg)) => {
                self.gprs[dst_word_reg as usize] = self.gprs[src_word_reg as usize];
            }

            (Reg::SegmentReg(segment_reg), Reg::WordReg(word_reg)) => {
                self.srs[segment_reg as usize] = self.gprs[word_reg as usize];
            }
            (Reg::WordReg(word_reg), Reg::SegmentReg(segment_reg)) => {
                self.gprs[word_reg as usize] = self.srs[segment_reg as usize];
            }

            (Reg::ByteReg(_), Reg::WordReg(_)) => unreachable!(),
            (Reg::ByteReg(_), Reg::SegmentReg(_)) => unreachable!(),
            (Reg::WordReg(_), Reg::ByteReg(_)) => unreachable!(),
            (Reg::SegmentReg(_), Reg::ByteReg(_)) => unreachable!(),
            (Reg::SegmentReg(_), Reg::SegmentReg(_)) => unreachable!(),
        };
    }
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
                Reg::ByteReg(byte_reg) => {
                    let value = self.read_byte_reg(*byte_reg);
                    writeln!(
                        output,
                        "{} {}: {:#06x} ({})",
                        prefix, byte_reg, value, value
                    )?;
                }
                Reg::WordReg(word_reg) => {
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
