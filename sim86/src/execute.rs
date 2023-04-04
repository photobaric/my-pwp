use std::io::Write;

use crate::model::{
    ByteOrWord, ByteReg, Instruction, PrefixedInstruction, RegMemOperand, RegOperand, SegmentReg,
    WordReg,
};

#[derive(Clone, Debug, Default)]
pub struct MachineState {
    pub gprs: [u16; 8],
    pub srs: [u16; 4],
    pub flags_reg: u16,
}

macro_rules! rw_flag {
    ($read_flag_fn:ident, $write_flag_fn:ident, $bitpos:literal) => {
        pub fn $read_flag_fn(flags: u16) -> bool {
            flags & (1 << $bitpos) != 0
        }

        pub fn $write_flag_fn(&mut self, flag: bool) {
            let flag: u16 = flag.into();
            // TODO(photobaric): Need two dependent ops?
            // see https://stackoverflow.com/questions/47981/how-do-i-set-clear-and-toggle-a-single-bit
            self.flags_reg &= !(1 << $bitpos);
            self.flags_reg |= (flag << $bitpos);
        }
    };
}

macro_rules! compute_af {
    ($a:ident, $b:ident, $r:ident) => {
        // AF is basically the CF but looking at the 4th bit instead of the 8th bit.
        // We want the following truth table for the 5th bit:
        // a, b, res, af
        // 0, 0, 0, 0
        // 0, 0, 1, 1
        // 0, 1, 0, 1
        // 0, 1, 1, 0
        // 1, 0, 0, 1
        // 1, 0, 1, 0
        // 1, 1, 0, 0
        // 1, 1, 1, 1
        // Note that this is the same bit pattern as a full adder
        // which is implemented as two XOR gates.
        ($a ^ $b ^ $r) & 0b10000 != 0
    };
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
                    pub fn mov_reg_to_reg(
                        state: &mut MachineState,
                        dst_reg: RegOperand,
                        src_reg: RegOperand,
                    ) {
                        match (dst_reg, src_reg) {
                            (RegOperand::Reg8(dst_byte_reg), RegOperand::Reg8(src_byte_reg)) => {
                                state.write_byte_reg(
                                    dst_byte_reg,
                                    state.read_byte_reg(src_byte_reg),
                                );
                            }
                            (RegOperand::Reg16(dst_word_reg), RegOperand::Reg16(src_word_reg)) => {
                                state.write_word_reg(
                                    dst_word_reg,
                                    state.read_word_reg(src_word_reg),
                                );
                            }

                            (RegOperand::Reg8(_), RegOperand::Reg16(_)) => unreachable!(),
                            (RegOperand::Reg16(_), RegOperand::Reg8(_)) => unreachable!(),
                        };
                    }
                    if is_reg_dst {
                        mov_reg_to_reg(self, reg, rm_reg)
                    } else {
                        mov_reg_to_reg(self, rm_reg, reg)
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

            Instruction::AddRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => match rm {
                RegMemOperand::Reg(rm_reg) => {
                    pub fn add_reg_to_reg(
                        state: &mut MachineState,
                        dst_reg: RegOperand,
                        src_reg: RegOperand,
                    ) {
                        match (dst_reg, src_reg) {
                            (RegOperand::Reg8(dst_reg), RegOperand::Reg8(src_reg)) => {
                                let dst_value = state.read_byte_reg(dst_reg);
                                let src_value = state.read_byte_reg(src_reg);

                                let (result, cf) = u8::overflowing_add(dst_value, src_value);
                                let (_, of) = i8::overflowing_add(dst_value as i8, src_value as i8);
                                state.write_byte_reg(dst_reg, result);
                                state.write_cf(cf);
                                state.write_of(of);
                                state.write_sf((result as i8) < 0);
                                state.write_pf((result as u8).count_ones() % 2 == 0);
                                state.write_zf(result == 0);

                                state.write_af(compute_af!(dst_value, src_value, result));
                            }
                            (RegOperand::Reg16(dst_reg), RegOperand::Reg16(src_reg)) => {
                                let dst_value = state.read_word_reg(dst_reg);
                                let src_value = state.read_word_reg(src_reg);

                                let (result, cf) = u16::overflowing_add(dst_value, src_value);
                                let (_, of) =
                                    i16::overflowing_add(dst_value as i16, src_value as i16);
                                state.write_word_reg(dst_reg, result);
                                state.write_cf(cf);
                                state.write_of(of);
                                state.write_sf((result as i16) < 0);
                                state.write_pf((result as u8).count_ones() % 2 == 0);
                                state.write_zf(result == 0);

                                state.write_af(compute_af!(dst_value, src_value, result));
                            }

                            (RegOperand::Reg8(_), RegOperand::Reg16(_)) => unreachable!(),
                            (RegOperand::Reg16(_), RegOperand::Reg8(_)) => unreachable!(),
                        };
                    }
                    if is_reg_dst {
                        add_reg_to_reg(self, reg, rm_reg)
                    } else {
                        add_reg_to_reg(self, rm_reg, reg)
                    }
                }
                RegMemOperand::Mem(_) => todo!(),
            },
            Instruction::AddImmediateToRm { rm, immediate } => match rm {
                RegMemOperand::Reg(reg) => match (reg, immediate) {
                    (RegOperand::Reg8(reg), ByteOrWord::Byte(b)) => {
                        let a = self.read_byte_reg(reg);

                        let (r, cf) = u8::overflowing_add(a, b);
                        let (_, of) = i8::overflowing_add(a as i8, b as i8);
                        self.write_byte_reg(reg, r);
                        self.write_cf(cf);
                        self.write_of(of);
                        self.write_sf((r as i8) < 0);
                        self.write_pf((r as u8).count_ones() % 2 == 0);
                        self.write_zf(r == 0);

                        self.write_af(compute_af!(a, b, r));
                    }
                    (RegOperand::Reg16(reg), ByteOrWord::Word(b)) => {
                        let a = self.read_word_reg(reg);

                        let (r, cf) = u16::overflowing_add(a, b);
                        let (_, of) = i16::overflowing_add(a as i16, b as i16);
                        self.write_word_reg(reg, r);
                        self.write_cf(cf);
                        self.write_of(of);
                        self.write_sf((r as i16) < 0);
                        self.write_pf((r as u8).count_ones() % 2 == 0);
                        self.write_zf(r == 0);

                        self.write_af(compute_af!(a, b, r));
                    }

                    (RegOperand::Reg8(_), ByteOrWord::Word(_)) => unreachable!(),
                    (RegOperand::Reg16(_), ByteOrWord::Byte(_)) => unreachable!(),
                },
                RegMemOperand::Mem(_) => todo!(),
            },

            Instruction::SubRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => match rm {
                RegMemOperand::Reg(rm_reg) => {
                    pub fn sub_reg_to_reg(
                        state: &mut MachineState,
                        dst_reg: RegOperand,
                        src_reg: RegOperand,
                    ) {
                        match (dst_reg, src_reg) {
                            (RegOperand::Reg8(dst_reg), RegOperand::Reg8(src_reg)) => {
                                let dst_value = state.read_byte_reg(dst_reg);
                                let src_value = state.read_byte_reg(src_reg);

                                let (result, cf) = u8::overflowing_sub(dst_value, src_value);
                                let (_, of) = i8::overflowing_sub(dst_value as i8, src_value as i8);
                                state.write_byte_reg(dst_reg, result);
                                state.write_cf(cf);
                                state.write_of(of);
                                state.write_sf((result as i8) < 0);
                                state.write_pf((result as u8).count_ones() % 2 == 0);
                                state.write_zf(result == 0);

                                state.write_af(compute_af!(dst_value, src_value, result));
                            }
                            (RegOperand::Reg16(dst_reg), RegOperand::Reg16(src_reg)) => {
                                let dst_value = state.read_word_reg(dst_reg);
                                let src_value = state.read_word_reg(src_reg);

                                let (result, cf) = u16::overflowing_sub(dst_value, src_value);
                                let (_, of) =
                                    i16::overflowing_sub(dst_value as i16, src_value as i16);
                                state.write_word_reg(dst_reg, result);
                                state.write_cf(cf);
                                state.write_of(of);
                                state.write_sf((result as i16) < 0);
                                state.write_pf((result as u8).count_ones() % 2 == 0);
                                state.write_zf(result == 0);

                                state.write_af(compute_af!(dst_value, src_value, result));
                            }

                            (RegOperand::Reg8(_), RegOperand::Reg16(_)) => unreachable!(),
                            (RegOperand::Reg16(_), RegOperand::Reg8(_)) => unreachable!(),
                        };
                    }
                    if is_reg_dst {
                        sub_reg_to_reg(self, reg, rm_reg)
                    } else {
                        sub_reg_to_reg(self, rm_reg, reg)
                    }
                }
                RegMemOperand::Mem(_) => todo!(),
            },
            Instruction::SubImmediateToRm { rm, immediate } => match rm {
                RegMemOperand::Reg(reg) => match (reg, immediate) {
                    (RegOperand::Reg8(reg), ByteOrWord::Byte(b)) => {
                        let a = self.read_byte_reg(reg);

                        let (r, cf) = u8::overflowing_sub(a, b);
                        let (_, of) = i8::overflowing_sub(a as i8, b as i8);
                        self.write_byte_reg(reg, r);
                        self.write_cf(cf);
                        self.write_of(of);
                        self.write_sf((r as i8) < 0);
                        self.write_pf((r as u8).count_ones() % 2 == 0);
                        self.write_zf(r == 0);

                        self.write_af(compute_af!(a, b, r));
                    }
                    (RegOperand::Reg16(reg), ByteOrWord::Word(b)) => {
                        let a = self.read_word_reg(reg);

                        let (r, cf) = u16::overflowing_sub(a, b);
                        let (_, of) = i16::overflowing_sub(a as i16, b as i16);
                        self.write_word_reg(reg, r);
                        self.write_cf(cf);
                        self.write_of(of);
                        self.write_sf((r as i16) < 0);
                        self.write_pf((r as u8).count_ones() % 2 == 0);
                        self.write_zf(r == 0);

                        self.write_af(compute_af!(a, b, r));
                    }

                    (RegOperand::Reg8(_), ByteOrWord::Word(_)) => unreachable!(),
                    (RegOperand::Reg16(_), ByteOrWord::Byte(_)) => unreachable!(),
                },
                RegMemOperand::Mem(_) => todo!(),
            },

            Instruction::CmpRmToReg {
                is_reg_dst,
                reg,
                rm,
            } => match rm {
                RegMemOperand::Reg(rm_reg) => {
                    pub fn cmp_reg_to_reg(
                        state: &mut MachineState,
                        dst_reg: RegOperand,
                        src_reg: RegOperand,
                    ) {
                        match (dst_reg, src_reg) {
                            (RegOperand::Reg8(dst_reg), RegOperand::Reg8(src_reg)) => {
                                let dst_value = state.read_byte_reg(dst_reg);
                                let src_value = state.read_byte_reg(src_reg);

                                let (result, cf) = u8::overflowing_sub(dst_value, src_value);
                                let (_, of) = i8::overflowing_sub(dst_value as i8, src_value as i8);
                                state.write_cf(cf);
                                state.write_of(of);
                                state.write_sf((result as i8) < 0);
                                state.write_pf((result as u8).count_ones() % 2 == 0);
                                state.write_zf(result == 0);

                                state.write_af(compute_af!(dst_value, src_value, result));
                            }
                            (RegOperand::Reg16(dst_reg), RegOperand::Reg16(src_reg)) => {
                                let dst_value = state.read_word_reg(dst_reg);
                                let src_value = state.read_word_reg(src_reg);

                                let (result, cf) = u16::overflowing_sub(dst_value, src_value);
                                let (_, of) =
                                    i16::overflowing_sub(dst_value as i16, src_value as i16);
                                state.write_cf(cf);
                                state.write_of(of);
                                state.write_sf((result as i16) < 0);
                                state.write_pf((result as u8).count_ones() % 2 == 0);
                                state.write_zf(result == 0);

                                state.write_af(compute_af!(dst_value, src_value, result));
                            }

                            (RegOperand::Reg8(_), RegOperand::Reg16(_)) => unreachable!(),
                            (RegOperand::Reg16(_), RegOperand::Reg8(_)) => unreachable!(),
                        };
                    }
                    if is_reg_dst {
                        cmp_reg_to_reg(self, reg, rm_reg)
                    } else {
                        cmp_reg_to_reg(self, rm_reg, reg)
                    }
                }
                RegMemOperand::Mem(_) => todo!(),
            },
            Instruction::CmpImmediateToRm { rm, immediate } => match rm {
                RegMemOperand::Reg(reg) => match (reg, immediate) {
                    (RegOperand::Reg8(reg), ByteOrWord::Byte(b)) => {
                        let a = self.read_byte_reg(reg);

                        let (r, cf) = u8::overflowing_sub(a, b);
                        let (_, of) = i8::overflowing_sub(a as i8, b as i8);
                        self.write_cf(cf);
                        self.write_of(of);
                        self.write_sf((r as i8) < 0);
                        self.write_pf((r as u8).count_ones() % 2 == 0);
                        self.write_zf(r == 0);

                        self.write_af(compute_af!(a, b, r));
                    }
                    (RegOperand::Reg16(reg), ByteOrWord::Word(b)) => {
                        let a = self.read_word_reg(reg);

                        let (r, cf) = u16::overflowing_sub(a, b);
                        let (_, of) = i16::overflowing_sub(a as i16, b as i16);
                        self.write_cf(cf);
                        self.write_of(of);
                        self.write_sf((r as i16) < 0);
                        self.write_pf((r as u8).count_ones() % 2 == 0);
                        self.write_zf(r == 0);

                        self.write_af(compute_af!(a, b, r));
                    }

                    (RegOperand::Reg8(_), ByteOrWord::Word(_)) => unreachable!(),
                    (RegOperand::Reg16(_), ByteOrWord::Byte(_)) => unreachable!(),
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

    rw_flag!(read_cf, write_cf, 0);
    rw_flag!(read_pf, write_pf, 2);
    rw_flag!(read_af, write_af, 4);
    rw_flag!(read_zf, write_zf, 6);
    rw_flag!(read_sf, write_sf, 7);

    rw_flag!(read_tf, write_tf, 8);
    rw_flag!(read_if, write_if, 9);
    rw_flag!(read_df, write_df, 10);
    rw_flag!(read_of, write_of, 11);
}

#[derive(Clone, Copy, Debug)]
pub enum Reg {
    Reg8(ByteReg),
    Reg16(WordReg),
    SegmentReg(SegmentReg),
    FlagsReg,
}

impl MachineState {
    pub fn print_register<W: Write>(&self, reg: Reg, output: &mut W) -> Result<(), anyhow::Error> {
        match reg {
            Reg::Reg8(byte_reg) => {
                let value = self.read_byte_reg(byte_reg);
                writeln!(output, "{}: {:#06x} ({})", byte_reg, value, value)?;
            }
            Reg::Reg16(word_reg) => {
                let value = self.gprs[word_reg as usize];
                writeln!(output, "{}: {:#06x} ({})", word_reg, value, value)?;
            }
            Reg::SegmentReg(segment_reg) => {
                let value = self.srs[segment_reg as usize];
                writeln!(output, "{}: {:#06x} ({})", segment_reg, value, value)?;
            }
            Reg::FlagsReg => {
                let value = self.flags_reg;
                writeln!(output, "flags: {}", Flags(value),)?;
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
    FlagsReg(u16, u16),
}

impl ::std::fmt::Display for MachineStateDiff {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MachineStateDiff::Gpr(gpr, prev, next) => write!(f, "{}:{:#x}->{:#x}", gpr, prev, next),
            MachineStateDiff::Sr(sr, prev, next) => write!(f, "{}:{:#x}->{:#x}", sr, prev, next),
            MachineStateDiff::FlagsReg(prev, next) => {
                write!(f, "flags:{}->{}", Flags(*prev), Flags(*next))
            }
        }
    }
}

pub struct Flags(u16);

impl ::std::fmt::Display for Flags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let flags = self.0;
        if MachineState::read_cf(flags) {
            write!(f, "C")?;
        }
        if MachineState::read_pf(flags) {
            write!(f, "P")?;
        }
        if MachineState::read_af(flags) {
            write!(f, "A")?;
        }
        if MachineState::read_zf(flags) {
            write!(f, "Z")?;
        }
        if MachineState::read_sf(flags) {
            write!(f, "S")?;
        }
        if MachineState::read_tf(flags) {
            write!(f, "T")?;
        }
        if MachineState::read_if(flags) {
            write!(f, "I")?;
        }
        if MachineState::read_df(flags) {
            write!(f, "D")?;
        }
        if MachineState::read_of(flags) {
            write!(f, "O")?;
        }
        std::fmt::Result::Ok(())
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
        {
            let prev_flags_reg = prev_state.flags_reg;
            let next_flags_reg = next_state.flags_reg;
            if prev_flags_reg != next_flags_reg {
                let diff = MachineStateDiff::FlagsReg(prev_flags_reg, next_flags_reg);
                process_diff(diff);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_af_formula() {
        pub fn compute_af_v1(a: u8, b: u8) -> bool {
            let (res, _) = u8::overflowing_add(a, b);
            compute_af!(a, b, res)
        }

        pub fn compute_af_v2(a: u8, b: u8) -> bool {
            let a = a << 4;
            let b = b << 4;
            let (_, cf) = u8::overflowing_add(a, b);
            cf
        }

        for a in 0x00u8..=0xFFu8 {
            for b in 0x00u8..=0xFFu8 {
                let af1 = compute_af_v1(a, b);
                let af2 = compute_af_v2(a, b);
                assert_eq!(af1, af2, "found disagreement {:#06b} {:#06b}", a, b);
            }
        }
    }
}
