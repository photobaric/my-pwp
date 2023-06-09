use std::io::Write;

use crate::model::{
    ByteOrWord, ByteReg, Instruction, PrefixedInstruction, RegMemOperand, RegOperand, SegmentReg,
    WordReg,
};

#[derive(Clone, Debug, Default)]
pub struct MachineState {
    pub gprs: [u16; 8],
    pub srs: [u16; 4],
    pub ip_reg: u16,
    pub flags_reg: Flags,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Flags(u16);

macro_rules! rw_flag {
    ($read_flag_fn:ident, $write_flag_fn:ident, $bitpos:literal) => {
        #[inline(always)]
        pub fn $read_flag_fn(&self) -> bool {
            self.0 & (1 << $bitpos) != 0
        }

        #[inline(always)]
        pub fn $write_flag_fn(&mut self, flag: bool) {
            let flag: u16 = flag.into();
            // TODO(photobaric): Need two dependent ops?
            // see https://stackoverflow.com/questions/47981/how-do-i-set-clear-and-toggle-a-single-bit
            self.0 &= !(1 << $bitpos);
            self.0 |= (flag << $bitpos);
        }
    };
}

macro_rules! compute_pf {
    ($r:ident) => {
        // This gets optimized by LLVM into a single setp instruction:
        // https://godbolt.org/z/Y31E7jh7T
        // This means we are implementing the parity flag using the parity flag itself!
        //
        // Note that PF only examines the lower 8 bits (Page 2-35)
        ($r as u8).count_ones() % 2 == 0
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

impl Flags {
    rw_flag!(read_cf, write_cf, 0);
    rw_flag!(read_pf, write_pf, 2);
    rw_flag!(read_af, write_af, 4);
    rw_flag!(read_zf, write_zf, 6);
    rw_flag!(read_sf, write_sf, 7);

    rw_flag!(read_tf, write_tf, 8);
    rw_flag!(read_if, write_if, 9);
    rw_flag!(read_df, write_df, 10);
    rw_flag!(read_of, write_of, 11);

    fn write_flags_u8(&mut self, a: u8, b: u8, r: u8, cf: bool, of: bool) {
        self.write_cf(cf);
        self.write_of(of);
        self.write_sf((r as i8) < 0);
        self.write_pf(compute_pf!(r));
        self.write_zf(r == 0);
        self.write_af(compute_af!(a, b, r));
    }

    fn write_flags_u16(&mut self, a: u16, b: u16, r: u16, cf: bool, of: bool) {
        self.write_cf(cf);
        self.write_of(of);
        self.write_sf((r as i16) < 0);
        self.write_pf(compute_pf!(r));
        self.write_zf(r == 0);
        self.write_af(compute_af!(a, b, r));
    }
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
                                let a = state.read_byte_reg(dst_reg);
                                let b = state.read_byte_reg(src_reg);

                                let (r, cf) = u8::overflowing_add(a, b);
                                let (_, of) = i8::overflowing_add(a as i8, b as i8);
                                state.write_byte_reg(dst_reg, r);
                                state.flags_reg.write_flags_u8(a, b, r, cf, of);
                            }
                            (RegOperand::Reg16(dst_reg), RegOperand::Reg16(src_reg)) => {
                                let a = state.read_word_reg(dst_reg);
                                let b = state.read_word_reg(src_reg);

                                let (r, cf) = u16::overflowing_add(a, b);
                                let (_, of) = i16::overflowing_add(a as i16, b as i16);
                                state.write_word_reg(dst_reg, r);
                                state.flags_reg.write_flags_u16(a, b, r, cf, of);
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
                        self.flags_reg.write_flags_u8(a, b, r, cf, of);
                    }
                    (RegOperand::Reg16(reg), ByteOrWord::Word(b)) => {
                        let a = self.read_word_reg(reg);

                        let (r, cf) = u16::overflowing_add(a, b);
                        let (_, of) = i16::overflowing_add(a as i16, b as i16);
                        self.write_word_reg(reg, r);
                        self.flags_reg.write_flags_u16(a, b, r, cf, of);
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
                                let a = state.read_byte_reg(dst_reg);
                                let b = state.read_byte_reg(src_reg);

                                let (r, cf) = u8::overflowing_sub(a, b);
                                let (_, of) = i8::overflowing_sub(a as i8, b as i8);
                                state.write_byte_reg(dst_reg, r);
                                state.flags_reg.write_flags_u8(a, b, r, cf, of);
                            }
                            (RegOperand::Reg16(dst_reg), RegOperand::Reg16(src_reg)) => {
                                let a = state.read_word_reg(dst_reg);
                                let b = state.read_word_reg(src_reg);

                                let (r, cf) = u16::overflowing_sub(a, b);
                                let (_, of) = i16::overflowing_sub(a as i16, b as i16);
                                state.write_word_reg(dst_reg, r);
                                state.flags_reg.write_flags_u16(a, b, r, cf, of);
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
                        self.flags_reg.write_flags_u8(a, b, r, cf, of);
                    }
                    (RegOperand::Reg16(reg), ByteOrWord::Word(b)) => {
                        let a = self.read_word_reg(reg);

                        let (r, cf) = u16::overflowing_sub(a, b);
                        let (_, of) = i16::overflowing_sub(a as i16, b as i16);
                        self.write_word_reg(reg, r);
                        self.flags_reg.write_flags_u16(a, b, r, cf, of);
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
                                let a = state.read_byte_reg(dst_reg);
                                let b = state.read_byte_reg(src_reg);

                                let (r, cf) = u8::overflowing_sub(a, b);
                                let (_, of) = i8::overflowing_sub(a as i8, b as i8);
                                state.flags_reg.write_flags_u8(a, b, r, cf, of);
                            }
                            (RegOperand::Reg16(dst_reg), RegOperand::Reg16(src_reg)) => {
                                let a = state.read_word_reg(dst_reg);
                                let b = state.read_word_reg(src_reg);

                                let (r, cf) = u16::overflowing_sub(a, b);
                                let (_, of) = i16::overflowing_sub(a as i16, b as i16);
                                state.flags_reg.write_flags_u16(a, b, r, cf, of);
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
                        self.flags_reg.write_flags_u8(a, b, r, cf, of);
                    }
                    (RegOperand::Reg16(reg), ByteOrWord::Word(b)) => {
                        let a = self.read_word_reg(reg);

                        let (r, cf) = u16::overflowing_sub(a, b);
                        let (_, of) = i16::overflowing_sub(a as i16, b as i16);
                        self.flags_reg.write_flags_u16(a, b, r, cf, of);
                    }

                    (RegOperand::Reg8(_), ByteOrWord::Word(_)) => unreachable!(),
                    (RegOperand::Reg16(_), ByteOrWord::Byte(_)) => unreachable!(),
                },
                RegMemOperand::Mem(_) => todo!(),
            },

            // See Table 2-15 on Page 2-46
            Instruction::JeJz { ip_inc8 } => {
                let zf = self.flags_reg.read_zf();
                let condition = zf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JlJnge { ip_inc8 } => {
                let sf = self.flags_reg.read_sf();
                let of = self.flags_reg.read_of();
                let condition = sf ^ of;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JleJng { ip_inc8 } => {
                let sf = self.flags_reg.read_sf();
                let of = self.flags_reg.read_of();
                let zf = self.flags_reg.read_zf();
                let condition = (sf ^ of) || zf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            // Note that Table 2-15 lists JC separately for some reason
            Instruction::JbJnaeJc { ip_inc8 } => {
                let cf = self.flags_reg.read_cf();
                let condition = cf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JbeJna { ip_inc8 } => {
                let cf = self.flags_reg.read_cf();
                let zf = self.flags_reg.read_zf();
                let condition = cf || zf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JpJpe { ip_inc8 } => {
                let pf = self.flags_reg.read_pf();
                let condition = pf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::Jo { ip_inc8 } => {
                let of = self.flags_reg.read_of();
                let condition = of;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::Js { ip_inc8 } => {
                let sf = self.flags_reg.read_sf();
                let condition = sf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JneJnz { ip_inc8 } => {
                let zf = self.flags_reg.read_zf();
                let condition = !zf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JnlJge { ip_inc8 } => {
                let sf = self.flags_reg.read_sf();
                let of = self.flags_reg.read_of();
                let condition = !(sf ^ of);
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JnleJg { ip_inc8 } => {
                let sf = self.flags_reg.read_sf();
                let of = self.flags_reg.read_of();
                let zf = self.flags_reg.read_zf();
                let condition = !((sf ^ of) || zf);
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            // Note that Table 2-15 lists JNC separately for some reason
            Instruction::JnbJaeJnc { ip_inc8 } => {
                let cf = self.flags_reg.read_cf();
                let condition = !cf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JnbeJa { ip_inc8 } => {
                let cf = self.flags_reg.read_cf();
                let zf = self.flags_reg.read_zf();
                let condition = !(cf || zf);
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::JnpJpo { ip_inc8 } => {
                let pf = self.flags_reg.read_pf();
                let condition = !pf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::Jno { ip_inc8 } => {
                let of = self.flags_reg.read_of();
                let condition = !of;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::Jns { ip_inc8 } => {
                let sf = self.flags_reg.read_sf();
                let condition = !sf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }

            Instruction::Loop { ip_inc8 } => {
                let cx = self.read_word_reg(WordReg::CX);
                let cx = cx.wrapping_sub(1);
                self.write_word_reg(WordReg::CX, cx);
                let condition = cx != 0;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::LoopeLoopz { ip_inc8 } => {
                let cx = self.read_word_reg(WordReg::CX);
                let cx = cx.wrapping_sub(1);
                self.write_word_reg(WordReg::CX, cx);

                let zf = self.flags_reg.read_zf();

                let condition = cx != 0 && zf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::LoopneLoopnz { ip_inc8 } => {
                let cx = self.read_word_reg(WordReg::CX);
                let cx = cx.wrapping_sub(1);
                self.write_word_reg(WordReg::CX, cx);

                let zf = self.flags_reg.read_zf();

                let condition = cx != 0 && !zf;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }
            Instruction::Jcxz { ip_inc8 } => {
                let cx = self.read_word_reg(WordReg::CX);
                let condition = cx == 0;
                if condition {
                    self.ip_inc8(ip_inc8);
                }
            }

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

    #[inline]
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

    #[inline]
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

    #[inline(always)]
    pub fn read_ip(&self) -> u16 {
        self.ip_reg
    }

    #[inline(always)]
    pub fn write_ip(&mut self, ip: u16) {
        self.ip_reg = ip;
    }

    #[inline(always)]
    pub fn ip_inc8(&mut self, ip_inc8: i8) {
        let ip_inc: i16 = ip_inc8.into();
        self.ip_reg = self.ip_reg.wrapping_add_signed(ip_inc);
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Reg {
    Reg8(ByteReg),
    Reg16(WordReg),
    SegmentReg(SegmentReg),
    IpReg,
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
            Reg::IpReg => {
                let value = self.ip_reg;
                writeln!(output, "ip: {:#06x} ({})", value, value)?;
            }
            Reg::FlagsReg => {
                let value = self.flags_reg;
                writeln!(output, "flags: {}", value)?;
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

        writeln!(output, "ip: {}", self.ip_reg)?;

        writeln!(output, "flags: {}", self.flags_reg)?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub enum MachineStateDiff {
    Gpr(WordReg, u16, u16),
    Sr(SegmentReg, u16, u16),
    IpReg(u16, u16),
    FlagsReg(u16, u16),
}

impl MachineStateDiff {
    pub fn diff<F: FnMut(MachineStateDiff)>(
        include_ip_diff: bool,
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
        if include_ip_diff {
            let prev_ip = prev_state.ip_reg;
            let next_ip = next_state.ip_reg;
            if prev_ip != next_ip {
                let diff = MachineStateDiff::IpReg(prev_ip, next_ip);
                process_diff(diff);
            }
        }
        {
            let prev_flags = prev_state.flags_reg;
            let next_flags = next_state.flags_reg;
            if prev_flags != next_flags {
                let diff = MachineStateDiff::FlagsReg(prev_flags.0, next_flags.0);
                process_diff(diff);
            }
        }
    }
}

impl ::std::fmt::Display for MachineStateDiff {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MachineStateDiff::Gpr(gpr, prev, next) => write!(f, "{}:{:#x}->{:#x}", gpr, prev, next),
            MachineStateDiff::Sr(sr, prev, next) => write!(f, "{}:{:#x}->{:#x}", sr, prev, next),
            MachineStateDiff::IpReg(prev, next) => write!(f, "ip:{:#x}->{:#x}", prev, next),
            MachineStateDiff::FlagsReg(prev, next) => {
                write!(f, "flags:{}->{}", Flags(*prev), Flags(*next))
            }
        }
    }
}

impl ::std::fmt::Display for Flags {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.read_cf() {
            write!(f, "C")?;
        }
        if self.read_pf() {
            write!(f, "P")?;
        }
        if self.read_af() {
            write!(f, "A")?;
        }
        if self.read_zf() {
            write!(f, "Z")?;
        }
        if self.read_sf() {
            write!(f, "S")?;
        }
        if self.read_tf() {
            write!(f, "T")?;
        }
        if self.read_if() {
            write!(f, "I")?;
        }
        if self.read_df() {
            write!(f, "D")?;
        }
        if self.read_of() {
            write!(f, "O")?;
        }
        std::fmt::Result::Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_af_formula() {
        pub fn compute_af_correctly(a: u8, b: u8) -> bool {
            let a = a << 4;
            let b = b << 4;
            let (_, cf) = u8::overflowing_add(a, b);
            cf
        }

        pub fn compute_af_formula(a: u8, b: u8) -> bool {
            let (res, _) = u8::overflowing_add(a, b);
            compute_af!(a, b, res)
        }

        for a in 0x00u8..=0xFFu8 {
            for b in 0x00u8..=0xFFu8 {
                let af = compute_af_correctly(a, b);
                let af1 = compute_af_formula(a, b);
                assert_eq!(af, af1, "found disagreement {:#06b} {:#06b}", a, b);
            }
        }
    }

    #[test]
    fn test_of_formula() {
        pub fn compute_of_correctly(a: u8, b: u8) -> bool {
            let (_, of) = i8::overflowing_add(a as i8, b as i8);
            of
        }

        // Truth table for the 8th bit:
        // a b r c
        // 0 0 0 0
        // 0 0 1 1
        // 0 1 0 0
        // 0 1 1 0
        // 1 0 0 0
        // 1 0 1 0
        // 1 1 0 1
        // 1 1 1 0
        //
        // LLVM output:
        //
        // compute_of_truth_table:
        // lea     ecx, [rsi + rdi]
        // mov     eax, esi
        // or      al, dil
        // and     sil, dil
        // xor     al, sil
        // not     al
        // and     al, cl
        // xor     al, sil
        // shr     al, 7
        // ret
        pub fn compute_of_truth_table(a: u8, b: u8) -> bool {
            let r = u8::wrapping_add(a, b);
            ((!a & !b & r) | (a & b & !r)) & 0x80 != 0
        }

        // LLVM output:
        //
        // compute_of_formula:
        // lea     eax, [rsi + rdi]
        // xor     al, dil
        // mov     ecx, edi
        // xor     cl, sil
        // not     cl
        // and     al, cl
        // shr     al, 7
        // ret
        pub fn compute_of_formula(a: u8, b: u8) -> bool {
            let r = u8::wrapping_add(a, b);
            (!(a ^ b) & (a ^ r)) & 0x80 != 0
        }

        for a in 0x00u8..=0xFFu8 {
            for b in 0x00u8..=0xFFu8 {
                let of = compute_of_correctly(a, b);
                let of1 = compute_of_truth_table(a, b);
                let of2 = compute_of_formula(a, b);
                assert_eq!(
                    of, of1,
                    "found disagreement for truth table {:#06b} {:#06b}",
                    a, b
                );
                assert_eq!(
                    of, of2,
                    "found disagreement for formula {:#06b} {:#06b}",
                    a, b
                );
            }
        }
    }

    #[test]
    fn test_cf_formula() {
        pub fn compute_cf_correctly(a: u8, b: u8) -> bool {
            let (_, cf) = u8::overflowing_add(a, b);
            cf
        }

        // Truth table for the 8th bit:
        // a b r c
        // 0 0 0 0
        // 0 0 1 0
        // 0 1 0 1
        // 0 1 1 0
        // 1 0 0 1
        // 1 0 1 0
        // 1 1 0 1
        // 1 1 1 1
        //
        // LLVM is super smart and turns this naive truth table encoding into 5 boolean ops:
        //
        // compute_cf_truth_table:
        // lea     eax, [rsi + rdi]
        // mov     ecx, esi
        // xor     cl, dil
        // not     al
        // and     al, cl
        // and     sil, dil
        // or      al, sil
        // shr     al, 7
        // ret
        pub fn compute_cf_truth_table(a: u8, b: u8) -> bool {
            let r = u8::wrapping_add(a, b);
            ((!a & b & !r) | (a & !b & !r) | (a & b & !r) | (a & b & r)) & 0x80 != 0
        }

        // LLVM output:
        //
        // compute_cf_formula:
        // lea     eax, [rsi + rdi]
        // mov     ecx, esi
        // or      cl, dil
        // not     al
        // and     al, cl
        // and     sil, dil
        // or      al, sil
        // shr     al, 7
        // ret
        pub fn compute_cf_formula(a: u8, b: u8) -> bool {
            let r = u8::wrapping_add(a, b);
            (((a | b) & !r) | (a & b)) & 0x80 != 0
        }

        for a in 0x00u8..=0xFFu8 {
            for b in 0x00u8..=0xFFu8 {
                let cf = compute_cf_correctly(a, b);
                let cf1 = compute_cf_truth_table(a, b);
                let cf2 = compute_cf_formula(a, b);
                assert_eq!(
                    cf, cf1,
                    "found disagreement for truth table {:#06b} {:#06b}",
                    a, b
                );
                assert_eq!(
                    cf, cf2,
                    "found disagreement for formula {:#06b} {:#06b}",
                    a, b
                );
            }
        }
    }
}
