#![allow(clippy::unusual_byte_groupings)]

use anyhow::ensure;

// Page 4-20, Table 4-9
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum ByteReg {
    AL = 0b000,
    CL = 0b001,
    DL = 0b010,
    BL = 0b011,
    AH = 0b100,
    CH = 0b101,
    DH = 0b110,
    BH = 0b111,
}

// Page 4-20, Table 4-9
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum WordReg {
    AX = 0b000,
    CX = 0b001,
    DX = 0b010,
    BX = 0b011,
    SP = 0b100,
    BP = 0b101,
    SI = 0b110,
    DI = 0b111,
}

// Page 4-21, "Segment register code"
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum SegmentReg {
    ES = 0b00,
    CS = 0b01,
    SS = 0b10,
    DS = 0b11,
}

impl TryFrom<u8> for ByteReg {
    type Error = anyhow::Error;

    fn try_from(reg: u8) -> Result<Self, Self::Error> {
        ensure!(reg & 0b111 == reg);
        let byte_reg: ByteReg = unsafe { ::std::mem::transmute(reg) };
        Ok(byte_reg)
    }
}

impl TryFrom<u8> for WordReg {
    type Error = anyhow::Error;

    fn try_from(reg: u8) -> Result<Self, Self::Error> {
        ensure!(reg & 0b111 == reg);
        let word_reg: WordReg = unsafe { ::std::mem::transmute(reg) };
        Ok(word_reg)
    }
}

impl TryFrom<u8> for SegmentReg {
    type Error = anyhow::Error;

    fn try_from(reg: u8) -> Result<Self, Self::Error> {
        ensure!(reg & 0b11 == reg);
        let segment_reg: SegmentReg = unsafe { ::std::mem::transmute(reg) };
        Ok(segment_reg)
    }
}

pub const REG_TABLE_W0: &[&str; 8] = &["al", "cl", "dl", "bl", "ah", "ch", "dh", "bh"];
pub const REG_TABLE_W1: &[&str; 8] = &["ax", "cx", "dx", "bx", "sp", "bp", "si", "di"];
pub const SEGMENT_REG_TABLE: &[&str; 4] = &["es", "cs", "ss", "ds"];

impl ::std::fmt::Display for ByteReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = REG_TABLE_W0[*self as usize];
        write!(f, "{}", str)
    }
}

impl ::std::fmt::Display for WordReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = REG_TABLE_W1[*self as usize];
        write!(f, "{}", str)
    }
}

impl ::std::fmt::Display for SegmentReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = SEGMENT_REG_TABLE[*self as usize];
        write!(f, "{}", str)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BaseReg {
    BX = 0b011,
    BP = 0b101,
}

#[derive(Debug, Copy, Clone)]
pub enum IndexReg {
    SI = 0b110,
    DI = 0b111,
}

impl From<BaseReg> for WordReg {
    fn from(value: BaseReg) -> Self {
        unsafe { std::mem::transmute(value) }
    }
}

impl From<IndexReg> for WordReg {
    fn from(value: IndexReg) -> Self {
        unsafe { std::mem::transmute(value) }
    }
}

impl ::std::fmt::Display for BaseReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let word_reg: WordReg = (*self).into();
        write!(f, "{}", word_reg)
    }
}

impl ::std::fmt::Display for IndexReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let word_reg: WordReg = (*self).into();
        write!(f, "{}", word_reg)
    }
}

// NOTE(photobaric): Explicitly this only encodes general-purpose registers
#[derive(Debug, Copy, Clone)]
pub enum RegOperand {
    Reg8(ByteReg),
    Reg16(WordReg),
}
::static_assertions::assert_eq_size!(RegOperand, [u8; 2]);

#[derive(Debug, Copy, Clone)]
pub enum MemOperand {
    Mem8(MemAddressingMode),
    Mem16(MemAddressingMode),
}

// Nesting enums like this is still fairly memory-efficient:
// - https://adeschamps.github.io/enum-size
// - https://github.com/rust-lang/rust/pull/45225
#[derive(Debug, Copy, Clone)]
pub enum RegMemOperand {
    Reg(RegOperand),
    Mem(MemOperand),
}
::static_assertions::assert_eq_size!(RegMemOperand, [u8; 8]);

// 8086 Addressing Modes:
// This is organized in accordance to the taxonomy described in Section 2.8
// rather than the binary encoding of the instructions.
// This makes decoding a bit more complex but the data structure is closer to the mental model
// of the 8086 processor.
#[derive(Debug, Copy, Clone)]
pub enum MemAddressingMode {
    // MOD=00, RM=110
    // Page 2-69
    DirectAddressing(u16),

    // MOD=00, RM!=110
    // Page 2-69 thru Page 2-70
    RegisterIndirectAddressingViaBaseReg(BaseReg),
    RegisterIndirectAddressingViaIndexReg(IndexReg),

    // MOD=01 or MOD=10, RM=11x
    // Page 2-70
    // {BX,BP} + displacement (8 or 16 bit immediate)
    // Used for addressing a field in a struct
    BasedAddressing(BaseReg, u16),

    // MOD=01 or MOD=10, RM=10x
    // Page 2-70 thru Page-2-71
    // {SI,DI} + displacement (8 or 16 bit immediate)
    // Used for addressing an element of an array
    IndexedAddressing(IndexReg, u16),

    // MOD=01 or MOD=10, RM=0xx
    // Page 2-71
    // {BX,BP} + {SI,DI} + displacement (8 or 16 bit immediate)
    // Used for addressing an element of a stack array
    // (base is stack pointer, displacement is where in the stack, index is index into array),
    // or an element of an array inside a struct
    // (base is struct pointer, displacement is which field in the struct, index is index into array)
    BasedIndexedAddressing(BaseReg, IndexReg, u16),
    BasedIndexedAddressingNoDisp(BaseReg, IndexReg), // TODO(photobaric): What is the use case here?
}
::static_assertions::assert_eq_size!(MemAddressingMode, [u8; 6]);

impl ::std::fmt::Display for RegOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegOperand::Reg8(x) => write!(f, "{}", x),
            RegOperand::Reg16(x) => write!(f, "{}", x),
        }
    }
}

impl ::std::fmt::Display for MemOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemOperand::Mem8(x) => write!(f, "{}", x),
            MemOperand::Mem16(x) => write!(f, "{}", x),
        }
    }
}

impl ::std::fmt::Display for RegMemOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegMemOperand::Reg(x) => write!(f, "{}", x),
            RegMemOperand::Mem(x) => write!(f, "{}", x),
        }
    }
}

impl ::std::fmt::Display for MemAddressingMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn signed_displacement(displacement: u16) -> (char, i16) {
            let displacement: i16 = displacement as i16;
            if displacement < 0 {
                ('-', -displacement)
            } else {
                ('+', displacement)
            }
        }
        match self {
            MemAddressingMode::DirectAddressing(direct_address) => {
                write!(f, "[{}]", direct_address)
            }
            MemAddressingMode::RegisterIndirectAddressingViaBaseReg(base_reg) => {
                write!(f, "[{}]", base_reg)
            }
            MemAddressingMode::RegisterIndirectAddressingViaIndexReg(index_reg) => {
                write!(f, "[{}]", index_reg)
            }
            MemAddressingMode::BasedAddressing(base_reg, displacement) => {
                let (sign, displacement) = signed_displacement(*displacement);
                write!(f, "[{} {} {}]", base_reg, sign, displacement)
            }
            MemAddressingMode::IndexedAddressing(index_reg, displacement) => {
                let (sign, displacement) = signed_displacement(*displacement);
                write!(f, "[{} {} {}]", index_reg, sign, displacement)
            }
            MemAddressingMode::BasedIndexedAddressing(base_reg, index_reg, displacement) => {
                let (sign, displacement) = signed_displacement(*displacement);
                write!(
                    f,
                    "[{} + {} {} {}]",
                    base_reg, index_reg, sign, displacement
                )
            }
            MemAddressingMode::BasedIndexedAddressingNoDisp(base_reg, index_reg) => {
                write!(f, "[{} + {}]", base_reg, index_reg)
            }
        }
    }
}

pub struct PrefixedMemAddressingMode(pub MemAddressingMode, pub Option<SegmentReg>);

pub struct PrefixedRegMemOperand(pub RegMemOperand, pub Option<SegmentReg>);

impl ::std::fmt::Display for PrefixedMemAddressingMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let PrefixedMemAddressingMode(mem, segment_override) = self;
        match segment_override {
            Some(segment_register) => write!(f, "{}:{}", segment_register, mem),
            None => write!(f, "{}", mem),
        }
    }
}

impl ::std::fmt::Display for PrefixedRegMemOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let PrefixedRegMemOperand(rm, segment_override) = self;
        match rm {
            RegMemOperand::Reg(reg) => write!(f, "{}", reg),
            RegMemOperand::Mem(mem) => match segment_override {
                Some(segment_register) => write!(f, "{}:{}", segment_register, mem),
                None => write!(f, "{}", mem),
            },
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ByteOrWord {
    Byte(u8),
    Word(u16),
}

#[derive(Debug, Clone)]
pub enum Instruction {
    // TODO(photobaric): This type signature currently allows encoding mismatching reg and rm fields
    //  (e.g. 8-bit register and 16-bit rm). When we pattern match we get a bunch of unreachable branches.
    //  We can do better with a tigher encoding by bundling them together like `RegRm8 | RegRm16`
    //  instead of allowing each operand to vary their size independently.
    MovRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    MovImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    MovRmToFromSegmentReg {
        is_segment_reg_dst: bool,
        segment_reg: SegmentReg,
        rm: RegMemOperand,
    },
    Push {
        rm: RegMemOperand,
    },
    PushSegmentReg {
        segment_reg: SegmentReg,
    },
    Pop {
        rm: RegMemOperand,
    },
    PopSegmentReg {
        segment_reg: SegmentReg,
    },
    Xchg {
        reg: RegOperand,
        rm: RegMemOperand,
    },
    InFixed {
        is_word: bool,
        port: u8,
    },
    InVariable {
        is_word: bool,
    },
    OutFixed {
        is_word: bool,
        port: u8,
    },
    OutVariable {
        is_word: bool,
    },
    Xlat,
    Lea {
        reg: RegOperand,
        rm: RegMemOperand,
    },
    Lds {
        reg: RegOperand,
        rm: RegMemOperand,
    },
    Les {
        reg: RegOperand,
        rm: RegMemOperand,
    },
    Lahf,
    Sahf,
    Pushf,
    Popf,

    AddRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    AddImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    AdcRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    AdcImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    Inc {
        rm: RegMemOperand,
    },
    Aaa,
    Daa,
    SubRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    SubImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    SbbRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    SbbImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    Dec {
        rm: RegMemOperand,
    },
    Neg {
        rm: RegMemOperand,
    },
    CmpRmToReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    CmpImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    Aas,
    Das,
    Mul {
        rm: RegMemOperand,
    },
    Imul {
        rm: RegMemOperand,
    },
    Aam,
    Div {
        rm: RegMemOperand,
    },
    Idiv {
        rm: RegMemOperand,
    },
    Aad,
    Cbw,
    Cwd,

    Not {
        rm: RegMemOperand,
    },
    ShlSal {
        count: bool,
        rm: RegMemOperand,
    },
    Shr {
        count: bool,
        rm: RegMemOperand,
    },
    Sar {
        count: bool,
        rm: RegMemOperand,
    },
    Rol {
        count: bool,
        rm: RegMemOperand,
    },
    Ror {
        count: bool,
        rm: RegMemOperand,
    },
    Rcl {
        count: bool,
        rm: RegMemOperand,
    },
    Rcr {
        count: bool,
        rm: RegMemOperand,
    },
    AndRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    AndImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    TestRmWithReg {
        reg: RegOperand,
        rm: RegMemOperand,
    },
    TestImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    OrRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    OrImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },
    XorRmToFromReg {
        is_reg_dst: bool,
        reg: RegOperand,
        rm: RegMemOperand,
    },
    XorImmediateToRm {
        rm: RegMemOperand,
        immediate: ByteOrWord,
    },

    Movs {
        is_word: bool,
    },
    Cmps {
        is_word: bool,
    },
    Scas {
        is_word: bool,
    },
    Lods {
        is_word: bool,
    },
    Stos {
        is_word: bool,
    },

    CallDirect {
        ip_inc16: i16,
    },
    CallIndirect {
        rm: RegMemOperand,
    },
    CallDirectIntersegment {
        ip: u16,
        cs: u16,
    },
    CallIndirectIntersegment {
        rm: RegMemOperand,
    },

    // Separate case from JmpDirect because instruction size is different
    // and we need to account for NASM messing with our jump targets.
    JmpDirectShort {
        ip_inc8: i8,
    },
    JmpDirect {
        ip_inc16: i16,
    },
    JmpIndirect {
        rm: RegMemOperand,
    },
    JmpDirectIntersegment {
        ip: u16,
        cs: u16,
    },
    JmpIndirectIntersegment {
        rm: RegMemOperand,
    },

    Ret {
        sp_add: u16,
    },
    RetIntersegment {
        sp_add: u16,
    },

    JeJz {
        ip_inc8: i8,
    },
    JlJnge {
        ip_inc8: i8,
    },
    JleJng {
        ip_inc8: i8,
    },
    JbJnaeJc {
        ip_inc8: i8,
    },
    JbeJna {
        ip_inc8: i8,
    },
    JpJpe {
        ip_inc8: i8,
    },
    Jo {
        ip_inc8: i8,
    },
    Js {
        ip_inc8: i8,
    },
    // JNE and JNZ instructions are encoded the same way in x86 and x86_64 architectures.
    // Both instructions have the same opcode (0x75) and behave identically.
    // The only difference between them is the mnemonic used in assembly language to represent the instruction,
    // which is meant to improve readability and convey the intended purpose of the instruction to the programmer.
    // However, once the assembly code is compiled, both JNE and JNZ instructions result in the same machine code.
    JneJnz {
        ip_inc8: i8,
    },
    JnlJge {
        ip_inc8: i8,
    },
    JnleJg {
        ip_inc8: i8,
    },
    JnbJaeJnc {
        ip_inc8: i8,
    },
    JnbeJa {
        ip_inc8: i8,
    },
    JnpJpo {
        ip_inc8: i8,
    },
    Jno {
        ip_inc8: i8,
    },
    Jns {
        ip_inc8: i8,
    },
    Loop {
        ip_inc8: i8,
    },
    LoopeLoopz {
        ip_inc8: i8,
    },
    LoopneLoopnz {
        ip_inc8: i8,
    },
    Jcxz {
        ip_inc8: i8,
    },

    Int {
        interrupt_type: u8,
    },
    Int3,
    Into,
    Iret,

    Clc,
    Cmc,
    Stc,
    Cld,
    Std,
    Cli,
    Sti,
    Hlt,
    Wait,
    Esc {
        external_opcode: u8,
        rm: RegMemOperand,
    },
}
::static_assertions::assert_eq_size!(Instruction, [u8; 14]);

// top 2 bits are zero, next 3 bits for segment override prefix, next 2 bits for rep, last 1 bit for lock
#[derive(Debug, Clone, Copy, Default)]
pub struct PrefixState(u8);

impl PrefixState {
    pub fn activate_lock(self) -> Self {
        PrefixState(self.0 | 1)
    }

    // See Page 2-42:
    // z = 0 => REP, REPE, REPZ (repeat while ZF=1)
    // z = 1 => REPNE, REPNZ (repeat while ZF=0)
    pub fn activate_rep(self, z: bool) -> Self {
        let z: u8 = z.into();
        PrefixState(self.0 | 0b100 | (z << 1))
    }

    pub fn activate_segment_override_prefix(self, segment_reg: SegmentReg) -> Self {
        let segment_reg: u8 = segment_reg as u8;
        PrefixState(self.0 | 0b00_100_000 | (segment_reg << 3))
    }

    pub fn get_lock(self) -> bool {
        self.0 & 1 == 1
    }

    pub fn get_rep(self) -> Option<bool> {
        if self.0 & 0b100 == 0 {
            None
        } else {
            Some(self.0 & 0b10 != 0)
        }
    }

    pub fn get_segment_override(self) -> Option<SegmentReg> {
        if self.0 & 0b00_100_000 == 0 {
            None
        } else {
            Some(SegmentReg::try_from((self.0 & 0b00_011_000) >> 3).unwrap())
        }
    }
}

pub struct PrefixedInstruction(pub Instruction, pub PrefixState);
static_assertions::assert_eq_size!(PrefixedInstruction, [u8; 16]);

impl ::std::fmt::Display for PrefixedInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let PrefixedInstruction(instruction, prefix_state) = self;
        if prefix_state.get_lock() {
            write!(f, "lock ")?;
        }
        match prefix_state.get_rep() {
            Some(true) => {
                write!(f, "repz ")?;
            }
            Some(false) => {
                write!(f, "repnz ")?;
            }
            None => {}
        }
        let segment_override = prefix_state.get_segment_override();

        // just some sugar to denoise the usage sites
        let prm = |rm: &RegMemOperand| PrefixedRegMemOperand(*rm, segment_override);
        let pmem = |mem: &MemAddressingMode| PrefixedMemAddressingMode(*mem, segment_override);

        let display_immediate_to_rm =
            |f: &mut std::fmt::Formatter<'_>,
             name: &str,
             rm: &RegMemOperand,
             immediate: &ByteOrWord| {
                match (rm, immediate) {
                    // in case of a reg destination, the size of the immediate is already clear from the size of the reg
                    (RegMemOperand::Reg(RegOperand::Reg8(reg)), ByteOrWord::Byte(immediate)) => {
                        write!(f, "{} {}, {}", name, reg, immediate)
                    }
                    (RegMemOperand::Reg(RegOperand::Reg16(reg)), ByteOrWord::Word(immediate)) => {
                        write!(f, "{} {}, {}", name, reg, immediate)
                    }

                    (RegMemOperand::Mem(MemOperand::Mem8(mem)), ByteOrWord::Byte(immediate)) => {
                        write!(f, "{} {}, byte {}", name, pmem(mem), immediate)
                    }
                    (RegMemOperand::Mem(MemOperand::Mem16(mem)), ByteOrWord::Word(immediate)) => {
                        write!(f, "{} {}, word {}", name, pmem(mem), immediate)
                    }

                    (RegMemOperand::Reg(RegOperand::Reg8(_)), ByteOrWord::Word(_)) => {
                        unreachable!()
                    }
                    (RegMemOperand::Reg(RegOperand::Reg16(_)), ByteOrWord::Byte(_)) => {
                        unreachable!()
                    }
                    (RegMemOperand::Mem(MemOperand::Mem8(_)), ByteOrWord::Word(_)) => {
                        unreachable!()
                    }
                    (RegMemOperand::Mem(MemOperand::Mem16(_)), ByteOrWord::Byte(_)) => {
                        unreachable!()
                    }
                }
            };

        let display_unary_rm =
            |f: &mut std::fmt::Formatter<'_>, name: &str, rm: &RegMemOperand| match rm {
                RegMemOperand::Reg(reg) => write!(f, "{} {}", name, reg),
                RegMemOperand::Mem(MemOperand::Mem8(mem)) => {
                    write!(f, "{} byte {}", name, pmem(mem))
                }
                RegMemOperand::Mem(MemOperand::Mem16(mem)) => {
                    write!(f, "{} word {}", name, pmem(mem))
                }
            };

        let display_shift =
            |f: &mut std::fmt::Formatter<'_>, name: &str, count: &bool, rm: &RegMemOperand| {
                let count = if *count { "cl" } else { "1" };
                match rm {
                    RegMemOperand::Reg(reg) => write!(f, "{} {}, {}", name, reg, count),
                    RegMemOperand::Mem(MemOperand::Mem8(mem)) => {
                        write!(f, "{} byte {}, {}", name, pmem(mem), count)
                    }
                    RegMemOperand::Mem(MemOperand::Mem16(mem)) => {
                        write!(f, "{} word {}, {}", name, pmem(mem), count)
                    }
                }
            };

        let display_jump =
            |f: &mut std::fmt::Formatter<'_>, name: &str, ip_inc8: &i8, size: i16| {
                // nasm wants the displacment to be from the beginning of the instruction
                // but in the machine code it's encoded from the end.
                // https://www.nasm.us/doc/nasmdoc3.html#section-3.5
                //
                // widen to i32 to fit `+ SIZE` and to fit the negated negative min
                let ip_inc8 = (*ip_inc8 as i16) + size;
                if ip_inc8 < 0 {
                    write!(f, "{} $-{}", name, -ip_inc8)
                } else {
                    write!(f, "{} $+{}", name, ip_inc8)
                }
            };
        let display_jump_16 =
            |f: &mut std::fmt::Formatter<'_>, name: &str, ip_inc16: &i16, size: i32| {
                // nasm wants the displacment to be from the beginning of the instruction
                // but in the machine code it's encoded from the end.
                // https://www.nasm.us/doc/nasmdoc3.html#section-3.5
                //
                // widen to i32 to fit `+ SIZE` and to fit the negated negative min
                let ip_inc8 = (*ip_inc16 as i32) + size;
                if ip_inc8 < 0 {
                    write!(f, "{} $-{}", name, -ip_inc8)
                } else {
                    write!(f, "{} $+{}", name, ip_inc8)
                }
            };

        match instruction {
            Instruction::MovRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "mov {}, {}", reg, prm(rm))
                } else {
                    write!(f, "mov {}, {}", prm(rm), reg)
                }
            }
            Instruction::MovImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "mov", rm, immediate)
            }
            Instruction::MovRmToFromSegmentReg {
                is_segment_reg_dst,
                segment_reg,
                rm,
            } => {
                if *is_segment_reg_dst {
                    write!(f, "mov {}, {}", segment_reg, prm(rm))
                } else {
                    write!(f, "mov {}, {}", prm(rm), segment_reg)
                }
            }
            Instruction::Push { rm } => display_unary_rm(f, "push", rm),
            Instruction::PushSegmentReg { segment_reg } => write!(f, "push {}", segment_reg),
            Instruction::Pop { rm } => display_unary_rm(f, "pop", rm),
            Instruction::PopSegmentReg { segment_reg } => write!(f, "pop {}", segment_reg),
            Instruction::Xchg { reg, rm } => {
                // work around nasm bug by making the memory operand the first argument
                // when there is a lock prefix:
                // https://bugzilla.nasm.us/show_bug.cgi?id=3392838#c2
                if prefix_state.get_lock() {
                    write!(f, "xchg {}, {}", prm(rm), reg)
                } else {
                    // but in order to roundtrip with our test cases, reg should be otherwise be the first argument
                    // since a register-register xchg will encode the first register in reg and the second in rm
                    write!(f, "xchg {}, {}", reg, prm(rm))
                }
            }
            Instruction::InFixed { is_word, port } => {
                let reg = if *is_word { "ax" } else { "al" };
                write!(f, "in {}, {}", reg, port)
            }
            Instruction::InVariable { is_word } => {
                let reg = if *is_word { "ax" } else { "al" };
                write!(f, "in {}, dx", reg)
            }
            Instruction::OutFixed { is_word, port } => {
                let reg = if *is_word { "ax" } else { "al" };
                write!(f, "out {}, {}", port, reg)
            }
            Instruction::OutVariable { is_word } => {
                let reg = if *is_word { "ax" } else { "al" };
                write!(f, "out dx, {}", reg)
            }
            Instruction::Xlat => {
                write!(f, "xlat")
            }
            Instruction::Lea { reg, rm } => write!(f, "lea {}, {}", reg, prm(rm)),
            Instruction::Lds { reg, rm } => write!(f, "lds {}, {}", reg, prm(rm)),
            Instruction::Les { reg, rm } => write!(f, "les {}, {}", reg, prm(rm)),
            Instruction::Lahf => write!(f, "lahf"),
            Instruction::Sahf => write!(f, "sahf"),
            Instruction::Pushf => write!(f, "pushf"),
            Instruction::Popf => write!(f, "popf"),

            Instruction::AddRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "add {}, {}", reg, prm(rm))
                } else {
                    write!(f, "add {}, {}", prm(rm), reg)
                }
            }
            Instruction::AddImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "add", rm, immediate)
            }
            Instruction::AdcRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "adc {}, {}", reg, prm(rm))
                } else {
                    write!(f, "adc {}, {}", prm(rm), reg)
                }
            }
            Instruction::AdcImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "adc", rm, immediate)
            }
            Instruction::Inc { rm } => display_unary_rm(f, "inc", rm),
            Instruction::Aaa => write!(f, "aaa"),
            Instruction::Daa => write!(f, "daa"),
            Instruction::SubRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "sub {}, {}", reg, prm(rm))
                } else {
                    write!(f, "sub {}, {}", prm(rm), reg)
                }
            }
            Instruction::SubImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "sub", rm, immediate)
            }
            Instruction::SbbRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "sbb {}, {}", reg, prm(rm))
                } else {
                    write!(f, "sbb {}, {}", prm(rm), reg)
                }
            }
            Instruction::SbbImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "sbb", rm, immediate)
            }
            Instruction::Dec { rm } => display_unary_rm(f, "dec", rm),
            Instruction::Neg { rm } => display_unary_rm(f, "neg", rm),
            Instruction::CmpRmToReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "cmp {}, {}", reg, prm(rm))
                } else {
                    write!(f, "cmp {}, {}", prm(rm), reg)
                }
            }
            Instruction::CmpImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "cmp", rm, immediate)
            }
            Instruction::Aas => write!(f, "aas"),
            Instruction::Das => write!(f, "das"),
            Instruction::Mul { rm } => display_unary_rm(f, "mul", rm),
            Instruction::Imul { rm } => display_unary_rm(f, "imul", rm),
            Instruction::Aam => write!(f, "aam"),
            Instruction::Div { rm } => display_unary_rm(f, "div", rm),
            Instruction::Idiv { rm } => display_unary_rm(f, "idiv", rm),
            Instruction::Aad => write!(f, "aad"),
            Instruction::Cbw => write!(f, "cbw"),
            Instruction::Cwd => write!(f, "cwd"),

            Instruction::Not { rm } => display_unary_rm(f, "not", rm),
            Instruction::ShlSal { count, rm } => display_shift(f, "shl", count, rm),
            Instruction::Shr { count, rm } => display_shift(f, "shr", count, rm),
            Instruction::Sar { count, rm } => display_shift(f, "sar", count, rm),
            Instruction::Rol { count, rm } => display_shift(f, "rol", count, rm),
            Instruction::Ror { count, rm } => display_shift(f, "ror", count, rm),
            Instruction::Rcl { count, rm } => display_shift(f, "rcl", count, rm),
            Instruction::Rcr { count, rm } => display_shift(f, "rcr", count, rm),
            Instruction::AndRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "and {}, {}", reg, prm(rm))
                } else {
                    write!(f, "and {}, {}", prm(rm), reg)
                }
            }
            Instruction::AndImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "and", rm, immediate)
            }
            Instruction::TestRmWithReg { reg, rm } => {
                // Seems that for `test` the r/m operand is typically written first:
                // - Page 4-31
                // - https://c9x.me/x86/html/file_module_x86_id_315.html
                write!(f, "test {}, {}", prm(rm), reg)
            }
            Instruction::TestImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "test", rm, immediate)
            }
            Instruction::OrRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "or {}, {}", reg, prm(rm))
                } else {
                    write!(f, "or {}, {}", prm(rm), reg)
                }
            }
            Instruction::OrImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "or", rm, immediate)
            }
            Instruction::XorRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "xor {}, {}", reg, prm(rm))
                } else {
                    write!(f, "xor {}, {}", prm(rm), reg)
                }
            }
            Instruction::XorImmediateToRm { rm, immediate } => {
                display_immediate_to_rm(f, "xor", rm, immediate)
            }

            Instruction::Movs { is_word } => {
                write!(f, "{}", if *is_word { "movsw" } else { "movsb" })
            }
            Instruction::Cmps { is_word } => {
                write!(f, "{}", if *is_word { "cmpsw" } else { "cmpsb" })
            }
            Instruction::Scas { is_word } => {
                write!(f, "{}", if *is_word { "scasw" } else { "scasb" })
            }
            Instruction::Lods { is_word } => {
                write!(f, "{}", if *is_word { "lodsw" } else { "lodsb" })
            }
            Instruction::Stos { is_word } => {
                write!(f, "{}", if *is_word { "stosw" } else { "stosb" })
            }

            Instruction::CallDirect { ip_inc16 } => display_jump_16(f, "call", ip_inc16, 3),
            Instruction::CallIndirect { rm } => write!(f, "call {}", prm(rm)),
            Instruction::CallDirectIntersegment { ip, cs } => write!(f, "call {}:{}", cs, ip),
            Instruction::CallIndirectIntersegment { rm } => write!(f, "call far {}", prm(rm)),
            Instruction::JmpDirectShort { ip_inc8 } => display_jump(f, "jmp", ip_inc8, 2),
            Instruction::JmpDirect { ip_inc16 } => display_jump_16(f, "jmp", ip_inc16, 3),
            Instruction::JmpIndirect { rm } => write!(f, "jmp {}", prm(rm)),
            Instruction::JmpDirectIntersegment { ip, cs } => write!(f, "jmp {}:{}", cs, ip),
            Instruction::JmpIndirectIntersegment { rm } => write!(f, "jmp far {}", prm(rm)),
            Instruction::Ret { sp_add } => {
                if *sp_add == 0 {
                    write!(f, "ret")
                } else {
                    write!(f, "ret {}", sp_add)
                }
            }
            Instruction::RetIntersegment { sp_add } => {
                if *sp_add == 0 {
                    write!(f, "retf")
                } else {
                    write!(f, "retf {}", sp_add)
                }
            }

            Instruction::JneJnz { ip_inc8 } => display_jump(f, "jnz", ip_inc8, 2),
            Instruction::JeJz { ip_inc8 } => display_jump(f, "jz", ip_inc8, 2),
            Instruction::JlJnge { ip_inc8 } => display_jump(f, "jl", ip_inc8, 2),
            Instruction::JleJng { ip_inc8 } => display_jump(f, "jle", ip_inc8, 2),
            Instruction::JbJnaeJc { ip_inc8 } => display_jump(f, "jb", ip_inc8, 2),
            Instruction::JbeJna { ip_inc8 } => display_jump(f, "jbe", ip_inc8, 2),
            Instruction::JpJpe { ip_inc8 } => display_jump(f, "jp", ip_inc8, 2),
            Instruction::Jo { ip_inc8 } => display_jump(f, "jo", ip_inc8, 2),
            Instruction::Js { ip_inc8 } => display_jump(f, "js", ip_inc8, 2),
            Instruction::JnlJge { ip_inc8 } => display_jump(f, "jge", ip_inc8, 2),
            Instruction::JnleJg { ip_inc8 } => display_jump(f, "jg", ip_inc8, 2),
            Instruction::JnbJaeJnc { ip_inc8 } => display_jump(f, "jae", ip_inc8, 2),
            Instruction::JnbeJa { ip_inc8 } => display_jump(f, "ja", ip_inc8, 2),
            Instruction::JnpJpo { ip_inc8 } => display_jump(f, "jpo", ip_inc8, 2),
            Instruction::Jno { ip_inc8 } => display_jump(f, "jno", ip_inc8, 2),
            Instruction::Jns { ip_inc8 } => display_jump(f, "jns", ip_inc8, 2),
            Instruction::Loop { ip_inc8 } => display_jump(f, "loop", ip_inc8, 2),
            Instruction::LoopeLoopz { ip_inc8 } => display_jump(f, "loopz", ip_inc8, 2),
            Instruction::LoopneLoopnz { ip_inc8 } => display_jump(f, "loopnz", ip_inc8, 2),
            Instruction::Jcxz { ip_inc8 } => display_jump(f, "jcxz", ip_inc8, 2),

            Instruction::Int { interrupt_type } => write!(f, "int {}", interrupt_type),
            Instruction::Int3 => write!(f, "int3"),
            Instruction::Into => write!(f, "into"),
            Instruction::Iret => write!(f, "iret"),
            Instruction::Clc => write!(f, "clc"),
            Instruction::Cmc => write!(f, "cmc"),
            Instruction::Stc => write!(f, "stc"),
            Instruction::Cld => write!(f, "cld"),
            Instruction::Std => write!(f, "std"),
            Instruction::Cli => write!(f, "cli"),
            Instruction::Sti => write!(f, "sti"),
            Instruction::Hlt => write!(f, "hlt"),
            Instruction::Wait => write!(f, "wait"),
            Instruction::Esc {
                external_opcode,
                rm,
            } => write!(f, "esc {}, {}", external_opcode, prm(rm)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn print_sizes() {
        fn print_size<T>() {
            println!(
                "{} - size {} align {}",
                ::std::any::type_name::<T>(),
                ::std::mem::size_of::<T>(),
                ::std::mem::align_of::<T>()
            );
        }
        print_size::<RegOperand>();
        print_size::<MemAddressingMode>();
        print_size::<RegMemOperand>();
        print_size::<Instruction>();
    }
}
