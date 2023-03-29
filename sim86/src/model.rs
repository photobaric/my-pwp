use anyhow::ensure;

// Page 4-20, Table 4-9
#[repr(u8)]
#[derive(Debug, Copy, Clone)]
#[allow(dead_code)]
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
#[allow(dead_code)]
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
#[allow(dead_code)]
pub enum SegmentReg {
    ES = 0b00,
    CS = 0b01,
    SS = 0b10,
    DS = 0b11,
}

#[derive(Debug, Copy, Clone)]
pub enum Reg {
    ByteReg(ByteReg),
    WordReg(WordReg),
    SegmentReg(SegmentReg),
}

impl Reg {
    pub fn size(self) -> u8 {
        match self {
            Reg::ByteReg(_) => 1,
            Reg::WordReg(_) => 2,
            Reg::SegmentReg(_) => 2,
        }
    }
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

impl ::std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Reg::ByteReg(byte_reg) => write!(f, "{}", byte_reg),
            Reg::WordReg(word_reg) => write!(f, "{}", word_reg),
            Reg::SegmentReg(segment_reg) => write!(f, "{}", segment_reg),
        }
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

// TODO(photobaric): Should ModRM encode `is_word`?
// TODO(photobaric): Add layer of nesting to ModRM for Memory and see if it increases the size of the struct
// TODO(photobaric): Add `is_word` to ModRM and see if it increases the size of the struct
// TODO(photobaric): Const assert sizes

#[derive(Debug, Clone)]
pub enum MemoryOperand {
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

// 8086 Addressing Modes:
// This is organized in accordance to the taxonomy described in Section 2.8
// rather than the binary encoding of the instructions.
// This makes decoding a bit more complex but the data structure is closer to the mental model
// of the 8086 processor.
#[derive(Debug, Copy, Clone)]
pub enum ModRM {
    // MOD=11
    Reg(Reg),

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

pub struct CompleteModRM(pub ModRM, pub Option<SegmentReg>);

impl ::std::fmt::Display for CompleteModRM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn signed_displacement(displacement: u16) -> (char, i16) {
            let displacement: i16 = displacement as i16;
            if displacement < 0 {
                ('-', -displacement)
            } else {
                ('+', displacement)
            }
        }
        let CompleteModRM(rm, segment_override) = self;
        match (rm, segment_override) {
            (ModRM::Reg(_), Some(_)) => {}
            (_, Some(segment_register)) => {
                write!(f, "{}:", segment_register)?;
            }
            (_, None) => {}
        }
        match rm {
            ModRM::Reg(reg) => write!(f, "{}", reg),
            ModRM::DirectAddressing(direct_address) => write!(f, "[{}]", direct_address),
            ModRM::RegisterIndirectAddressingViaBaseReg(base_reg) => write!(f, "[{}]", base_reg),
            ModRM::RegisterIndirectAddressingViaIndexReg(index_reg) => write!(f, "[{}]", index_reg),
            ModRM::BasedAddressing(base_reg, displacement) => {
                let (sign, displacement) = signed_displacement(*displacement);
                write!(f, "[{} {} {}]", base_reg, sign, displacement)
            }
            ModRM::IndexedAddressing(index_reg, displacement) => {
                let (sign, displacement) = signed_displacement(*displacement);
                write!(f, "[{} {} {}]", index_reg, sign, displacement)
            }
            ModRM::BasedIndexedAddressing(base_reg, index_reg, displacement) => {
                let (sign, displacement) = signed_displacement(*displacement);
                write!(
                    f,
                    "[{} + {} {} {}]",
                    base_reg, index_reg, sign, displacement
                )
            }
            ModRM::BasedIndexedAddressingNoDisp(base_reg, index_reg) => {
                write!(f, "[{} + {}]", base_reg, index_reg)
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ByteOrWord {
    Byte(u8),
    Word(u16),
}

impl ::std::fmt::Display for ByteOrWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ByteOrWord::Byte(byte) => write!(f, "byte {}", byte),
            ByteOrWord::Word(word) => write!(f, "word {}", word),
        }
    }
}

pub struct NoPrefixByteOrWord(ByteOrWord);

impl ::std::fmt::Display for NoPrefixByteOrWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            ByteOrWord::Byte(byte) => write!(f, "{}", byte),
            ByteOrWord::Word(word) => write!(f, "{}", word),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Instruction {
    MovRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    MovImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    Push {
        rm: ModRM,
    },
    Pop {
        rm: ModRM,
    },
    Xchg {
        reg: Reg,
        rm: ModRM,
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
        reg: Reg,
        rm: ModRM,
    },
    Lds {
        reg: Reg,
        rm: ModRM,
    },
    Les {
        reg: Reg,
        rm: ModRM,
    },
    Lahf,
    Sahf,
    Pushf,
    Popf,

    AddRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    AddImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    AdcRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    AdcImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    Inc {
        is_word: bool,
        rm: ModRM,
    },
    Aaa,
    Daa,
    SubRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    SubImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    SbbRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    SbbImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    Dec {
        is_word: bool,
        rm: ModRM,
    },
    Neg {
        is_word: bool,
        rm: ModRM,
    },
    CmpRmWithReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    CmpImmediateWithRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    Aas,
    Das,
    Mul {
        is_word: bool,
        rm: ModRM,
    },
    Imul {
        is_word: bool,
        rm: ModRM,
    },
    Aam,
    Div {
        is_word: bool,
        rm: ModRM,
    },
    Idiv {
        is_word: bool,
        rm: ModRM,
    },
    Aad,
    Cbw,
    Cwd,

    Not {
        is_word: bool,
        rm: ModRM,
    },
    ShlSal {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    Shr {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    Sar {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    Rol {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    Ror {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    Rcl {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    Rcr {
        count: bool,
        is_word: bool,
        rm: ModRM,
    },
    AndRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    AndImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    TestRmWithReg {
        reg: Reg,
        rm: ModRM,
    },
    TestImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    OrRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    OrImmediateToRm {
        rm: ModRM,
        immediate: ByteOrWord,
    },
    XorRmToFromReg {
        is_reg_dst: bool,
        reg: Reg,
        rm: ModRM,
    },
    XorImmediateToRm {
        rm: ModRM,
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
        rm: ModRM,
    },
    CallDirectIntersegment {
        ip: u16,
        cs: u16,
    },
    CallIndirectIntersegment {
        rm: ModRM,
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
        rm: ModRM,
    },
    JmpDirectIntersegment {
        ip: u16,
        cs: u16,
    },
    JmpIndirectIntersegment {
        rm: ModRM,
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
    JbJnae {
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
    JnbJae {
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
        rm: ModRM,
    },
}

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

pub struct CompleteInstruction(pub Instruction, pub PrefixState);

impl ::std::fmt::Display for CompleteInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let CompleteInstruction(instruction, prefix_state) = self;
        macro_rules! display_jump {
            ($name:expr, $ip_inc8:ident, $size:literal) => {{
                // nasm wants the displacment to be from the beginning of the instruction
                // but in the machine code it's encoded from the end.
                // https://www.nasm.us/doc/nasmdoc3.html#section-3.5
                //
                // widen to i32 to fit `+ SIZE` and to fit the negated negative min
                let ip_inc8 = (*$ip_inc8 as i32) + $size;
                if ip_inc8 < 0 {
                    write!(f, "{} $-{}", $name, -ip_inc8)
                } else {
                    write!(f, "{} $+{}", $name, ip_inc8)
                }
            }};
        }
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
        macro_rules! rm {
            ($rm:ident) => {
                CompleteModRM(*$rm, segment_override)
            };
        }
        macro_rules! display_shift {
            ($name:literal, $count:ident, $is_word:ident, $rm:ident) => {{
                let count = if *$count { "cl" } else { "1" };
                match $rm {
                    ModRM::Reg(reg) => write!(f, "{} {}, {}", $name, reg, count),
                    _ => {
                        let byte_or_word = if *$is_word { "word" } else { "byte" };
                        write!(f, "{} {} {}, {}", $name, byte_or_word, rm!($rm), count)
                    }
                }
            }};
        }
        match instruction {
            Instruction::MovRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "mov {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "mov {}, {}", rm!(rm), reg)
                }
            }
            Instruction::MovImmediateToRm { rm, immediate } => match rm {
                // in case of a reg destination, the size of the immediate is already clear from the size of the reg
                ModRM::Reg(reg) => write!(f, "mov {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "mov {}, {}", rm!(rm), immediate),
            },
            Instruction::Push { rm } => match rm {
                ModRM::Reg(reg) => write!(f, "push {}", reg),
                // for some reason nasm wants "word" to be specified explicitly
                // even though Page 2-31 says that push always pushes words
                _ => write!(f, "push word {}", rm!(rm)),
            },
            Instruction::Pop { rm } => match rm {
                ModRM::Reg(reg) => write!(f, "pop {}", reg),
                // for some reason nasm wants "word" to be specified explicitly
                // even though Page 2-31 says that pop always pops words
                _ => write!(f, "pop word {}", rm!(rm)),
            },
            Instruction::Xchg { reg, rm } => {
                // work around nasm bug by making the memory operand the first argument
                // when there is a lock prefix:
                // https://bugzilla.nasm.us/show_bug.cgi?id=3392838#c2
                if prefix_state.get_lock() {
                    write!(f, "xchg {}, {}", rm!(rm), reg)
                } else {
                    // but in order to roundtrip with our test cases, reg should be otherwise be the first argument
                    // since a register-register xchg will encode the first register in reg and the second in rm
                    write!(f, "xchg {}, {}", reg, rm!(rm))
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
            Instruction::Lea { reg, rm } => write!(f, "lea {}, {}", reg, rm!(rm)),
            Instruction::Lds { reg, rm } => write!(f, "lds {}, {}", reg, rm!(rm)),
            Instruction::Les { reg, rm } => write!(f, "les {}, {}", reg, rm!(rm)),
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
                    write!(f, "add {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "add {}, {}", rm!(rm), reg)
                }
            }
            Instruction::AddImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "add {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "add {}, {}", rm!(rm), immediate),
            },
            Instruction::AdcRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "adc {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "adc {}, {}", rm!(rm), reg)
                }
            }
            Instruction::AdcImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "adc {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "adc {}, {}", rm!(rm), immediate),
            },
            Instruction::Inc { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "inc {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "inc {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::Aaa => write!(f, "aaa"),
            Instruction::Daa => write!(f, "daa"),
            Instruction::SubRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "sub {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "sub {}, {}", rm!(rm), reg)
                }
            }
            Instruction::SubImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "sub {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "sub {}, {}", rm!(rm), immediate),
            },
            Instruction::SbbRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "sbb {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "sbb {}, {}", rm!(rm), reg)
                }
            }
            Instruction::SbbImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "sbb {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "sbb {}, {}", rm!(rm), immediate),
            },
            Instruction::Dec { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "dec {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "dec {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::Neg { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "neg {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "neg {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::CmpRmWithReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "cmp {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "cmp {}, {}", rm!(rm), reg)
                }
            }
            Instruction::CmpImmediateWithRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "cmp {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "cmp {}, {}", rm!(rm), immediate),
            },
            Instruction::Aas => write!(f, "aas"),
            Instruction::Das => write!(f, "das"),
            Instruction::Mul { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "mul {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "mul {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::Imul { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "imul {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "imul {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::Aam => write!(f, "aam"),
            Instruction::Div { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "div {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "div {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::Idiv { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "idiv {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "idiv {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::Aad => write!(f, "aad"),
            Instruction::Cbw => write!(f, "cbw"),
            Instruction::Cwd => write!(f, "cwd"),

            Instruction::Not { is_word, rm } => match rm {
                ModRM::Reg(reg) => write!(f, "not {}", reg),
                _ => {
                    let byte_or_word = if *is_word { "word" } else { "byte" };
                    write!(f, "not {} {}", byte_or_word, rm!(rm))
                }
            },
            Instruction::ShlSal { count, is_word, rm } => {
                display_shift!("shl", count, is_word, rm)
            }
            Instruction::Shr { count, is_word, rm } => display_shift!("shr", count, is_word, rm),
            Instruction::Sar { count, is_word, rm } => display_shift!("sar", count, is_word, rm),
            Instruction::Rol { count, is_word, rm } => display_shift!("rol", count, is_word, rm),
            Instruction::Ror { count, is_word, rm } => display_shift!("ror", count, is_word, rm),
            Instruction::Rcl { count, is_word, rm } => display_shift!("rcl", count, is_word, rm),
            Instruction::Rcr { count, is_word, rm } => display_shift!("rcr", count, is_word, rm),
            Instruction::AndRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "and {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "and {}, {}", rm!(rm), reg)
                }
            }
            Instruction::AndImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "and {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "and {}, {}", rm!(rm), immediate),
            },
            Instruction::TestRmWithReg { reg, rm } => {
                // Seems that for `test` the r/m operand is typically written first:
                // - Page 4-31
                // - https://c9x.me/x86/html/file_module_x86_id_315.html
                write!(f, "test {}, {}", rm!(rm), reg)
            }
            Instruction::TestImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "test {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "test {}, {}", rm!(rm), immediate),
            },
            Instruction::OrRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "or {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "or {}, {}", rm!(rm), reg)
                }
            }
            Instruction::OrImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "or {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "or {}, {}", rm!(rm), immediate),
            },
            Instruction::XorRmToFromReg {
                is_reg_dst,
                reg,
                rm,
            } => {
                if *is_reg_dst {
                    write!(f, "xor {}, {}", reg, rm!(rm))
                } else {
                    write!(f, "xor {}, {}", rm!(rm), reg)
                }
            }
            Instruction::XorImmediateToRm { rm, immediate } => match rm {
                ModRM::Reg(reg) => write!(f, "xor {}, {}", reg, NoPrefixByteOrWord(*immediate)),
                _ => write!(f, "xor {}, {}", rm!(rm), immediate),
            },

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

            Instruction::CallDirect { ip_inc16 } => display_jump!("call", ip_inc16, 3),
            Instruction::CallIndirect { rm } => write!(f, "call {}", rm!(rm)),
            Instruction::CallDirectIntersegment { ip, cs } => write!(f, "call {}:{}", cs, ip),
            Instruction::CallIndirectIntersegment { rm } => write!(f, "call far {}", rm!(rm)),
            Instruction::JmpDirectShort { ip_inc8 } => display_jump!("jmp", ip_inc8, 2),
            Instruction::JmpDirect { ip_inc16 } => display_jump!("jmp", ip_inc16, 3),
            Instruction::JmpIndirect { rm } => write!(f, "jmp {}", rm!(rm)),
            Instruction::JmpDirectIntersegment { ip, cs } => write!(f, "jmp {}:{}", cs, ip),
            Instruction::JmpIndirectIntersegment { rm } => write!(f, "jmp far {}", rm!(rm)),
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

            Instruction::JneJnz { ip_inc8 } => display_jump!("jnz", ip_inc8, 2),
            Instruction::JeJz { ip_inc8 } => display_jump!("jz", ip_inc8, 2),
            Instruction::JlJnge { ip_inc8 } => display_jump!("jl", ip_inc8, 2),
            Instruction::JleJng { ip_inc8 } => display_jump!("jle", ip_inc8, 2),
            Instruction::JbJnae { ip_inc8 } => display_jump!("jb", ip_inc8, 2),
            Instruction::JbeJna { ip_inc8 } => display_jump!("jbe", ip_inc8, 2),
            Instruction::JpJpe { ip_inc8 } => display_jump!("jp", ip_inc8, 2),
            Instruction::Jo { ip_inc8 } => display_jump!("jo", ip_inc8, 2),
            Instruction::Js { ip_inc8 } => display_jump!("js", ip_inc8, 2),
            Instruction::JnlJge { ip_inc8 } => display_jump!("jge", ip_inc8, 2),
            Instruction::JnleJg { ip_inc8 } => display_jump!("jg", ip_inc8, 2),
            Instruction::JnbJae { ip_inc8 } => display_jump!("jae", ip_inc8, 2),
            Instruction::JnbeJa { ip_inc8 } => display_jump!("ja", ip_inc8, 2),
            Instruction::JnpJpo { ip_inc8 } => display_jump!("jpo", ip_inc8, 2),
            Instruction::Jno { ip_inc8 } => display_jump!("jno", ip_inc8, 2),
            Instruction::Jns { ip_inc8 } => display_jump!("jns", ip_inc8, 2),
            Instruction::Loop { ip_inc8 } => display_jump!("loop", ip_inc8, 2),
            Instruction::LoopeLoopz { ip_inc8 } => display_jump!("loopz", ip_inc8, 2),
            Instruction::LoopneLoopnz { ip_inc8 } => display_jump!("loopnz", ip_inc8, 2),
            Instruction::Jcxz { ip_inc8 } => display_jump!("jcxz", ip_inc8, 2),

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
            } => write!(f, "esc {}, {}", external_opcode, rm!(rm)),
        }
    }
}
