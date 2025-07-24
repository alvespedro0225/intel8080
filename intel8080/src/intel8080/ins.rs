pub enum Instruction {
    NOP,
    LXI(u8),
    STAX(u8),
    INX(u8),
    INR(u8),
    DCR(u8),
    MVI(u8),
    DAD(u8),
    LDAX(u8),
    DCX(u8),
    RLC,
    RRC,
    RAL,
    RAR,
    SHLD,
    DAA,
    LHLD,
    CMA,
    STA,
    STC,
    LDA,
    CMC,
    MOV(u8, u8),
    HLT,
    ADD(u8),
    ADC(u8),
    SUB(u8),
    SBB(u8),
    ANA(u8),
    XRA(u8),
    ORA(u8),
    CMP(u8),
    RCC(u8),
    POP(u8),
    JCC(u8),
    CCC(u8),
    PUSH(u8),
    ADI,
    ACI,
    SUI,
    SBI,
    ANI,
    XRI,
    ORI,
    CPI,
    RST(u8),
    RET,
    CALL,
    JMP,
    OUT,
    IN,
    XTHL,
    PCHL,
    XCHG,
    DI,
    SPLH,
    EI,
}

impl From<u8> for Instruction {
    fn from(opcode: u8) -> Self {
        let instruction = match opcode {
            0x00 | 0x08 | 0x10 | 0x18 | 0x20 | 0x28 | 0x30 | 0x38 => Some(Instruction::NOP),
            0x15 => Some(Instruction::RRC),
            0x17 => Some(Instruction::RAL),
            0x1F => Some(Instruction::RAR),
            0x22 => Some(Instruction::SHLD),
            0x27 => Some(Instruction::DAA),
            0x2A => Some(Instruction::LHLD),
            0x2F => Some(Instruction::CMA),
            0x32 => Some(Instruction::STA),
            0x37 => Some(Instruction::STC),
            0x3A => Some(Instruction::LDA),
            0x3F => Some(Instruction::CMC),
            0x76 => Some(Instruction::HLT),
            0xC3 | 0xCB => Some(Instruction::JMP),
            0xC9 | 0xD9 => Some(Instruction::RET),
            0xCD | 0xDD | 0xED | 0xFD => Some(Instruction::CALL),
            0xC6 => Some(Instruction::ADI),
            0xCE => Some(Instruction::ACI),
            0xD6 => Some(Instruction::SUI),
            0xDE => Some(Instruction::SBI),
            0xE6 => Some(Instruction::ANI),
            0xEE => Some(Instruction::XRI),
            0xF6 => Some(Instruction::ORI),
            0xFE => Some(Instruction::CPI),
            0xD3 => Some(Instruction::OUT),
            0xD8 => Some(Instruction::IN),
            0xE3 => Some(Instruction::XTHL),
            0xE9 => Some(Instruction::PCHL),
            0xEB => Some(Instruction::XCHG),
            0xF9 => Some(Instruction::SPLH),
            0xF3 => Some(Instruction::DI),
            0xFB => Some(Instruction::EI),
            _ => None,
        };

        if let Some(ins) = instruction {
            return ins;
        }

        // RP
        let ins_var = (opcode & (0b11 << 4)) >> 4;

        let instruction = match opcode & !(0b11 << 4) {
            0x01 => Some(Instruction::LXI(ins_var)),
            0x03 => Some(Instruction::INX(ins_var)),
            0x09 => Some(Instruction::DAD(ins_var)),
            0x11 => Some(Instruction::DCX(ins_var)),
            0xC1 => Some(Instruction::POP(ins_var)),
            0xC5 => Some(Instruction::PUSH(ins_var)),
            _ => None
        };

        if let Some(ins) = instruction {
            return ins;
        }

        // DDD
        let ins_var = (opcode & (0b111 << 3)) >> 3;

        let instruction = match opcode & !(0b111 << 3) {
            0x04 => Some(Instruction::INR(ins_var)),
            0x05 => Some(Instruction::DCR(ins_var)),
            0x06 => Some(Instruction::MVI(ins_var)),
            0xC0 => Some(Instruction::RCC(ins_var)),
            0xC2 => Some(Instruction::JCC(ins_var)),
            0xC4 => Some(Instruction::CCC(ins_var)),
            0xC7 => Some(Instruction::RST(ins_var)),
            _ => None
        };
        
        if let Some(ins) = instruction {
            return ins;
        }
        
        let ins_var = opcode & 0b111;
        
        let instruction:Option<Instruction> = match opcode & !0b111 {
            0x80 => Some(Instruction::ADD(ins_var)),
            0x88 => Some(Instruction::ADC(ins_var)),
            0x90 => Some(Instruction::SUB(ins_var)),
            0x98 => Some(Instruction::SBB(ins_var)),
            0xA0 => Some(Instruction::ANA(ins_var)),
            0xA8 => Some(Instruction::XRA(ins_var)),
            0xB0 => Some(Instruction::ORA(ins_var)),
            0xB8 => Some(Instruction::CMP(ins_var)),
            _ => None
        };
        
        let ins_var = (opcode & (1 << 4)) >> 4;
        
        if let Some(ins) = instruction {
            return ins;
        }
        
        let instruction: Option<Instruction> = match opcode & !(1 <<4) {
            0x02 => Some(Instruction::STAX(ins_var)),
            0x0A => Some(Instruction::LDAX(ins_var)),
            _ => None
        };
        
        if let Some(ins) = instruction {
            return ins;
        }
        
        if opcode & !0b111111 == 0x40 {
            return Instruction::MOV((opcode & 0b111 << 3) >> 3, opcode & 0b111);
        }
        
        panic!("Unknown instruction: {opcode}")
    }
}
