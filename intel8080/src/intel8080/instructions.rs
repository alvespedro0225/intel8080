use crate::intel8080::hardware::{Intel8080, Register, RegisterPair, StatusFlags};

// https://en.wikipedia.org/wiki/Intel_8080#Instruction_set Instruction reference
// https://altairclone.com/downloads/manuals/8080%20Programmers%20Manual.pdf 8080 manual
// https://svofski.github.io/pretty-8080-assembler/ assembler
pub fn handle_instruction(instruction: u8, intel8080: &mut Intel8080) {
    match instruction {
        0 => return,
        // 0b00RP0001
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 1 => {
            lxi_rp_data(instruction, intel8080);
            intel8080.program_counter += 2;
        }
        // 0b00RP0010
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 2 => {
            stax_rp(instruction, intel8080);
        }
        // 0b00RP0011
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 3 => {
            inx_rp(instruction, intel8080);
        }
        // 0b00DDD100
        _ if InstructionVars::negate(instruction, InstructionVars::DDD) == 4 => {
            inr_ddd(instruction, intel8080);
        }
        // 0b00DDD101
        _ if InstructionVars::negate(instruction, InstructionVars::DDD) == 5 => {
            dcr_ddd(instruction, intel8080);
        }
        // 0b00DDD110
        _ if InstructionVars::negate(instruction, InstructionVars::DDD) == 6 => {
            mvi_ddd_data(instruction, intel8080);
            intel8080.program_counter += 1;
        }
        // 0b00RP1001
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 9 => {
            dad_rp(instruction, intel8080);
        }
        // 0b00RP1010
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 10 => {
            ldax_rp(instruction, intel8080);
        }
        // 0b00RP1011
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 11 => {
            dcx_rp(instruction, intel8080);
        }
        // 0b00000111
        _ if instruction == 7 => {
            rlc(intel8080);
        }
        // 0b00001111
        _ if instruction == 15 => {
            rrc(intel8080);
        }
        // 0b00010111
        _ if instruction == 0x17 => {
            ral(intel8080);
        }
        // 0b00011111
        _ if instruction == 0x1F => {
            rar(intel8080);
        }
        // 0b00100010
        _ if instruction == 0x22 => {
            shld(intel8080);
            intel8080.program_counter += 2;
        }
        // 0b00100111
        _ if instruction == 0x27 => {
            daa(intel8080);
        }
        // 0b00101010
        _ if instruction == 0x2A => {
            lhld(intel8080);
            intel8080.program_counter += 2;
        }
        // 0b00101111
        _ if instruction == 0x2F => {
            cma(intel8080);
        }
        // 0b00110010
        _ if instruction == 0x32 => {
            sta(intel8080);
            intel8080.program_counter += 2;
        }
        // 0b00110111
        _ if instruction == 0x37 => {
            stc(intel8080);
        }
        // 0b00111010
        _ if instruction == 0x3A => {
            lda(intel8080);
        }
        // 0b00111111
        _ if instruction == 0x3F => {
            cmc(intel8080);
        } 
        _ => {}
    }
    intel8080.program_counter += 1;
}

// Manual page 25, PDF's 31
// Uses the next 2 instruction bytes as data and sets RP to it.
fn lxi_rp_data(instruction: u8, intel8080: &mut Intel8080) {
    let rp_value = combine_next_instructions(intel8080) as u16;
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let rp = RegisterPair::get_rp(rp);
    intel8080.set_register_pair(rp, rp_value);
}
// Manual page 17, PDF's 23
// Store Accumulator. memory[RP] = A
fn stax_rp(instruction: u8, intel8080: &mut Intel8080) {
    let reg_a = intel8080.get_register(&Register::A);
    let rp = InstructionVars::get(instruction, InstructionVars::RP);

    if rp > 1 {
        panic!("Invalid RP value for instruction stax {rp}")
    }

    let rp = RegisterPair::get_rp(rp);
    let index = intel8080.get_register_pair(&rp) as usize;
    intel8080.memory[index] = reg_a;
}
// Manal page 24, PDF's 30
// Increases RP by 1. RP += 1
fn inx_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let rp = RegisterPair::get_rp(rp);
    let rp_value = intel8080.get_register_pair(&rp);
    intel8080.set_register_pair(rp, u16::wrapping_add(rp_value, 1));
}
// Manual page 15, PDF's 21
// Increment register or memory. DDD += 1
fn inr_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = InstructionVars::get(instruction, InstructionVars::DDD);
    let register = Register::get_ddd(ddd);
    let register_value = intel8080.get_register(&register);
    let (new_value, _) = u8::overflowing_add(register_value, 1);
    intel8080.set_register(register, new_value);
    intel8080.set_status_add(register_value, 1);
}
// Manual page 15, PDF's 21
// Decrement register or memory. DDD -= 1
fn dcr_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = InstructionVars::get(instruction, InstructionVars::DDD);
    let register = Register::get_ddd(ddd);
    let register_value = intel8080.get_register(&register);
    let (new_value, _) = u8::overflowing_sub(register_value, 1);
    intel8080.set_register(register, new_value);
    intel8080.set_status_sub(register_value, 1);
}
// Manual page 26, PDF's 32
// Move immediate data. DDD = Data
fn mvi_ddd_data(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = InstructionVars::get(instruction, InstructionVars::DDD);
    let ddd = Register::get_ddd(ddd);
    let data = intel8080.memory[(intel8080.program_counter + 1) as usize];
    intel8080.set_register(ddd, data);
}
// Manual page 24, PDF's 30
// Double add. HL += RP
fn dad_rp(instruction: u8, intel8080: &mut Intel8080) {
    let hl = intel8080.get_register_pair(&RegisterPair::HL);
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let rp = RegisterPair::get_rp(rp);

    let (sum, of) = if let RegisterPair::HL = rp {
        (hl << 1, hl >= 32768) // hl >= 32768 checks if msb is set
    } else {
        let rp = intel8080.get_register_pair(&rp);
        u16::overflowing_add(rp, hl)
    };

    intel8080.set_flag(StatusFlags::C, of);
    intel8080.set_register_pair(RegisterPair::HL, sum);
}
// Manual page 17, PDF's 23
// Load Accumulator. A = memory[RP]
fn ldax_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = InstructionVars::get(instruction, InstructionVars::RP);

    if rp > 1 {
        panic!("Invalid RP value for instruction ldax {rp}")
    }

    let rp = RegisterPair::get_rp(rp);
    let rp = intel8080.get_register_pair(&rp);
    intel8080.set_register(Register::A, intel8080.memory[rp as usize]);
}
// Manual page 24, PDF's 30
// Decrement Register Pair. RP -= 1
fn dcx_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let rp = RegisterPair::get_rp(rp);
    let rp_value = intel8080.get_register_pair(&rp);
    intel8080.set_register_pair(rp, u16::wrapping_sub(rp_value, 1));
}
// Manual page 21, PDF's 27
// Rotate Accumulator Left
fn rlc(intel8080: &mut Intel8080) {
    let accumulator = intel8080.get_register(&Register::A);
    let carry = accumulator >> 7 == 1;
    intel8080.set_flag(StatusFlags::C, carry);
    intel8080.set_register(Register::A, accumulator.rotate_left(1))
}
// Manual page 21, PDF's 27
// Rotate Accumulator Right
fn rrc(intel8080: &mut Intel8080) {
    let accumulator = intel8080.get_register(&Register::A);
    let carry = (accumulator & 1) == 1;
    intel8080.set_flag(StatusFlags::C, carry);
    intel8080.set_register(Register::A, accumulator.rotate_right(1));
}
// Manual page 22, PDF's 28
// Rotate Accumulator Left Through Carry
fn ral(intel8080: &mut Intel8080) {
    let mut accumulator = intel8080.get_register(&Register::A);
    let carry = if intel8080.get_flag(StatusFlags::C) {
        1
    } else {
        0
    };
    let new_carry = accumulator >> 7 == 1;
    intel8080.set_flag(StatusFlags::C, new_carry);
    accumulator <<= 1;
    accumulator ^= carry;
    intel8080.set_register(Register::A, accumulator);
}
// Manual page 22, PDF's 28
// Rotate Accumulator Right Through Carry
fn rar(intel8080: &mut Intel8080) {
    let mut accumulator = intel8080.get_register(&Register::A);
    let carry = if intel8080.get_flag(StatusFlags::C) {
        1
    } else {
        0
    };
    let new_carry = accumulator & 1 == 1;
    intel8080.set_flag(StatusFlags::C, new_carry);
    accumulator >>= 1;
    accumulator ^= carry << 7;
    intel8080.set_register(Register::A, accumulator);
}
// Manual page 30, PDF's 36
// Store H and L Directly
fn shld(intel8080: &mut Intel8080) {
    let index = combine_next_instructions(intel8080) as usize;
    intel8080.memory[index] = intel8080.get_register(&Register::L);
    intel8080.memory[index + 1] = intel8080.get_register(&Register::H);
}
// Manual page 15, PDF's 21
// Decimal Adjust Accumulator
fn daa(intel8080: &mut Intel8080) {
    let mut accumulator = intel8080.get_register(&Register::A);
    let right = accumulator & 0xF;

    if right > 9 {
        accumulator += 6;
        intel8080.set_flag(StatusFlags::AC, true);
    } else if intel8080.get_flag(StatusFlags::AC) {
        accumulator += 6;
        intel8080.set_flag(StatusFlags::AC, false);
    }

    let left = (accumulator & 0xF0) >> 4;

    if left > 9 {
        accumulator = u8::wrapping_add(accumulator, 6 << 4);
        intel8080.set_flag(StatusFlags::C, true);
    } else if intel8080.get_flag(StatusFlags::C) {
        accumulator += 6 << 4;
        intel8080.set_flag(StatusFlags::C, false);
    }

    intel8080.set_register(Register::A, accumulator);
    intel8080.set_parity(accumulator);
    intel8080.set_zero_or_less(accumulator);
}
// Manual page 31, PDF's 37
// Load H And L Direct
fn lhld(intel8080: &mut Intel8080) {
    let index = combine_next_instructions(intel8080) as usize;
    intel8080.set_register(Register::L, intel8080.memory[index]);
    intel8080.set_register(Register::H, intel8080.memory[index + 1]);
}
// Manual page 15, PDF's 21
// Complement Accumulator
fn cma(intel8080: &mut Intel8080) {
    let accumulator = intel8080.get_register(&Register::A);
    intel8080.set_register(Register::A, !accumulator);
}
// Manual page 30, PDF's 36
// Store Accumulator Direct
fn sta(intel8080: &mut Intel8080) {
    let index = combine_next_instructions(intel8080) as usize;
    intel8080.memory[index] = intel8080.get_register(&Register::A);
}
// Manual page 14, PDF's 20
// Set Carry
fn stc(intel8080: &mut Intel8080) {
    intel8080.set_flag(StatusFlags::C, true);
}
// Manual page 30, PDF's 36
// Load Accumulator Direct
fn lda(intel8080: &mut Intel8080) {
    let index = combine_next_instructions(intel8080) as usize;
    let value = intel8080.memory[index];
    intel8080.set_register(Register::A, value);
}
// Manual page 14, PDF's 20
// Complement Carry
fn cmc(intel8080: &mut Intel8080){
    let carry = intel8080.get_flag(StatusFlags::C);
    intel8080.set_flag(StatusFlags::C, !carry);
}
fn combine_next_instructions(intel8080: &mut Intel8080) -> u16 {
    let pc = intel8080.program_counter as usize;
    let (second, third) = (intel8080.memory[pc + 1], intel8080.memory[pc + 2]);
    let second = second as u16;
    let third = third as u16;
    let mut value = third << 8;
    value ^= second;
    value
}
/// Combines two 8 bits memory addresses into one 16 bits address. The third bit is the msb.
enum InstructionVars {
    RP,
    CC,
    DDD,
    ALU,
    N,
    SSS,
}

impl InstructionVars {
    fn negate(instruction: u8, var: InstructionVars) -> u8 {
        let neg = match var {
            InstructionVars::RP | InstructionVars::CC => !(0b11 << 4),
            InstructionVars::DDD | InstructionVars::ALU | InstructionVars::N => !(0b111 << 3),
            InstructionVars::SSS => !0b111,
        };
        instruction & neg
    }

    fn get(instruction: u8, var: InstructionVars) -> u8 {
        let shift;
        let neg = match var {
            InstructionVars::RP | InstructionVars::CC => {
                shift = 4;
                0b11 << shift
            }
            InstructionVars::DDD | InstructionVars::ALU | InstructionVars::N => {
                shift = 3;
                0b111 << shift
            }
            InstructionVars::SSS => {
                shift = 0;
                0b111
            }
        };
        let instruction = neg & instruction;
        instruction >> shift
    }
}
mod tests {
    use super::*;

    #[test]
    fn get_instruction_var() {
        let ins = 0b01101110;
        let rp = InstructionVars::get(ins, InstructionVars::RP);
        assert_eq!(rp, 2);
    }

    #[test]
    fn negate_instruction_var() {
        let ins = 0b11111111;
        let negated = InstructionVars::negate(ins, InstructionVars::DDD);
        assert_eq!(0b11000111, negated)
    }

    #[test]
    fn subset() {
        let subset = InstructionVars::get(0x38, InstructionVars::DDD);
        assert_eq!(subset, 7)
    }

    // #[test]
    // fn combine() {
    //     let second = 0xFF;
    //     let third = 0x1A;
    //     assert_eq!(combine_into_u16(second, third), 0x1AFF)
    // }

    #[test]
    fn lxi() {
        let mut cpu = Intel8080::default();
        // HL
        let inst: u8 = 0b00100001;
        cpu.memory[1] = 0xFB;
        cpu.memory[2] = 0xA3;
        lxi_rp_data(inst, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 0xA3FB);
    }

    #[test]
    fn stax() {
        let index = 0x3F16;
        let value = 0xA4;
        let mut cpu = Intel8080::default();
        cpu.set_register_pair(RegisterPair::DE, index);
        cpu.set_register(Register::A, value);
        let ins = 0b00010010;
        stax_rp(ins, &mut cpu);
        assert_eq!(cpu.memory[index as usize], value)
    }

    #[test]
    fn inx() {
        let mut cpu = Intel8080::default();
        let ins = 0b00100011;
        inx_rp(ins, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 1)
    }

    #[test]
    fn inx_low_overflow() {
        let mut cpu = Intel8080::default();
        let ins = 0b00010011;
        cpu.set_register(Register::E, 0xFF);
        inx_rp(ins, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::DE), 0x0100);
    }

    #[test]
    fn inx_high_overflow() {
        let mut cpu = Intel8080::default();
        let ins = 0b00000011;
        cpu.set_register_pair(RegisterPair::BC, 0xFFFF);
        inx_rp(ins, &mut cpu);
        assert_eq!(0, cpu.get_register_pair(&RegisterPair::BC))
    }

    #[test]
    fn inr_value() {
        let mut cpu = Intel8080::default();
        let ins = 0b00001100;
        cpu.set_register(Register::C, 0x20);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_register(&Register::C), 0x21)
    }

    #[test]
    fn inr_value_of() {
        let mut cpu = Intel8080::default();
        let ins = 0b00001100;
        cpu.set_register(Register::C, 0xFF);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_register(&Register::C), 0x0)
    }

    #[test]
    fn inr_zero() {
        let mut cpu = Intel8080::default();
        let ins = 0b00000100;
        cpu.set_register(Register::B, 0xFF);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b01010110);
    }

    #[test]
    fn inr_aux_carry() {
        let mut cpu = Intel8080::default();
        let ins = 0b00011100;
        cpu.set_register(Register::E, 0xF);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b00010010);
    }

    #[test]
    fn inr_parity() {
        let mut cpu = Intel8080::default();
        let ins = 0b00100100;
        cpu.set_register(Register::H, 0b11001110);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b10000110);
    }

    #[test]
    fn inr_sign() {
        let mut cpu = Intel8080::default();
        let ins = 0b00110100;
        cpu.set_register_pair(RegisterPair::HL, 0xFF);
        cpu.set_register(Register::M, -125i8 as u8);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b10000110);
    }

    #[test]
    fn dcr_value() {
        let mut cpu = Intel8080::default();
        let ins = 0b00000101;
        cpu.set_register(Register::B, 10);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(9, cpu.get_register(&Register::B));
    }

    #[test]
    fn dcr_value_of() {
        let mut cpu = Intel8080::default();
        let ins = 0b00001101;
        dcr_ddd(ins, &mut cpu);
        assert_eq!(255, cpu.get_register(&Register::C));
    }

    #[test]
    fn dcr_zero() {
        let mut cpu = Intel8080::default();
        let ins = 0b00010101;
        cpu.set_register(Register::D, 1);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b01000110)
    }

    #[test]
    fn dcr_aux_carry() {
        let mut cpu = Intel8080::default();
        let ins = 0b00011101;
        cpu.set_register(Register::E, 0b00100000);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b00010010);
    }

    #[test]
    fn dcr_parity() {
        let mut cpu = Intel8080::default();
        let ins = 0b00100101;
        cpu.set_register(Register::H, 0b00110111);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b00000110);
    }

    #[test]
    fn dcr_sign() {
        let mut cpu = Intel8080::default();
        let ins = 0b00011101;
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b10010110)
    }

    #[test]
    fn mvi() {
        let mut cpu = Intel8080::default();
        let ins = 0b00000110;
        cpu.memory[(cpu.program_counter + 1) as usize] = 69;
        mvi_ddd_data(ins, &mut cpu);
        assert_eq!(cpu.get_register(&Register::B), 69)
    }

    #[test]
    fn dad() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00001001;
        cpu.set_register_pair(RegisterPair::BC, 0x339F);
        cpu.set_register_pair(RegisterPair::HL, 0xA17B);
        cpu.set_flag(StatusFlags::C, true);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 0xD51A);
        assert_eq!(cpu.get_flag(StatusFlags::C), false)
    }

    #[test]
    fn dad_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00011001;
        cpu.set_register_pair(RegisterPair::HL, 0xFFFF);
        cpu.set_register_pair(RegisterPair::DE, 0xFF);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 0xFE);
        assert_eq!(cpu.get_flag(StatusFlags::C), true)
    }

    #[test]
    fn dad_hl() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00101001;
        cpu.set_register_pair(RegisterPair::HL, 0xFF);
        cpu.set_flag(StatusFlags::C, true);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 2 * 0xFF);
        assert_eq!(cpu.get_flag(StatusFlags::C), false)
    }

    #[test]
    fn dad_hl_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00101001;
        cpu.set_register_pair(RegisterPair::HL, 0xF1AB);
        let (res, _) = u16::overflowing_shl(0xF1AB, 1);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), res);
        assert_eq!(cpu.get_flag(StatusFlags::C), true)
    }

    #[test]
    fn ldax() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00001010;
        cpu.set_register_pair(RegisterPair::BC, 0xA1);
        cpu.memory[0xA1] = 0xFF;
        ldax_rp(instruction, &mut cpu);
        assert_eq!(0xFF, cpu.get_register(&Register::A))
    }

    #[test]
    #[should_panic]
    fn ldax_hl() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00101010;
        ldax_rp(instruction, &mut cpu)
    }

    #[test]
    fn dcr() {
        let mut cpu = Intel8080::default();
        cpu.set_register_pair(RegisterPair::DE, 0xF1);
        let instruction = 0b00011011;
        dcx_rp(instruction, &mut cpu);
        assert_eq!(0xF0, cpu.get_register_pair(&RegisterPair::DE))
    }

    #[test]
    fn dcr_low_of() {
        let mut cpu = Intel8080::default();
        cpu.set_register_pair(RegisterPair::BC, 0x100);
        let instruction = 0b00001011;
        dcx_rp(instruction, &mut cpu);
        assert_eq!(0xFF, cpu.get_register_pair(&RegisterPair::BC))
    }

    #[test]
    fn dcr_high_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00101011;
        dcx_rp(instruction, &mut cpu);
        assert_eq!(0xFFFF, cpu.get_register_pair(&RegisterPair::HL))
    }

    #[test]
    fn rlc_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xF2);
        rlc(&mut cpu);
        assert_eq!(cpu.get_flag(StatusFlags::C), true);
        assert_eq!(cpu.get_register(&Register::A), 0xE5);
    }

    #[test]
    fn rrc_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xF2);
        cpu.set_flag(StatusFlags::C, true);
        rrc(&mut cpu);
        assert_eq!(cpu.get_flag(StatusFlags::C), false);
        assert_eq!(cpu.get_register(&Register::A), 0x79)
    }

    #[test]
    fn ral_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xB5);
        ral(&mut cpu);
        assert_eq!(cpu.get_flag(StatusFlags::C), true);
        assert_eq!(cpu.get_register(&Register::A), 0x6A);
    }

    #[test]
    fn rar_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0x6A);
        cpu.set_flag(StatusFlags::C, true);
        rar(&mut cpu);
        assert_eq!(cpu.get_flag(StatusFlags::C), false);
        assert_eq!(cpu.get_register(&Register::A), 0xB5);
    }

    #[test]
    fn shld_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::H, 0xAE);
        cpu.set_register(Register::L, 0x29);
        cpu.memory[1] = 0x0A;
        cpu.memory[2] = 0x01;
        shld(&mut cpu);
        assert_eq!(cpu.memory[0x10A], 0x29);
        assert_eq!(cpu.memory[0x10A + 1], 0xAE)
    }

    #[test]
    fn daa_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0x9B);
        daa(&mut cpu);
        assert_eq!(cpu.get_flags(), 0b00010011);
        assert_eq!(cpu.get_register(&Register::A), 1)
    }

    #[test]
    fn daa_parity() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0x9D);
        daa(&mut cpu);
        assert_eq!(cpu.get_flags(), 0b00010111);
        assert_eq!(cpu.get_register(&Register::A), 3);
    }

    #[test]
    fn lhld_t() {
        let mut cpu = Intel8080::default();
        cpu.memory[1] = 0x5B;
        cpu.memory[2] = 0x02;
        cpu.memory[0x25B] = 0xFF;
        cpu.memory[0x25C] = 0x03;
        lhld(&mut cpu);
        assert_eq!(cpu.get_register(&Register::L), 0xFF);
        assert_eq!(cpu.get_register(&Register::H), 0x03);
    }

    #[test]
    fn cma_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0x51);
        cma(&mut cpu);
        assert_eq!(0xAE, cpu.get_register(&Register::A));
    }

    #[test]
    fn sta_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xA1);
        cpu.memory[1] = 0xB3;
        cpu.memory[2] = 0x05;
        sta(&mut cpu);
        assert_eq!(0xA1, cpu.memory[0x5B3]);
    }

    #[test]
    fn stc_t() {
        let mut cpu = Intel8080::default();
        stc(&mut cpu);
        assert_eq!(true, cpu.get_flag(StatusFlags::C));
    }

    #[test]
    fn lda_t() {
        let mut cpu = Intel8080::default();
        cpu.memory[1] = 0x00;
        cpu.memory[2] = 0x03;
        cpu.memory[0x300] = 0xBC;
        lda(&mut cpu);
        assert_eq!(0xBC, cpu.get_register(&Register::A));
    }
    
    #[test]
    fn cmc_unset(){
        let mut cpu = Intel8080::default();
        cmc(&mut cpu);
        assert_eq!(true, cpu.get_flag(StatusFlags::C));
    }
    
    #[test]
    fn cmc_set(){
        let mut cpu = Intel8080::default();
        cpu.set_flag(StatusFlags::C, true);
        cmc(&mut cpu);
        assert_eq!(false, cpu.get_flag(StatusFlags::C));
    }
}
