use crate::intel8080::hardware::{Intel8080, Register, RegisterPair};
use std::num::Wrapping;

// https://en.wikipedia.org/wiki/Intel_8080#Instruction_set Instruction reference
// https://altairclone.com/downloads/manuals/8080%20Programmers%20Manual.pdf 8080 manual
pub fn handle_instruction(instruction: u8, intel8080: &mut Intel8080) {
    intel8080.program_counter += 1;
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
        _ => {}
    }
}

// Manual page 25, PDF's 31
// Uses the next 2 instruction bytes as data and sets RP to it.
fn lxi_rp_data(instruction: u8, intel8080: &mut Intel8080) {
    let mem = intel8080.memory;
    let pc = intel8080.program_counter as usize;
    let (data_low, data_high) = (mem[pc], mem[pc + 1]);
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let data = combine_into_u16(data_low, data_high);

    match rp {
        0 => intel8080.set_register_pair(RegisterPair::BC, data),
        1 => intel8080.set_register_pair(RegisterPair::DE, data),
        2 => intel8080.set_register_pair(RegisterPair::HL, data),
        3 => intel8080.set_register_pair(RegisterPair::SP, data),
        _ => panic!("Invalid RP value: {rp}"),
    }
}
// Manual page 17, PDF's 23
// Stores register A's value at memory[RP], where RP is BC or DE
fn stax_rp(instruction: u8, intel8080: &mut Intel8080) {
    let reg_a = intel8080.get_register(Register::A);
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let index = match rp {
        0 => intel8080.get_register_pair(RegisterPair::BC) as usize,
        1 => intel8080.get_register_pair(RegisterPair::DE) as usize,
        _ => panic!("Stack can only target BC (0) or DE (1), target: {rp}"),
    };

    intel8080.memory[index] = reg_a;
}
// Manal page 24, PDF's 30
// Increases RP by 1. Overflow allowed
fn inx_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = InstructionVars::get(instruction, InstructionVars::RP);
    let rp = match rp {
        0 => RegisterPair::BC,
        1 => RegisterPair::DE,
        2 => RegisterPair::HL,
        3 => RegisterPair::SP,
        _ => panic!("Invalid RP value {rp}"),
    };
    let rp_value = intel8080.get_register_pair(rp);
    intel8080.set_register_pair(rp, (Wrapping(rp_value) + Wrapping(1)).0);
}
// Manual page 15, PDF's 21
// Increment register or memory. DDD = DDD + 1
fn inr_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = InstructionVars::get(instruction, InstructionVars::DDD);
    let register = Register::get_ddd(ddd);
    let register_value = intel8080.get_register(register);
    let (new_value, _) = u8::overflowing_add(register_value, 1);
    intel8080.set_register(register, new_value);
    intel8080.set_status_add(register_value, 1);
}
fn dcr_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = InstructionVars::get(instruction, InstructionVars::DDD);
    let register = Register::get_ddd(ddd);
    let register_value = intel8080.get_register(register);
    let (new_value, _) = u8::overflowing_sub(register_value, 1);
    intel8080.set_register(register, new_value);
    intel8080.set_status_sub(register_value, 1);
}

fn combine_into_u16(low: u8, high: u8) -> u16 {
    let mut combined = 0;
    combined |= (high as u16) << 8;
    combined |= low as u16;
    combined
}

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

    #[test]
    fn combine() {
        let low: u8 = 0xFF;
        let high: u8 = 0xAA;
        let combined = combine_into_u16(low, high);
        assert_eq!(combined, 0xAAFF);
    }

    #[test]
    fn lxi() {
        let mut cpu = Intel8080::default();
        // HL
        let inst: u8 = 0b00100001;
        cpu.memory[0] = 0xFB;
        cpu.memory[1] = 0xA3;
        lxi_rp_data(inst, &mut cpu);
        assert_eq!(cpu.get_register_pair(RegisterPair::HL), 0xA3FB);
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
        assert_eq!(cpu.get_register_pair(RegisterPair::HL), 1)
    }

    #[test]
    fn inx_low_overflow() {
        let mut cpu = Intel8080::default();
        let ins = 0b00010011;
        cpu.set_register(Register::E, 0xFF);
        inx_rp(ins, &mut cpu);
        assert_eq!(cpu.get_register_pair(RegisterPair::DE), 0x0100);
    }

    #[test]
    fn inx_high_overflow() {
        let mut cpu = Intel8080::default();
        let ins = 0b00000011;
        cpu.set_register_pair(RegisterPair::BC, 0xFFFF);
        inx_rp(ins, &mut cpu);
        assert_eq!(0, cpu.get_register_pair(RegisterPair::BC))
    }

    #[test]
    fn inr_value() {
        let mut cpu = Intel8080::default();
        let ins = 0b00001100;
        cpu.set_register(Register::C, 0x20);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_register(Register::C), 0x21)
    }

    #[test]
    fn inr_value_of(){
        let mut cpu = Intel8080::default();
        let ins = 0b00001100;
        cpu.set_register(Register::C, 0xFF);
        inr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_register(Register::C), 0x0)
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
    fn dcr_value(){
        let mut cpu = Intel8080::default();
        let ins = 0b00000101;
        cpu.set_register(Register::B, 10);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(9, cpu.get_register(Register::B));
    }

    #[test]
    fn dcr_value_of(){
        let mut cpu = Intel8080::default();
        let ins = 0b00001101;
        dcr_ddd(ins, &mut cpu);
        assert_eq!(255, cpu.get_register(Register::C));
    }

    #[test]
    fn dcr_zero(){
        let mut cpu = Intel8080::default();
        let ins = 0b00010101;
        cpu.set_register(Register::D, 1);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b01000110)
    }

    #[test]
    fn dcr_aux_carry(){
        let mut cpu = Intel8080::default();
        let ins =  0b00011101;
        cpu.set_register(Register::E, 0b00100000);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b00010010);
    }
    
    #[test]
    fn dcr_parity(){
        let mut cpu = Intel8080::default();
        let ins = 0b00100101;
        cpu.set_register(Register::H, 0b00110111);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b00000110);
    }
    
    #[test]
    fn dcr_sign(){
        let mut cpu = Intel8080::default();
        let ins = 0b00011101;
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flags(), 0b10010110)
    }
}
