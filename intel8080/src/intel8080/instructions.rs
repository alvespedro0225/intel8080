use crate::intel8080::hardware::{Flags, Intel8080, Register, RegisterPair};

// https://en.wikipedia.org/wiki/Intel_8080#Instruction_set Instruction reference
// https://bitsavers.org/components/intel/MCS80/9800301D_8080_8085_Assembly_Language_Programming_Manual_May81.pdf 8080 manual
// https://svofski.github.io/pretty-8080-assembler/ assembler
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
        _ if (instruction & !0x10) == 0xA => {
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
        // 0b01DDDSSS
        _ if (instruction & !0b111111u8) == 0x40 => {
            mov_sss_ddd(instruction, intel8080);
        }
        // 0b01110110
        _ if instruction == 0x76 => {
            hlt(intel8080);
        }
        // 0b10001SSS
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0x80 => {
            add_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0x88 => {
            adc_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0x90 => {
            sub_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0x98 => {
            sbb_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0xA0 => {
            ana_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0xA8 => {
            xra_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0xB0 => {
            ora_sss(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::SSS) == 0xB8 => {
            cmp_sss(instruction, intel8080);
        }
        _ if instruction == 0xC9 => {
            ret(intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::DDD) == 0xC0 => {
            ret_cond(instruction, intel8080);
        }
        _ if instruction == 0xCD => {
            call(intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::DDD) == 0xC4 => {
            call_cond(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 0xC1 => {
            pop(instruction, intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::RP) == 0xC5 => {
            push(instruction, intel8080)
        }
        _ if instruction == 0xC3 => {
            jmp(intel8080);
        }
        _ if InstructionVars::negate(instruction, InstructionVars::DDD) == 0xC3 => {
            jmp_cond(instruction, intel8080);
        }
        _ if instruction == 0xC6 => {
            adi(intel8080);
            intel8080.program_counter += 1;
        }
        _ if instruction == 0xCE => {
            aci(intel8080);
            intel8080.program_counter += 1;
        }
        _ => {}
    }
}

// Manual page 25, PDF's 31
// Uses the next 2 instruction bytes as data and sets RP to it.
fn lxi_rp_data(instruction: u8, intel8080: &mut Intel8080) {
    let rp_value = combine_next_instructions(intel8080);
    let rp = get_associated_paired_register(instruction);
    intel8080.set_register_pair(rp, rp_value);
}
// Manual page 17, PDF's 23
// Store Accumulator. memory[RP] = A
fn stax_rp(instruction: u8, intel8080: &mut Intel8080) {
    let accumulator = intel8080.get_register(&Register::A);
    let rp = get_associated_paired_register(instruction);
    let index = intel8080.get_register_pair(&rp) as usize;
    intel8080.memory[index] = accumulator;
}
// Manal page 24, PDF's 30
// Increases RP by 1. RP += 1
fn inx_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = get_associated_paired_register(instruction);
    let rp_value = intel8080.get_register_pair(&rp);
    intel8080.set_register_pair(rp, u16::wrapping_add(rp_value, 1));
}
// Manual page 15, PDF's 21
// Increment register or memory. DDD += 1
fn inr_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = get_associated_register(instruction, InstructionVars::DDD);
    let register_value = intel8080.get_register(&ddd);
    let result = intel8080.set_status_add(register_value, 1, false);
    intel8080.set_register(ddd, result);
}
// Manual page 15, PDF's 21
// Decrement register or memory. DDD -= 1
fn dcr_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = get_associated_register(instruction, InstructionVars::DDD);
    let register_value = intel8080.get_register(&ddd);
    let result = intel8080.set_status_sub(register_value, 1, false);
    intel8080.set_register(ddd, result);
}
// Manual page 26, PDF's 32
// Move immediate data. DDD = Data
fn mvi_ddd_data(instruction: u8, intel8080: &mut Intel8080) {
    let ddd = get_associated_register(instruction, InstructionVars::DDD);
    let data = intel8080.memory[(intel8080.program_counter + 1) as usize];
    intel8080.set_register(ddd, data);
}
// Manual page 24, PDF's 30
// Double add. HL += RP
fn dad_rp(instruction: u8, intel8080: &mut Intel8080) {
    let hl = intel8080.get_register_pair(&RegisterPair::HL);
    let rp = get_associated_paired_register(instruction);

    let (sum, of) = if let RegisterPair::HL = rp {
        (hl << 1, hl >= 32768) // hl >= 32768 checks if msb is set
    } else {
        let rp = intel8080.get_register_pair(&rp);
        u16::overflowing_add(rp, hl)
    };

    intel8080.set_flag(Flags::C, of);
    intel8080.set_register_pair(RegisterPair::HL, sum);
}
// Manual page 17, PDF's 23
// Load Accumulator. A = memory[RP]
fn ldax_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = get_associated_paired_register(instruction);
    let rp = intel8080.get_register_pair(&rp);
    intel8080.set_register(Register::A, intel8080.memory[rp as usize]);
}
// Manual page 24, PDF's 30
// Decrement Register Pair. RP -= 1
fn dcx_rp(instruction: u8, intel8080: &mut Intel8080) {
    let rp = get_associated_paired_register(instruction);
    let rp_value = intel8080.get_register_pair(&rp);
    intel8080.set_register_pair(rp, u16::wrapping_sub(rp_value, 1));
}
// Manual page 21, PDF's 27
// Rotate Accumulator Left
fn rlc(intel8080: &mut Intel8080) {
    let accumulator = intel8080.get_register(&Register::A);
    let carry = accumulator >> 7 == 1;
    intel8080.set_flag(Flags::C, carry);
    intel8080.set_register(Register::A, accumulator.rotate_left(1))
}
// Manual page 21, PDF's 27
// Rotate Accumulator Right
fn rrc(intel8080: &mut Intel8080) {
    let accumulator = intel8080.get_register(&Register::A);
    let carry = (accumulator & 1) == 1;
    intel8080.set_flag(Flags::C, carry);
    intel8080.set_register(Register::A, accumulator.rotate_right(1));
}
// Manual page 22, PDF's 28
// Rotate Accumulator Left Through Carry
fn ral(intel8080: &mut Intel8080) {
    let mut accumulator = intel8080.get_register(&Register::A);
    let carry = if intel8080.get_flag(Flags::C) { 1 } else { 0 };
    let new_carry = accumulator >> 7 == 1;
    intel8080.set_flag(Flags::C, new_carry);
    accumulator <<= 1;
    accumulator ^= carry;
    intel8080.set_register(Register::A, accumulator);
}
// Manual page 22, PDF's 28
// Rotate Accumulator Right Through Carry
fn rar(intel8080: &mut Intel8080) {
    let mut accumulator = intel8080.get_register(&Register::A);
    let carry = if intel8080.get_flag(Flags::C) { 1 } else { 0 };
    let new_carry = accumulator & 1 == 1;
    intel8080.set_flag(Flags::C, new_carry);
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
        intel8080.set_flag(Flags::AC, true);
    } else if intel8080.get_flag(Flags::AC) {
        accumulator += 6;
        intel8080.set_flag(Flags::AC, false);
    }

    let left = (accumulator & 0xF0) >> 4;

    if left > 9 {
        accumulator = u8::wrapping_add(accumulator, 6 << 4);
        intel8080.set_flag(Flags::C, true);
    } else if intel8080.get_flag(Flags::C) {
        accumulator += 6 << 4;
        intel8080.set_flag(Flags::C, false);
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
    intel8080.set_flag(Flags::C, true);
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
fn cmc(intel8080: &mut Intel8080) {
    let carry = intel8080.get_flag(Flags::C);
    intel8080.set_flag(Flags::C, !carry);
}
// Manual page 16, PDF's 22
//  MOV Instruction
fn mov_sss_ddd(instruction: u8, intel8080: &mut Intel8080) {
    let src = get_associated_register(instruction, InstructionVars::SSS);
    let dest = get_associated_register(instruction, InstructionVars::DDD);
    let src = intel8080.get_register(&src);
    intel8080.set_register(dest, src);
}
// Manual page 39, PDF's 45
// Halt
fn hlt(intel8080: &mut Intel8080) {
    intel8080.stopped = true;
}
// Manual page 17, PDF's 23
// ADD Register or Memory To Accumulator
fn add_sss(instruction: u8, intel8080: &mut Intel8080) {
    let added = get_associated_register(instruction, InstructionVars::SSS);
    let added = intel8080.get_register(&added);
    let accumulator = intel8080.get_register(&Register::A);
    let result = intel8080.set_status_add(accumulator, added, true);
    intel8080.set_register(Register::A, result);
}
// Manual page 18, PDF's 24
// ADD Register or Memory To Accumulator With Carry
fn adc_sss(instruction: u8, intel8080: &mut Intel8080) {
    let added = get_associated_register(instruction, InstructionVars::SSS);
    let added = intel8080.get_register(&added);
    let accumulator = intel8080.get_register(&Register::A);
    let result: u8;

    if intel8080.get_flag(Flags::C) {
        result = add_with_carry(intel8080, accumulator, added);
    } else {
        result = intel8080.set_status_add(accumulator, added, true);
    }

    intel8080.set_register(Register::A, result);
}

// Manual page 18, PDF's 24
// SUB Subtract Register or Memory From Accumulator
fn sub_sss(instruction: u8, intel8080: &mut Intel8080) {
    let sub = get_associated_register(instruction, InstructionVars::SSS);
    let sub = intel8080.get_register(&sub);
    let accumulator = intel8080.get_register(&Register::A);
    let result = intel8080.set_status_sub(accumulator, sub, true);
    intel8080.set_register(Register::A, result);
}
// Manual page 18, PDF's 24
// SUB Subtract Register or Memory From Accumulator With Borrow
fn sbb_sss(instruction: u8, intel8080: &mut Intel8080) {
    let sub = get_associated_register(instruction, InstructionVars::SSS);
    let sub = intel8080.get_register(&sub);
    let accumulator = intel8080.get_register(&Register::A);
    let result: u8;

    if intel8080.get_flag(Flags::C) {
        result = sub_with_carry(intel8080, accumulator, sub);
    } else {
        result = intel8080.set_status_sub(accumulator, sub, true);
    }

    intel8080.set_register(Register::A, result);
}
// Manual page 19, PDF's 25
// Logical and Register or Memory With Accumulator
fn ana_sss(instruction: u8, intel8080: &mut Intel8080) {
    let sss = get_associated_register(instruction, InstructionVars::SSS);
    let sss = intel8080.get_register(&sss);
    let accumulator = intel8080.get_register(&Register::A);
    let result = sss & accumulator;
    let aux_carry = (sss & 0xF) == 0xF || (accumulator & 0xF) == 0xF;
    intel8080.set_flag(Flags::AC, aux_carry);
    intel8080.set_register(Register::A, result);
    intel8080.set_flag(Flags::C, false);
    intel8080.set_parity(result);
    intel8080.set_zero_or_less(result);
}
// Manual page 19, PDF's 25
// Logical and Register or Memory With Accumulator
fn xra_sss(instruction: u8, intel8080: &mut Intel8080) {
    let sss = get_associated_register(instruction, InstructionVars::SSS);
    let sss = intel8080.get_register(&sss);
    let accumulator = intel8080.get_register(&Register::A);
    let result = sss ^ accumulator;
    intel8080.set_flag(Flags::C, false);
    intel8080.set_flag(Flags::AC, false);
    intel8080.set_parity(result);
    intel8080.set_zero_or_less(result);
    intel8080.set_register(Register::A, result);
}

fn ora_sss(instruction: u8, intel8080: &mut Intel8080) {
    let sss = get_associated_register(instruction, InstructionVars::SSS);
    let sss = intel8080.get_register(&sss);
    let accumulator = intel8080.get_register(&Register::A);
    let result = sss | accumulator;
    intel8080.set_flag(Flags::C, false);
    intel8080.set_flag(Flags::AC, false);
    intel8080.set_parity(result);
    intel8080.set_zero_or_less(result);
    intel8080.set_register(Register::A, result);
}

fn cmp_sss(instruction: u8, intel8080: &mut Intel8080) {
    let sss = get_associated_register(instruction, InstructionVars::SSS);
    let sss = intel8080.get_register(&sss);
    let accumulator = intel8080.get_register(&Register::A);
    intel8080.set_status_sub(accumulator, sss, true);
}

fn ret(intel8080: &mut Intel8080) {
    let address = intel8080.pop_address();
    intel8080.program_counter = address;
}

fn ret_cond(instruction: u8, intel8080: &mut Intel8080) {
    let condition = InstructionVars::get_conditions(instruction, intel8080);

    if condition {
        ret(intel8080)
    }
}

fn jmp(intel8080: &mut Intel8080) {
    let address = combine_next_instructions(intel8080);
    intel8080.program_counter = address;
}

fn jmp_cond(instruction: u8, intel8080: &mut Intel8080) {
    let condition = InstructionVars::get_conditions(instruction, intel8080);

    if condition {
        jmp(intel8080);
    }
}

fn call(intel8080: &mut Intel8080) {
    let address = combine_next_instructions(intel8080);
    intel8080.push_address(address);
    intel8080.program_counter = address;
}

fn call_cond(instruction: u8, intel8080: &mut Intel8080) {
    let condition = InstructionVars::get_conditions(instruction, intel8080);

    if condition {
        call(intel8080);
    }
}
fn pop(instruction: u8, intel8080: &mut Intel8080) {
    let rp = get_associated_paired_register(instruction);
    let popped = intel8080.pop_address();
    intel8080.set_register_pair(rp, popped);
}

fn push(instruction: u8, intel8080: &mut Intel8080) {
    let rp = get_associated_paired_register(instruction);
    let pushed = intel8080.get_register_pair(&rp);
    intel8080.push_address(pushed);
}

fn adi(intel8080: &mut Intel8080) {
    let added = intel8080.memory[intel8080.program_counter as usize];
    let accumulator = intel8080.get_register(&Register::A);
    let result = intel8080.set_status_add(accumulator, added, true);
    intel8080.set_register(Register::A, result);
}

fn aci(intel8080: &mut Intel8080) {
    let added = intel8080.memory[intel8080.program_counter as usize];
    let accumulator = intel8080.get_register(&Register::A);
    let result: u8;

    if intel8080.get_flag(Flags::C) {
        result = add_with_carry(intel8080, accumulator, added);
    } else {
        result = intel8080.set_status_add(accumulator, added, true);
    }

    intel8080.set_register(Register::A, result);
}
fn get_associated_register(instruction: u8, var: InstructionVars) -> Register {
    let subset = InstructionVars::get_subset(instruction, &var);

    if let InstructionVars::RP = var {
        panic!("Double byte register used in single byte register operation")
    }

    Register::from(subset)
}

fn get_associated_paired_register(instruction: u8) -> RegisterPair {
    let subset = InstructionVars::get_subset(instruction, &InstructionVars::RP);
    RegisterPair::from(subset)
}
/// Combines the next two instructions into one 16 bits number. The third byte is the msb.
fn combine_next_instructions(intel8080: &mut Intel8080) -> u16 {
    let pc = intel8080.program_counter as usize;
    let (second, third) = (intel8080.memory[pc], intel8080.memory[pc + 1]);
    combine_into_u16(second, third)
}

fn combine_into_u16(low: u8, high: u8) -> u16 {
    let low = low as u16;
    let high = high as u16;
    let mut value = high << 8;
    value ^= low;
    value
}

fn add_with_carry(intel8080: &mut Intel8080, accumulator: u8, added: u8) -> u8 {
    let result = u8::wrapping_add(accumulator, added);
    let result = u8::wrapping_add(result, 1);
    intel8080.set_zero_or_less(result);
    intel8080.set_parity(result);
    let accumulator = accumulator as u16;
    let added = added as u16;
    let res = accumulator + added + 1;
    let res = res ^ accumulator ^ added;
    let aux = res & (1 << 4) > 0;
    let carry = res & (1 << 8) > 0;
    intel8080.set_flag(Flags::C, carry);
    intel8080.set_flag(Flags::AC, aux);
    result
}

fn sub_with_carry(intel8080: &mut Intel8080, accumulator: u8, sub: u8) -> u8 {
    // sub + 1 cause adding the carry to the subtracting number. not adding the + 1 from 2's
    // complement becausse teh add with carry adds 1 by default
    let res = add_with_carry(intel8080, accumulator, !u8::wrapping_add(sub, 1));
    intel8080.flip_carry();
    res
}
enum InstructionVars {
    RP,
    DDD,
    SSS,
}

impl InstructionVars {
    fn negate(instruction: u8, var: InstructionVars) -> u8 {
        let neg = match var {
            InstructionVars::RP => !(0b11 << 4),
            InstructionVars::DDD => !(0b111 << 3),
            InstructionVars::SSS => !0b111,
        };
        instruction & neg
    }

    fn get_subset(instruction: u8, var: &InstructionVars) -> u8 {
        let shift;
        let neg = match var {
            InstructionVars::RP => {
                shift = 4;
                0b11 << shift
            }
            InstructionVars::DDD => {
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
    fn get_conditions(instruction: u8, intel8080: &mut Intel8080) -> bool {
        let cc = InstructionVars::get_subset(instruction, &InstructionVars::DDD);
        match cc {
            0 => !intel8080.get_flag(Flags::Z), // RNZ
            1 => intel8080.get_flag(Flags::Z),  // RZ
            2 => !intel8080.get_flag(Flags::C), // RNC
            3 => intel8080.get_flag(Flags::C),  // RC
            4 => !intel8080.get_flag(Flags::P), // RPO
            5 => intel8080.get_flag(Flags::P),  // RPE
            6 => !intel8080.get_flag(Flags::S), // RP
            7 => intel8080.get_flag(Flags::S),  // RM
            _ => panic!("Shouldn't be possible to get more than 7 out of 3 bits"),
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_instruction_var() {
        let ins = 0b01101110;
        let rp = InstructionVars::get_subset(ins, &InstructionVars::RP);
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
        let subset = InstructionVars::get_subset(0x38, &InstructionVars::DDD);
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
        cpu.memory[0] = 0xFB;
        cpu.memory[1] = 0xA3;
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
    fn dcr_value_max() {
        let mut cpu = Intel8080::default();
        let ins = 0x0D; // DCR C
        cpu.set_register(Register::C, u8::MAX);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(u8::MAX - 1, cpu.get_register(&Register::C));
    }

    #[test]
    fn dcr_value_min() {
        let mut cpu = Intel8080::default();
        let ins = 0x0D; // DCR C
        dcr_ddd(ins, &mut cpu);
        assert_eq!(u8::wrapping_sub(u8::MIN, 1), cpu.get_register(&Register::C));
    }

    #[test]
    fn dcr_zero() {
        let mut cpu = Intel8080::default();
        let ins = 0b00010101;
        cpu.set_register(Register::D, 1);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flag(Flags::Z), true)
    }

    #[test]
    fn dcr_aux_carry() {
        let mut cpu = Intel8080::default();
        let ins = 0b00011101;
        cpu.set_register(Register::E, 0b00100000);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flag(Flags::AC), false);
    }

    #[test]
    fn dcr_parity() {
        let mut cpu = Intel8080::default();
        let ins = 0b00100101;
        cpu.set_register(Register::H, 0b00110111);
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flag(Flags::P), true);
    }

    #[test]
    fn dcr_sign() {
        let mut cpu = Intel8080::default();
        let ins = 0b00011101;
        dcr_ddd(ins, &mut cpu);
        assert_eq!(cpu.get_flag(Flags::S), true)
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
        cpu.set_flag(Flags::C, true);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 0xD51A);
        assert_eq!(cpu.get_flag(Flags::C), false)
    }

    #[test]
    fn dad_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00011001;
        cpu.set_register_pair(RegisterPair::HL, 0xFFFF);
        cpu.set_register_pair(RegisterPair::DE, 0xFF);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 0xFE);
        assert_eq!(cpu.get_flag(Flags::C), true)
    }

    #[test]
    fn dad_hl() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00101001;
        cpu.set_register_pair(RegisterPair::HL, 0xFF);
        cpu.set_flag(Flags::C, true);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 2 * 0xFF);
        assert_eq!(cpu.get_flag(Flags::C), false)
    }

    #[test]
    fn dad_hl_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0b00101001;
        cpu.set_register_pair(RegisterPair::HL, 0xF1AB);
        let (res, _) = u16::overflowing_shl(0xF1AB, 1);
        dad_rp(instruction, &mut cpu);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), res);
        assert_eq!(cpu.get_flag(Flags::C), true)
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
        assert_eq!(cpu.get_flag(Flags::C), true);
        assert_eq!(cpu.get_register(&Register::A), 0xE5);
    }

    #[test]
    fn rrc_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xF2);
        cpu.set_flag(Flags::C, true);
        rrc(&mut cpu);
        assert_eq!(cpu.get_flag(Flags::C), false);
        assert_eq!(cpu.get_register(&Register::A), 0x79)
    }

    #[test]
    fn ral_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xB5);
        ral(&mut cpu);
        assert_eq!(cpu.get_flag(Flags::C), true);
        assert_eq!(cpu.get_register(&Register::A), 0x6A);
    }

    #[test]
    fn rar_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0x6A);
        cpu.set_flag(Flags::C, true);
        rar(&mut cpu);
        assert_eq!(cpu.get_flag(Flags::C), false);
        assert_eq!(cpu.get_register(&Register::A), 0xB5);
    }

    #[test]
    fn shld_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::H, 0xAE);
        cpu.set_register(Register::L, 0x29);
        cpu.memory[0] = 0x0A;
        cpu.memory[1] = 0x01;
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
        cpu.memory[0] = 0x5B;
        cpu.memory[1] = 0x02;
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
        cpu.memory[0] = 0xB3;
        cpu.memory[1] = 0x05;
        sta(&mut cpu);
        assert_eq!(0xA1, cpu.memory[0x5B3]);
    }

    #[test]
    fn stc_t() {
        let mut cpu = Intel8080::default();
        stc(&mut cpu);
        assert_eq!(true, cpu.get_flag(Flags::C));
    }

    #[test]
    fn lda_t() {
        let mut cpu = Intel8080::default();
        cpu.memory[0] = 0x00;
        cpu.memory[1] = 0x03;
        cpu.memory[0x300] = 0xBC;
        lda(&mut cpu);
        assert_eq!(0xBC, cpu.get_register(&Register::A));
    }

    #[test]
    fn cmc_unset() {
        let mut cpu = Intel8080::default();
        cmc(&mut cpu);
        assert_eq!(true, cpu.get_flag(Flags::C));
    }

    #[test]
    fn cmc_set() {
        let mut cpu = Intel8080::default();
        cpu.set_flag(Flags::C, true);
        cmc(&mut cpu);
        assert_eq!(false, cpu.get_flag(Flags::C));
    }

    #[test]
    fn mov() {
        let mut cpu = Intel8080::default();
        let instruction = 0x77;
        cpu.set_register(Register::A, 0x11);
        cpu.set_register(Register::H, 0x2B);
        cpu.set_register(Register::L, 0xE9);
        mov_sss_ddd(instruction, &mut cpu);
        assert_eq!(
            cpu.get_register(&Register::A),
            cpu.get_register(&Register::M)
        );
    }

    #[test]
    fn add() {
        let mut cpu = Intel8080::default();
        let instruction = 0x82;
        cpu.set_register(Register::D, 0x2E);
        cpu.set_register(Register::A, 0x6C);
        add_sss(instruction, &mut cpu);
        assert_eq!(0x9A, cpu.get_register(&Register::A));
        assert_eq!(0b10010110, cpu.get_flags())
    }

    #[test]
    fn add_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0x86;
        cpu.set_register(Register::H, 0x10);
        cpu.set_register(Register::L, 0xAB);
        cpu.set_register(Register::M, 0x10);
        cpu.set_register(Register::A, 0xF0);
        add_sss(instruction, &mut cpu);
        assert_eq!(0, cpu.get_register(&Register::A));
        assert_eq!(0b01000111, cpu.get_flags())
    }

    #[test]
    fn adc_unset() {
        let mut cpu = Intel8080::default();
        let instruction = 0x89; // ADC C
        cpu.set_register(Register::C, 0x3D);
        cpu.set_register(Register::A, 0x42);
        adc_sss(instruction, &mut cpu);
        assert_eq!(cpu.get_register(&Register::A), 0x7F);
        assert_eq!(cpu.get_flags(), 0b00000010);
    }

    #[test]
    fn adc_set() {
        let mut cpu = Intel8080::default();
        let instruction = 0x89; // ADC C
        cpu.set_register(Register::C, 0x3D);
        cpu.set_register(Register::A, 0x42);
        cpu.set_flag(Flags::C, true);
        adc_sss(instruction, &mut cpu);
        assert_eq!(cpu.get_register(&Register::A), 0x80);
        assert_eq!(cpu.get_flags(), 0b10010010);
    }

    #[test]
    fn adc_of() {
        let mut cpu = Intel8080::default();
        let instruction = 0x8E; // ADC M
        cpu.set_register(Register::H, 0x10);
        cpu.set_register(Register::L, 0xAB);
        cpu.set_register(Register::M, 0x0F);
        cpu.set_register(Register::A, 0xF0);
        cpu.set_flag(Flags::C, true);
        adc_sss(instruction, &mut cpu);
        assert_eq!(0, cpu.get_register(&Register::A));
        assert_eq!(0b01010111, cpu.get_flags())
    }

    #[test]
    fn adc_255() {
        let mut cpu = Intel8080::default();
        let instruction = 0x8C; // ADC H
        cpu.set_register(Register::H, 255);
        cpu.set_register(Register::A, 255);
        cpu.set_flag(Flags::C, true);
        adc_sss(instruction, &mut cpu);
        assert_eq!(255, cpu.get_register(&Register::A));
        assert_eq!(0b10010111, cpu.get_flags());
    }

    #[test]
    fn sub() {
        let mut cpu = Intel8080::default();
        let instruction = 0x97; // SUB A
        cpu.set_register(Register::A, 0x3E);
        sub_sss(instruction, &mut cpu);
        assert_eq!(0, cpu.get_register(&Register::A));
        assert_eq!(0b01010110, cpu.get_flags());
    }

    #[test]
    fn sbb() {
        let mut cpu = Intel8080::default();
        let instruction = 0x9D;
        cpu.set_register(Register::A, 0x4);
        cpu.set_register(Register::L, 0x2);
        cpu.set_flag(Flags::C, true);
        sbb_sss(instruction, &mut cpu);
        assert_eq!(1, cpu.get_register(&Register::A));
        assert_eq!(0b00010010, cpu.get_flags())
    }

    #[test]
    fn sbb_255() {
        let mut cpu = Intel8080::default();
        let instruction = 0x97; // SUB A
        cpu.set_register(Register::A, 255);
        cpu.set_flag(Flags::C, true);
        sbb_sss(instruction, &mut cpu);
        assert_eq!(255, cpu.get_register(&Register::A));
        assert_eq!(0b10010110, cpu.get_flags());
    }

    #[test]
    fn ana() {
        let mut cpu = Intel8080::default();
        let instruction = 0xA1;
        cpu.set_register(Register::C, 0x0F);
        cpu.set_register(Register::A, 0xFC);
        ana_sss(instruction, &mut cpu);
        assert_eq!(0xC, cpu.get_register(&Register::A));
        assert_eq!(0b00010110, cpu.get_flags())
    }

    #[test]
    fn xra() {
        let mut cpu = Intel8080::default();
        let instruction = 0xAF;
        cpu.set_register(Register::A, 0xB5);
        cpu.set_flag(Flags::AC, true);
        cpu.set_flag(Flags::C, true);
        xra_sss(instruction, &mut cpu);
        assert_eq!(0, cpu.get_register(&Register::A));
        assert_eq!(0b01000110, cpu.get_flags());
    }

    #[test]
    fn ora() {
        let mut cpu = Intel8080::default();
        let instruction = 0xB2;
        cpu.set_register(Register::D, 0x8);
        cpu.set_register(Register::A, 0x43);
        cpu.set_flag(Flags::C, true);
        cpu.set_flag(Flags::AC, true);
        ora_sss(instruction, &mut cpu);
        assert_eq!(0x4B, cpu.get_register(&Register::A));
        assert_eq!(0b00000110, cpu.get_flags());
    }

    #[test]
    fn cmp() {
        let mut cpu = Intel8080::default();
        let instruction = 0xBB;
        cpu.set_register(Register::E, 0x5);
        cpu.set_register(Register::A, 0xA);
        cmp_sss(instruction, &mut cpu);
        assert_eq!(0b00010110, cpu.get_flags())
    }

    #[test]
    fn ret_t() {
        let mut cpu = Intel8080::default();
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret(&mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }
    #[test]
    fn rnz_unset() {
        let mut cpu = Intel8080::default();
        let instruction = 0xC0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rnz_set() {
        let mut cpu = Intel8080::default();
        let instruction = 0xC0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::Z, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rz_unset() {
        let mut cpu = Intel8080::default();
        let instruction = 0xC8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rz_set() {
        let mut cpu = Intel8080::default();
        let instruction = 0xC8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::Z, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rnc_unset() {
        let mut cpu = Intel8080::default();
        let instruction = 0xD0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rnc_set() {
        let mut cpu = Intel8080::default();
        let instruction = 0xD0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::C, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rc_unset() {
        let mut cpu = Intel8080::default();
        let instruction = 0xD8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rc_set() {
        let mut cpu = Intel8080::default();
        let instruction = 0xD8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::C, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rpo_odd() {
        let mut cpu = Intel8080::default();
        let instruction = 0xE0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rpo_even() {
        let mut cpu = Intel8080::default();
        let instruction = 0xE0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::P, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rpe_odd() {
        let mut cpu = Intel8080::default();
        let instruction = 0xE8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rpe_even() {
        let mut cpu = Intel8080::default();
        let instruction = 0xE8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::P, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rp_pos() {
        let mut cpu = Intel8080::default();
        let instruction = 0xF0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn rp_neg() {
        let mut cpu = Intel8080::default();
        let instruction = 0xF0;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::S, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rm_pos() {
        let mut cpu = Intel8080::default();
        let instruction = 0xF8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xF1F1);
    }

    #[test]
    fn rm_neg() {
        let mut cpu = Intel8080::default();
        let instruction = 0xF8;
        cpu.push_address(0xAADD);
        cpu.program_counter = 0xF1F1;
        cpu.set_flag(Flags::S, true);
        ret_cond(instruction, &mut cpu);
        assert_eq!(cpu.program_counter, 0xAADD);
    }

    #[test]
    fn jump_t() {
        let mut cpu = Intel8080::default();
        cpu.memory[0] = 0xFF;
        cpu.memory[1] = 0x2B;
        jmp(&mut cpu);
        assert_eq!(cpu.program_counter, 0x2BFF);
    }

    #[test]
    fn call_t() {
        let mut cpu = Intel8080::default();
        cpu.program_counter = 0xA1B2;
        let pc = cpu.program_counter as usize;
        cpu.memory[pc] = 0xCC;
        cpu.memory[pc + 1] = 0xDD;
        call(&mut cpu);
        assert_eq!(cpu.program_counter, 0xDDCC);
    }

    #[test]
    fn pop_reg() {
        let mut cpu = Intel8080::default();
        let instruction = 0xC1; // POP B
        cpu.push_address(0xFFAA);
        pop(instruction, &mut cpu);
        assert_eq!(0xFFAA, cpu.get_register_pair(&RegisterPair::BC))
    }

    #[test]
    fn pop_psw() {
        let mut cpu = Intel8080::default();
        let instruction = 0xF1; // POP PSW
        cpu.push_address(0xFFAA);
        pop(instruction, &mut cpu);
        assert_eq!(0xFFAA, cpu.get_register_pair(&RegisterPair::PSW));
    }

    #[test]
    fn push_reg() {
        let mut cpu = Intel8080::default();
        let instruction = 0xC5; // PUSH D
        cpu.set_register(Register::B, 0x2A);
        cpu.set_register(Register::C, 0x4C);
        push(instruction, &mut cpu);
        assert_eq!(0x2A4C, cpu.pop_address())
    }

    #[test]
    fn push_psw() {
        let mut cpu = Intel8080::default();
        let instruction = 0xF5;
        cpu.set_register(Register::FLAGS, 0x92);
        cpu.set_register(Register::A, 0x2B);
        push(instruction, &mut cpu);
        assert_eq!(0x2b92, cpu.get_register_pair(&RegisterPair::PSW))
    }

    #[test]
    fn adi_t() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0x14);
        cpu.memory[0] = 0x42;
        adi(&mut cpu);
        assert_eq!(0x56, cpu.get_register(&Register::A));
        assert_eq!(0b00000110, cpu.get_flags());
    }

    #[test]
    fn adi_of() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 0xFF);
        cpu.memory[0] = 0xFF;
        adi(&mut cpu);
        assert_eq!(0xFE, cpu.get_register(&Register::A));
        assert_eq!(0b10010011, cpu.get_flags());
    }

    #[test]
    fn aci_unset(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 100);
        cpu.memory[0] = 95;
        aci(&mut cpu);
        assert_eq!(195, cpu.get_register(&Register::A));
        assert_eq!(0b10010110, cpu.get_flags());
    }

    #[test]
    fn aci_set(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 100);
        cpu.set_flag(Flags::C, true);
        cpu.memory[0] = 95;
        aci(&mut cpu);
        assert_eq!(196, cpu.get_register(&Register::A));
        assert_eq!(0b10010010, cpu.get_flags());
    }
    
    #[test]
    fn aci_acc_max(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 255);
        cpu.set_flag(Flags::C, true);
        cpu.memory[0] = 95;
        aci(&mut cpu);
        assert_eq!(95, cpu.get_register(&Register::A));
        assert_eq!(0b00010111, cpu.get_flags());
    }
    
    #[test]
    fn aci_next_max(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 95);
        cpu.set_flag(Flags::C, true);
        cpu.memory[0] = 255;
        aci(&mut cpu);
        assert_eq!(95, cpu.get_register(&Register::A));
        assert_eq!(0b00010111, cpu.get_flags());
    }
    
    #[test]
    fn aci_both_max(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 255);
        cpu.set_flag(Flags::C, true);
        cpu.memory[0] = 255;
        aci(&mut cpu);
        assert_eq!(255, cpu.get_register(&Register::A));
        assert_eq!(0b10010111, cpu.get_flags());
    }
}
