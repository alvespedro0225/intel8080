use crate::intel8080::hardware::{Intel8080, RegisterPair};
use crate::intel8080::instructions::InstructionVars::RP;

pub fn handle_instruction(instruction: u8, intel8080: &mut Intel8080) {
    intel8080.program_counter += 1;
    match instruction {
        // 0b00RP0001 -> RP = data, where data_low = next_inst and data_high = next_inst + 1
        _ if instruction & InstructionVars::negate(RP) == 1 => lxi_rp_data(instruction, intel8080),
        _ => {}
    }
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
    fn negate(var: InstructionVars) -> u8 {
        match var {
            RP | InstructionVars::CC => !(0b11 << 4),
            InstructionVars::DDD | InstructionVars::ALU | InstructionVars::N => !(0b111 << 3),
            InstructionVars::SSS => !0b111,
        }
    }

    fn get(var: InstructionVars) -> u8 {
        !Self::negate(var)
    }
}
fn get_subset(instruction: u8, var: InstructionVars) -> u8 {
    match var {
        RP | InstructionVars::CC => (instruction & InstructionVars::get(var)) >> 4,
        InstructionVars::DDD | InstructionVars::ALU | InstructionVars::N => {
            (instruction & InstructionVars::get(var)) >> 3
        }
        InstructionVars::SSS => instruction & InstructionVars::get(var)
    }
}

fn lxi_rp_data(instruction: u8, intel8080: &mut Intel8080){
    let mem = &intel8080.memory;
    let pc = intel8080.program_counter as usize;
    let (data_low, data_high) = (mem[pc] as u16, mem[pc + 1] as u16);
    intel8080.program_counter += 2;
    let rp = get_subset(instruction, RP);
    let mut data: u16 = 0;
    data |= data_high << 8;
    data |= data_low;

    match rp {
        // https://en.wikipedia.org/wiki/Intel_8080#Instruction_set RP on the end
        0 => intel8080.set_register_pair(RegisterPair::BC, data),
        1 => intel8080.set_register_pair(RegisterPair::DE, data),
        2 => intel8080.set_register_pair(RegisterPair::HL, data),
        3 => intel8080.set_register_pair(RegisterPair::PSW, data),
        _ => panic!("Invalid RP value: {rp}")
    }
}