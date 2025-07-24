use crate::intel8080::ins::Instruction;
use crate::intel8080::register_pair::RegisterPair;
const MEMORY_SIZE: usize = 0x10000;
const REGISTER_NUMBER: usize = 7;
pub struct Intel8080 {
    pub memory: [u8; MEMORY_SIZE],
    registers: [u8; REGISTER_NUMBER],
    stack_pointer: u16,
    pub program_counter: u16,
    pub interrupt_enabled: bool,
    interrupt_instruction: u8,
    interrupt_pending: bool,
    pub halted: bool,
    // S | Z | 0 | AC | 0 | P | 1 |  C
    flags: u8,
    pub input: Box<dyn Fn(&Self, u8) -> u8>,
    pub output: Box<dyn Fn(&Self, u8, u8)>,
}
fn combine_into_u16(low: u8, high: u8) -> u16 {
    let low = low as u16;
    let high = high as u16;
    let mut value = high << 8;
    value ^= low;
    value
}
impl Default for Intel8080 {
    fn default() -> Self {
        Intel8080 {
            memory: [0; MEMORY_SIZE],
            stack_pointer: 0x100,
            program_counter: 0,
            flags: 2,
            registers: [0; REGISTER_NUMBER],
            interrupt_enabled: false,
            halted: false,
            interrupt_instruction: 0,
            interrupt_pending: false,
            input: Box::new(|_: &Intel8080, _: u8| 0),
            output: Box::new(|_: &Intel8080, _: u8, _: u8| {}),
        }
    }
}

impl Intel8080 {
    pub fn get_register_pair(&self, register_pair: &RegisterPair) -> u16 {
        match register_pair {
            RegisterPair::BC => combine_into_u16(
                self.get_register(&Register::C),
                self.get_register(&Register::B),
            ),
            RegisterPair::DE => combine_into_u16(
                self.get_register(&Register::E),
                self.get_register(&Register::D),
            ),
            RegisterPair::HL => combine_into_u16(
                self.get_register(&Register::L),
                self.get_register(&Register::H),
            ),
            RegisterPair::PSW => combine_into_u16(self.flags, self.get_register(&Register::A)),
            RegisterPair::SP => self.stack_pointer,
        }
    }

    pub fn set_register_pair(&mut self, register_pair: RegisterPair, value: u16) {
        let (low, high) = Self::get_register_pair_subsets(value);
        match register_pair {
            RegisterPair::BC => {
                self.set_register(Register::B, high);
                self.set_register(Register::C, low)
            }
            RegisterPair::DE => {
                self.set_register(Register::D, high);
                self.set_register(Register::E, low);
            }
            RegisterPair::HL => {
                self.set_register(Register::H, high);
                self.set_register(Register::L, low);
            }
            RegisterPair::PSW => {
                self.set_register(Register::A, high);
                self.flags = low;
            }
            RegisterPair::SP => self.stack_pointer = value,
        }
    }
    pub fn get_register(&self, register: &Register) -> u8 {
        if let Register::M = register {
            let index = self.get_register_pair(&RegisterPair::HL) as usize;
            return self.memory[index];
        }

        self.registers[register.get_index()]
    }

    pub fn set_register(&mut self, register: Register, value: u8) {
        if let Register::M = register {
            self.memory[self.get_register_pair(&RegisterPair::HL) as usize] = value;
            return;
        }

        self.registers[register.get_index()] = value;
    }

    pub fn get_flag(&self, flag: Flags) -> bool {
        match flag {
            Flags::S => (self.flags >> 7) == 1,
            Flags::Z => ((self.flags >> 6) & 1) == 1,
            Flags::HC => ((self.flags >> 4) & 1) == 1,
            Flags::P => ((self.flags >> 2) & 1) == 1,
            Flags::C => (self.flags & 1) == 1,
        }
    }

    pub fn set_flag(&mut self, flag: Flags, value: bool) {
        let offset = match flag {
            Flags::S => 7,
            Flags::Z => 6,
            Flags::HC => 4,
            Flags::P => 2,
            Flags::C => 0,
        };

        if value {
            self.flags |= 1 << offset;
            return;
        }

        self.flags &= !(1 << offset);
    }
    fn update_paired_register(paired_register: &mut u16, value: u16, high_byte: bool) {
        let offset = if high_byte { 8 } else { 0 };
        let mask = !(0xFF << offset);
        *paired_register &= mask;
        *paired_register |= value << offset;
    }

    fn get_register_pair_subsets(value: u16) -> (u8, u8) {
        let high = (value >> 8) as u8;
        (value as u8, high)
    }

    pub fn flip_carry(&mut self) {
        self.flags ^= 1;
    }
    pub fn set_zero_or_less(&mut self, result: u8) {
        match result {
            _ if result == 0 => {
                self.set_flag(Flags::Z, true);
                self.set_flag(Flags::S, false);
            }
            _ if (result >> 7) == 1 => {
                self.set_flag(Flags::Z, false);
                self.set_flag(Flags::S, true);
            }
            _ => {
                self.set_flag(Flags::Z, false);
                self.set_flag(Flags::S, false);
            }
        }
    }

    pub fn set_parity(&mut self, result: u8) {
        let mut count = 0;
        let mut result = result;

        while result > 0 {
            // https://www.techiedelight.com/brian-kernighans-algorithm-count-set-bits-integer/
            // Brian Kernighan algorithm
            count += 1;
            result = (result - 1) & result;
        }

        let is_pair = count & 1 == 0;
        self.set_flag(Flags::P, is_pair);
    }
    pub fn set_flags_add(&mut self, register: u8, added: u8, set_carry: bool) -> u8 {
        let result = u8::overflowing_add(register, added);
        let (result, of) = result;
        self.set_zero_or_less(result);
        self.set_parity(result);
        set_auxiliary_carry(self, register, added, result);
        if set_carry {
            self.set_flag(Flags::C, of)
        }
        return result;

        fn set_auxiliary_carry(slf: &mut Intel8080, register: u8, added: u8, result: u8) {
            // https://retrocomputing.stackexchange.com/questions/11262/can-someone-explain-this-algorithm-used-to-compute-the-auxiliary-carry-flag
            // the xor between register and added should be the same as the result, unless there was
            // a carry bit
            let aux_carry = ((register ^ added) & 0x10) != (result & 0x10);
            slf.set_flag(Flags::HC, aux_carry);
        }
    }

    pub fn set_flags_sub(&mut self, register: u8, sub: u8, set_carry: bool) -> u8 {
        let result = self.set_flags_add(register, u8::wrapping_add(!sub, 1), set_carry);
        if set_carry {
            if sub != 0 {
                self.flip_carry();
            }
        }
        result
    }

    pub fn execute(&mut self) {
        if self.interrupt_pending {
            self.handle_instruction(Instruction::from(self.interrupt_instruction));
            self.interrupt_enabled = false;
            self.interrupt_pending = false;
        } else if !self.halted {
            let opcode = self.memory[self.program_counter as usize];
            self.handle_instruction(Instruction::from(opcode));
        }
    }

    pub fn interrupt(&mut self, op_code: u8) {
        if self.interrupt_enabled {
            self.interrupt_instruction = op_code;
            self.interrupt_pending = true;
        }
    }

    fn pop_address(&mut self) -> u16 {
        // TODO deal with overflow
        let sp = &mut self.stack_pointer;
        let low = self.memory[*sp as usize] as u16;
        *sp += 1;
        let high = self.memory[*sp as usize] as u16;
        *sp += 1;
        let mut address = high << 8;
        address |= low;
        address
    }

    fn push_address(&mut self, address: u16) {
        // TODO deal with overflow
        let sp = &mut self.stack_pointer;
        let low = (address & 0xFF) as u8;
        let high = ((address >> 8) & 0xFF) as u8;
        *sp -= 1;
        self.memory[*sp as usize] = high;
        *sp -= 1;
        self.memory[*sp as usize] = low;
    }

    fn handle_instruction(&mut self, instruction: Instruction) {
        match instruction {
            Instruction::NOP => {}
            // PDF page 89
            Instruction::LXI(rp) => {
                let rp = RegisterPair::from_in(rp, RegisterPair::SP);
                let value = self.combine_next_instructions();
                self.set_register_pair(rp, value);
            }
            // PDF page 116
            Instruction::STAX(r) => {
                let r = RegisterPair::from_in(r, RegisterPair::SP);
                let acc = self.get_register(&Register::A);
                let index = self.get_register_pair(&r) as usize;
                self.memory[index] = acc;
            }
            // PDF page 87
            Instruction::LDAX(r) => {
                let r = RegisterPair::from_in(r, RegisterPair::SP);
                let index = self.get_register_pair(&r) as usize;
                let value = self.memory[index];
                self.set_register(Register::A, value);
            }
            // PDF page 80
            Instruction::INX(rp) => {
                let rp = RegisterPair::from_in(rp, RegisterPair::SP);
                let value = self.get_register_pair(&rp);
                self.set_register_pair(rp, u16::wrapping_add(value, 1));
            }
            // PDF page 76
            Instruction::DCX(rp) => {
                let rp = RegisterPair::from_in(rp, RegisterPair::SP);
                let value = self.get_register_pair(&rp);
                self.set_register_pair(rp, u16::wrapping_sub(value, 1))
            }
            // PDF page 79
            Instruction::INR(ddd) => {
                let ddd = Register::from(ddd);
                let value = self.get_register(&ddd);
                let (result, _) = self.add_u8(value, 1);
                self.set_half_carry(value, 1, result);
                self.set_register(ddd, result);
            }
            // PDF page 74
            Instruction::DCR(ddd) => {
                let ddd = Register::from(ddd);
                let value = self.get_register(&ddd);
                let added = complement(1);
                let (result, _) = self.add_u8(value, added);
                self.set_half_carry(value, added, result);
                self.set_register(ddd, result);
            }
            // PDF page 91
            Instruction::MVI(ddd) => {
                let ddd = Register::from(ddd);
                let value = self.get_next_byte();
                self.set_register(ddd, value);
            }
            // PDF page 74
            Instruction::DAD(rp) => {
                let rp = RegisterPair::from_in(rp, RegisterPair::SP);
                let rp = self.get_register_pair(&rp);
                let hl = self.get_register_pair(&RegisterPair::HL);
                let (result, of) = u16::overflowing_add(rp, hl);
                self.set_register_pair(RegisterPair::HL, result);
                self.set_flag(Flags::C, of);
            }
            // PDF page 103
            Instruction::RLC => {
                let acc = self.get_register(&Register::A);
                let carry = acc >> 7 == 1;
                self.set_flag(Flags::C, carry);
                self.set_register(Register::A, acc.rotate_left(1))
            }
            // PDF page 107
            Instruction::RRC => {
                let acc = self.get_register(&Register::A);
                let carry = (acc & 1) == 1;
                self.set_flag(Flags::C, carry);
                self.set_register(Register::A, acc.rotate_right(1));
            }
            // PDF page 100
            Instruction::RAL => {
                let mut acc = self.get_register(&Register::A);
                let carry = if self.get_flag(Flags::C) { 1 } else { 0 };
                let new_carry = acc >> 7 == 1;
                self.set_flag(Flags::C, new_carry);
                acc <<= 1;
                acc ^= carry;
                self.set_register(Register::A, acc);
            }
            // PDF page 100
            Instruction::RAR => {
                let mut acc = self.get_register(&Register::A);
                let carry = if self.get_flag(Flags::C) { 1 } else { 0 };
                let new_carry = acc & 1 == 1;
                self.set_flag(Flags::C, new_carry);
                acc >>= 1;
                acc ^= carry << 7;
                self.set_register(Register::A, acc);
            }
            // PDF page 114
            Instruction::SHLD => {
                let index = self.combine_next_instructions() as usize;
                self.memory[index] = self.get_register(&Register::L);
                self.memory[index + 1] = self.get_register(&Register::H);
            }
            // PDF page 88
            Instruction::LHLD => {
                let index = self.combine_next_instructions() as usize;
                self.set_register(Register::L, self.memory[index]);
                self.set_register(Register::H, self.memory[index + 1]);
            }
            // PDF page 73
            Instruction::DAA => {
                let mut acc = self.get_register(&Register::A);
                let right = acc & 0xF;

                if right > 9 {
                    acc += 6;
                    self.set_flag(Flags::HC, true);
                } else if self.get_flag(Flags::HC) {
                    acc += 6;
                    self.set_flag(Flags::HC, false);
                }

                let left = (acc & 0xF0) >> 4;

                if left > 9 {
                    acc = u8::wrapping_add(acc, 6 << 4);
                    self.set_flag(Flags::C, true);
                } else if self.get_flag(Flags::C) {
                    acc += 6 << 4;
                    self.set_flag(Flags::C, false);
                }

                self.set_register(Register::A, acc);
                self.set_parity(acc);
                self.set_zero_or_less(acc);
            }
            // PDF page 65
            Instruction::CMA => {
                let acc = self.get_register(&Register::A);
                self.set_register(Register::A, !acc);
            }
            // PDF page 116
            Instruction::STA => {
                let index = self.combine_next_instructions() as usize;
                self.memory[index] = self.get_register(&Register::A);
            }
            // PDF page 117
            Instruction::STC => {
                self.set_flag(Flags::C, true);
            }
            // PDF page 87
            Instruction::LDA => {
                let index = self.combine_next_instructions() as usize;
                let value = self.memory[index];
                self.set_register(Register::A, value);
            }
        }

        self.program_counter += 1;
    }

    fn add_u8(&mut self, accumulator: u8, added: u8) -> (u8, bool) {
        let result = u8::overflowing_add(accumulator, added);
        self.set_parity(result.0);
        self.set_zero_or_less(result.0);
        result
    }

    fn set_half_carry(&mut self, accumulator: u8, added: u8, result: u8) {
        let hc = accumulator ^ added ^ result & 0xF;
        self.set_flag(Flags::HC, hc > 0);
    }

    fn combine_next_instructions(&mut self) -> u16 {
        let pc = self.program_counter as usize;
        let (second, third) = (self.memory[pc + 1], self.memory[pc + 2]);
        self.program_counter += 2;
        combine_into_u16(second, third)
    }

    fn get_next_byte(&mut self) -> u8 {
        self.program_counter += 1;
        self.memory[self.program_counter as usize]
    }
}

fn complement(value: u8) -> u8 {
    u8::wrapping_add(!value, 1)
}
#[derive(Debug)]
pub enum Flags {
    S,
    Z,
    P,
    C,
    HC,
}

#[derive(Debug)]
pub enum Register {
    B,
    C,
    D,
    E,
    H,
    L,
    M,
    A,
}

impl From<u8> for Register {
    fn from(value: u8) -> Self {
        match value {
            0 => Register::B,
            1 => Register::C,
            2 => Register::D,
            3 => Register::E,
            4 => Register::H,
            5 => Register::L,
            6 => Register::M,
            7 => Register::A,
            _ => panic!("Invalid value for register: {value}"),
        }
    }
}

impl Register {
    pub fn get_index(&self) -> usize {
        match self {
            Register::B => 0,
            Register::C => 1,
            Register::D => 2,
            Register::E => 3,
            Register::H => 4,
            Register::L => 5,
            Register::A => 6,
            Register::M => panic!("No index associated to register M"),
        }
    }
}
#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn set_high_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::B, 0xFF);
        assert_eq!(cpu.get_register_pair(&RegisterPair::BC), 0 | (0xFF << 8));
    }

    #[test]
    fn set_low_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::L, 0x3);
        assert_eq!(cpu.get_register_pair(&RegisterPair::HL), 0x3);
    }

    #[test]
    fn set_a() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 200);
        assert_eq!(200, cpu.get_register(&Register::A));
    }

    #[test]
    fn set_m_default() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 200);
        assert_eq!(cpu.get_register(&Register::A), 200);
    }

    #[test]
    fn set_hl_before_m() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::H, 100);
        cpu.set_register(Register::M, 200);
        assert_eq!(cpu.get_register(&Register::M), 200);
    }

    #[test]
    fn set_hl_after_m() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::M, 199);
        cpu.set_register(Register::L, 100);
        assert_ne!(199, cpu.get_register(&Register::M));
    }

    #[test]
    fn set_flag_true() {
        let mut cpu = Intel8080::default();
        cpu.set_flag(Flags::S, true);
        assert_eq!(130, cpu.flags);
    }

    #[test]
    fn set_flag_false() {
        let mut cpu = Intel8080::default();
        cpu.flags = 255;
        cpu.set_flag(Flags::HC, false);
        assert_eq!(239, cpu.flags);
    }

    #[test]
    fn set_register_pair() {
        let mut cpu = Intel8080::default();
        cpu.set_register_pair(RegisterPair::PSW, 0xBC10);
        assert_eq!(cpu.get_register_pair(&RegisterPair::PSW), 0xBC10);
    }

    #[test]
    fn set_register_pair_high_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register_pair(RegisterPair::HL, 0x13FF);
        assert_eq!(cpu.get_register(&Register::H), 0x13);
    }

    #[test]
    fn set_register_pair_low_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register_pair(RegisterPair::BC, 0xFCBA);
        assert_eq!(cpu.get_register(&Register::C), 0xBA);
    }

    #[test]
    fn set_flag_addition_negative() {
        let mut cpu = Intel8080::default();
        cpu.set_flags_add(0b10101000, 1, false);
        assert_eq!(cpu.flags, 0b10000110)
    }

    #[test]
    fn set_flag_addition_positive() {
        let mut cpu = Intel8080::default();
        cpu.set_flags_add(0b00101100, 1, false);
        assert_eq!(cpu.flags, 0b00000110)
    }

    #[test]
    fn set_flag_addition_zero() {
        let mut cpu = Intel8080::default();
        cpu.set_flags_add(255, 1, true);
        assert_eq!(cpu.flags, 0b01010111);
    }
}
