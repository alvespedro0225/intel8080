use crate::intel8080::instructions;
const MEMORY_SIZE: usize = 0x10000;
const REGISTER_NUMBER: usize = 7;
const PORT_SIZE: usize = 256;

pub struct Intel8080 {
    pub terminate: bool,
    pub memory: [u8; MEMORY_SIZE],
    registers: [u8; REGISTER_NUMBER],
    pub ports: [u8; PORT_SIZE],
    stack_pointer: u16,
    pub program_counter: u16,
    pub interrupt_enabled: bool,
    interrupt_instruction: u8,
    interrupt_pending: bool,
    pub halted: bool,
    // S | Z | 0 | AC | 0 | P | 1 |  C
    flags: u8,
    bc: u16,
    de: u16,
    hl: u16,
    psw: u16, // accumulator and flags register together,
    pub input: Box<dyn Fn(&Self, u8) -> u8>,
    pub output: Box<dyn Fn(&Self, u8, u8)>,
}

impl Default for Intel8080 {
    fn default() -> Self {
        Intel8080 {
            terminate: false,
            memory: [0; MEMORY_SIZE],
            ports: [0; PORT_SIZE],
            stack_pointer: 0x100,
            program_counter: 0,
            flags: 2,
            bc: 0,
            de: 0,
            hl: 0,
            psw: 0,
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
    pub fn get_flags(&self) -> u8 {
        self.flags
    }

    pub fn get_register_pair(&self, register_pair: &RegisterPair) -> u16 {
        match register_pair {
            RegisterPair::BC => self.bc,
            RegisterPair::DE => self.de,
            RegisterPair::HL => self.hl,
            RegisterPair::PSW => {
                let low = self.get_register(&Register::FLAGS) as u16;
                let high = self.get_register(&Register::A) as u16;
                low | (high << 8)
            },
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
                self.set_register(Register::FLAGS, low);
            }
            RegisterPair::SP => self.stack_pointer = value,
        }
    }
    pub fn get_register(&self, register: &Register) -> u8 {
        match register {
            Register::M => {
                let index = self.hl as usize;
                self.memory[index]
            }
            Register::FLAGS => {
                self.flags
            }
            _ => {
                let (mut index, _, _) = Register::get_pair_data(register);
                // register A is 7 (0b111) in instruction but index 6 on the struct since M is not stored,
                // but referenced
                if index == 7 {
                    index = 6;
                }

                self.registers[index]
            }
        }
    }

    pub fn set_register(&mut self, register: Register, value: u8) {
        if let Register::M = register {
            self.memory[self.hl as usize] = value;
            return;
        }

        let (mut index, paired, high_byte) = Register::get_pair_data(&register);

        let paired_pointer = match &paired {
            RegisterPair::PSW => &mut self.psw,
            RegisterPair::BC => &mut self.bc,
            RegisterPair::DE => &mut self.de,
            RegisterPair::HL => &mut self.hl,
            RegisterPair::SP => panic!("Got SP from a register reference."),
        };

        Self::update_paired_register(paired_pointer, value as u16, high_byte);

        if let RegisterPair::PSW = paired {
            // register M
            if index != 7 {
                self.flags = value;
                return;
            }

            index = 6;
        }

        self.registers[index] = value;
    }

    pub fn get_flag(&self, flag: Flags) -> bool {
        match flag {
            Flags::S => (self.flags >> 7) == 1,
            Flags::Z => ((self.flags >> 6) & 1) == 1,
            Flags::AC => ((self.flags >> 4) & 1) == 1,
            Flags::P => ((self.flags >> 2) & 1) == 1,
            Flags::C => (self.flags & 1) == 1,
        }
    }

    pub fn set_flag(&mut self, flag: Flags, value: bool) {
        let offset = match flag {
            Flags::S => 7,
            Flags::Z => 6,
            Flags::AC => 4,
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
            slf.set_flag(Flags::AC, aux_carry);
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
            instructions::handle_instruction(self.interrupt_instruction, self);
            self.interrupt_enabled = false;
            self.interrupt_pending = false;
        } else if !self.halted {
            let instruction = self.memory[self.program_counter as usize];
            instructions::handle_instruction(instruction, self)
        }
    }

    pub fn interrupt(&mut self, op_code: u8) {
        if self.interrupt_enabled {
            self.interrupt_instruction = op_code;
            self.interrupt_pending = true;
        }
    }

    pub fn pop_address(&mut self) -> u16 {
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

    pub fn push_address(&mut self, address: u16) {
        // TODO deal with overflow
        let sp = &mut self.stack_pointer;
        let low = (address & 0xFF) as u8;
        let high = ((address >> 8) & 0xFF) as u8;
        *sp -= 1;
        self.memory[*sp as usize] = high;
        *sp -= 1;
        self.memory[*sp as usize] = low;
    }
    
}

#[derive(Debug)]
pub enum RegisterPair {
    BC,
    DE,
    HL,
    PSW,
    SP,
}
#[derive(Debug)]
pub enum Flags {
    S,
    Z,
    P,
    C,
    AC,
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
    FLAGS,
}

impl Register {
    fn get_pair_data(variation: &Self) -> (usize, RegisterPair, bool) {
        match variation {
            Register::B => (0, RegisterPair::BC, true),
            Register::C => (1, RegisterPair::BC, false),
            Register::D => (2, RegisterPair::DE, true),
            Register::E => (3, RegisterPair::DE, false),
            Register::H => (4, RegisterPair::HL, true),
            Register::L => (5, RegisterPair::HL, false),
            // Associated 10 so it will crash in case accessed
            Register::FLAGS => (10, RegisterPair::PSW, false),
            Register::A => (7, RegisterPair::PSW, true),
            Register::M => panic!("M is not associated to a pair"),
        }
    }
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
            _ => panic!("Got value higher than 7 for DDD {value}"),
        }
    }
}

impl RegisterPair {
    /// like the "From" trait, but makes the caller choose between SP/PSW  
    pub fn get_register(value: u8, fourth: RegisterPair) -> Self {
        match value {
            0 => RegisterPair::BC,
            1 => RegisterPair::DE,
            2 => RegisterPair::HL,
            3 => fourth,
            _ => panic!("{value} not associated with a register pair"),
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
        assert_eq!(cpu.bc, 0 | (0xFF << 8));
    }

    #[test]
    fn set_low_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::L, 0x3);
        assert_eq!(cpu.hl, 0x3);
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
        cpu.set_flag(Flags::AC, false);
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
