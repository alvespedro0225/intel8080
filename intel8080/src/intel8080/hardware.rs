use crate::intel8080::instructions;
const MEMORY_SIZE: usize = 2usize.pow(16);
const REGISTER_NUMBER: usize = 7;

pub struct Intel8080 {
    // https://web.archive.org/web/20240118230903/http://www.emulator101.com/memory-maps.html
    // ROM:
    // 0x0000 => 0x07FF invaders.h
    // 0x0800 => 0x0FFF invaders.g
    // 0x1000 => 0x17FF invaders.f
    // 0x1800 => 0x1FFF invaders.e
    // RAM:
    // 0x2000 => 0x23FF Work RAM
    // 0x2400 => 0x3FFF Video RAM
    // 0x4000 =-> ... RAM mirror
    pub memory: [u8; MEMORY_SIZE],
    registers: [u8; REGISTER_NUMBER],
    pub stack_pointer: u16,
    pub program_counter: u16,
    // S | Z | 0 | AC | 0 | P | 1 |  C
    flags: u8,
    bc: u16,
    de: u16,
    hl: u16,
    psw: u16, // accumulator and flags register together
}

impl Default for Intel8080 {
    fn default() -> Self {
        Intel8080 {
            memory: [0; MEMORY_SIZE],
            stack_pointer: 0,
            program_counter: 0,
            flags: 2,
            bc: 0,
            de: 0,
            hl: 0,
            psw: 0,
            registers: [0; REGISTER_NUMBER],
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
            RegisterPair::PSW => self.psw,
            RegisterPair::SP => self.stack_pointer,
        }
    }

    pub fn set_register_pair(&mut self, register_pair: RegisterPair, value: u16) {
        let (first, second) = Self::get_register_pair_subsets(value);
        match register_pair {
            RegisterPair::BC => {
                self.set_register(Register::B, first);
                self.set_register(Register::C, second)
            }
            RegisterPair::DE => {
                self.set_register(Register::D, first);
                self.set_register(Register::E, second);
            }
            RegisterPair::HL => {
                self.set_register(Register::H, first);
                self.set_register(Register::L, second);
            }
            RegisterPair::PSW => {
                self.set_register(Register::FLAGS, first);
                self.set_register(Register::A, second);
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

    pub fn get_flag(&self, flag: StatusFlags) -> bool{
        match flag {
            StatusFlags::S => (self.flags >> 7) == 1,
            StatusFlags::Z => ((self.flags >> 6) & 1) == 1,
            StatusFlags::AC => ((self.flags >> 4) & 1) == 1,
            StatusFlags::P => ((self.flags >> 2) & 1) == 1,
            StatusFlags::C => (self.flags & 1) == 1
        }
    }

    pub fn set_flag(&mut self, flag: StatusFlags, value: bool) {
        let offset = match flag {
            StatusFlags::S => 7,
            StatusFlags::Z => 6,
            StatusFlags::AC => 4,
            StatusFlags::P => 2,
            StatusFlags::C => 0,
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
        let first_byte = (value >> 8) as u8;
        (first_byte, value as u8)
    }

    pub fn set_status_add(&mut self, register: u8, add: u8) {
        let result = u8::overflowing_add(register, add);
        let (result, _) = result;
        set_zero_or_less(self, result);
        set_auxiliary_carry(self, register, add, result);
        set_parity(self, result);

        fn set_zero_or_less(slf: &mut Intel8080, result: u8) {
            match result {
                _ if result == 0 => {
                    slf.set_flag(StatusFlags::Z, true);
                    slf.set_flag(StatusFlags::S, false);
                }
                _ if (result >> 7) == 1 => {
                    slf.set_flag(StatusFlags::Z, false);
                    slf.set_flag(StatusFlags::S, true);
                }
                _ => {
                    slf.set_flag(StatusFlags::Z, false);
                    slf.set_flag(StatusFlags::S, false);
                }
            }
        }

        fn set_auxiliary_carry(slf: &mut Intel8080, register: u8, added: u8, result: u8) {
            // https://retrocomputing.stackexchange.com/questions/11262/can-someone-explain-this-algorithm-used-to-compute-the-auxiliary-carry-flag
            // the xor between register and added should be the same as the result, unless there was
            // a carry bit
            let aux_carry = ((register ^ added) & 0x10) != (result & 0x10);
            slf.set_flag(StatusFlags::AC, aux_carry);
        }
        
        fn set_parity(slf: &mut Intel8080, result: u8) {
            let mut count = 0;
            let mut result = result;

            while result > 0 {
                // https://www.techiedelight.com/brian-kernighans-algorithm-count-set-bits-integer/
                // Brian Kernighan algorithm
                count += 1;
                result = (result - 1) & result;
            }

            let is_pair = count & 1 == 0;
            slf.set_flag(StatusFlags::P, is_pair);
        }
    }
    
    pub fn set_status_sub(&mut self, register: u8, sub:u8){
        self.set_status_add(register, !sub + 1);
        // flips AC flag
        self.flags ^= 0b00010000;
    }
    
    pub fn execute_next_instruction(&mut self){
        let instruction = self.memory[self.program_counter as usize];
        instructions::handle_instruction(instruction, self)
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
pub enum StatusFlags {
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
            Register::FLAGS => (10, RegisterPair::PSW, true),
            Register::A => (7, RegisterPair::PSW, false),
            Register::M => panic!("M is not associated to a pair"),
        }
    }
    
    pub fn get_ddd(ddd: u8) -> Register {
        match ddd {
            0 => Register::B,
            1 => Register::C,
            2 => Register::D,
            3 => Register::E,
            4 => Register::H,
            5 => Register::L,
            6 => Register::M,
            7 => Register::A,
            _ => panic!("Got value higher than 7 for DDD {ddd}"),
        }
    }
}

impl RegisterPair {
    pub fn get_rp(rp: u8) -> RegisterPair{
        match rp {
            0 => RegisterPair::BC,
            1 => RegisterPair::DE,
            2 => RegisterPair::HL,
            3 => RegisterPair::SP,
            _ => panic!("{rp} not associated with a register pair")
        }
    }
}

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
    fn set_status_true() {
        let mut cpu = Intel8080::default();
        cpu.set_flag(StatusFlags::S, true);
        assert_eq!(130, cpu.flags);
    }

    #[test]
    fn set_status_false() {
        let mut cpu = Intel8080::default();
        cpu.flags = 255;
        cpu.set_flag(StatusFlags::AC, false);
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
    fn set_status_addition_negative() {
        let mut cpu = Intel8080::default();
        cpu.set_status_add(0b10101000, 1);
        assert_eq!(cpu.flags, 0b10000110)
    }

    #[test]
    fn set_status_addition_positive() {
        let mut cpu = Intel8080::default();
        cpu.set_status_add(0b00101100, 1);
        assert_eq!(cpu.flags, 0b00000110)
    }

    #[test]
    fn set_status_addition_zero() {
        let mut cpu = Intel8080::default();
        cpu.set_status_add(255, 1);
        assert_eq!(cpu.flags, 0b01010111);
    }
}
