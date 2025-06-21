use crate::intel8080::hardware::Register::B;

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
    status: u8,
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
            status: 2,
            bc: 0,
            de: 0,
            hl: 0,
            psw: 0,
            registers: [0; REGISTER_NUMBER],
        }
    }
}

impl Intel8080 {
    pub fn get_paired_register(&self, register_pair: RegisterPair) -> u16{
        match register_pair {
            RegisterPair::BC => self.bc,
            RegisterPair::DE => self.de,
            RegisterPair::HL => self.hl,
            RegisterPair::PSW => self.psw
        }
    }

    pub fn set_register_pair(&mut self, register_pair: RegisterPair, value: u16) {
        let (first, second) = Self::get_paired_register_subsets(value);
        match register_pair {
            RegisterPair::BC => {
                self.set_register(B, first);
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
                self.set_register(Register::A, first);
                self.set_register(Register::M, second);
            }
        }
    }
    pub fn get_register(&self, register: Register) -> u8 {
        match register {
            Register::M => {
                let index = self.hl as usize;
                self.memory[index]
            }
            _ => {
                let (mut index, _, _) = Register::value(register);
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

        let (mut index, paired, first_byte) = Register::value(register);

        let paired_pointer = match paired {
            RegisterPair::PSW => &mut self.psw,
            RegisterPair::BC => &mut self.bc,
            RegisterPair::DE => &mut self.de,
            RegisterPair::HL => &mut self.hl,
        };

        Self::update_paired_register(paired_pointer, value as u16, first_byte);

        if let RegisterPair::PSW = paired {
            // register M
            if index == 6 {
                self.memory[self.hl as usize] = value;
                return
            }

            index = 6;
        }

        self.registers[index] = value;
    }

    pub fn set_status(&mut self, flags: StatusFlags, value: bool) {
        let offset = match flags {
            StatusFlags::S => 7,
            StatusFlags::Z => 6,
            StatusFlags::AC => 4,
            StatusFlags::P => 2,
            StatusFlags::C => 0
        };

        if value {
            self.status |= 1 << offset;
            return
        }

        self.status &= !(1 << offset);
    }
    fn update_paired_register(paired_register: &mut u16, value: u16, first_byte: bool) {
        let offset = if first_byte { 8 } else { 0 };
        let mask = !(0xF << offset);
        *paired_register &= mask;
        *paired_register |= value << offset;
    }

    fn get_paired_register_subsets(value: u16) -> (u8, u8) {
        let first_byte = (value >> 8) as u8;
        (first_byte, value as u8)
    }


}
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

pub enum RegisterPair {
    BC,
    DE,
    HL,
    PSW,
}

pub enum StatusFlags {
    S,
    Z,
    P,
    C,
    AC
}

impl Register {
    fn value(variation: Self) -> (usize, RegisterPair, bool) {
        match variation {
            Register::B => (0, RegisterPair::BC, true),
            Register::C => (1, RegisterPair::BC, false),
            Register::D => (2, RegisterPair::DE, true),
            Register::E => (3, RegisterPair::DE, false),
            Register::H => (4, RegisterPair::HL, true),
            Register::L => (5, RegisterPair::HL, false),
            Register::M => (6, RegisterPair::PSW, false),
            Register::A => (7, RegisterPair::PSW, true),
        }
    }
}

pub mod tests {
    use super::*;

    #[test]
    fn mutation_first_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::B, 0xFF);
        assert_eq!(cpu.bc, 0 | (0xFF << 8))
    }

    #[test]
    fn mutation_second_byte() {
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::L, 0x3);
        assert_eq!(cpu.hl, 0x3)
    }

    #[test]
    fn mutate_a(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::A, 200);
        assert_eq!(200, cpu.get_register(Register::A))
    }

    #[test]
    fn mutate_m_default(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::M, 200);
        assert_eq!(cpu.get_register(Register::M), 200)
    }

    #[test]
    fn mutate_hl_before_m(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::H, 100);
        cpu.set_register(Register::M, 200);
        assert_eq!(cpu.get_register(Register::M), 200);
    }

    #[test]
    fn mutate_hl_after_m(){
        let mut cpu = Intel8080::default();
        cpu.set_register(Register::M, 199);
        cpu.set_register(Register::L, 100);
        assert_ne!(199, cpu.get_register(Register::M))
    }

    #[test]
    fn set_status_true(){
        let mut cpu = Intel8080::default();
        cpu.set_status(StatusFlags::S, true);
        assert_eq!(130, cpu.status)
    }

    #[test]
    fn set_status_false(){
        let mut cpu = Intel8080::default();
        cpu.status = 255;
        cpu.set_status(StatusFlags::AC, false);
        assert_eq!(239, cpu.status)
    }
}
