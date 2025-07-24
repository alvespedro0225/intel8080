use intel8080::Intel8080;
use intel8080::intel8080::hardware::{Register, RegisterPair};
use std::fs;
static mut TERMINATE: bool = false;
pub fn run_test(path: &str) {
    let mut intel8080 = Intel8080::default();
    intel8080.output = Box::new(output);
    let file = fs::read(path).expect("Error reading file");
    intel8080.program_counter = 0x100;
    intel8080.memory[0x100..0x100 + file.len()].clone_from_slice(&file);
    intel8080.memory[0] = 0xD3;
    intel8080.memory[5] = 0xD3;
    intel8080.memory[6] = 1;
    intel8080.memory[7] = 0xC9;

    unsafe {
        while !TERMINATE {
            intel8080.execute();
        }
    }
}

fn output(intel8080: &Intel8080, port: u8, _: u8) {
    if port != 1 {
        unsafe {
            TERMINATE = true;
        }
        return;
    }

    let reg_c = intel8080.get_register(&Register::C);

    if reg_c == 2 {
        print!("{}", intel8080.get_register(&Register::E));
    } else if reg_c == 9 {
        let mut i = intel8080.get_register_pair(&RegisterPair::DE) as usize;
        loop {
            
            print!("{}", char::from(intel8080.memory[i]));
            i += 1;

            if char::from(intel8080.memory[i]) == '$' {
                break;
            };

        }
    }
}
