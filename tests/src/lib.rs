use std::fs;
use intel8080;
use intel8080::Intel8080;

pub fn run_test(intel8080: &mut Intel8080, path: &str){
    let file = fs::read(path).expect("Error reading file");
    intel8080.program_counter = 0x100;
    intel8080.memory[0x100..0x100 + file.len()].clone_from_slice(&file);
    intel8080.memory[0] = 0xD3;
    intel8080.memory[5] = 0xD3;
    intel8080.memory[6] = 1;
    intel8080.memory[7] = 0xC9;
}