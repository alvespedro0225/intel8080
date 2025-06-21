use intel8080::instructions;
use intel8080::hardware;
mod intel8080;

fn init(){
    let mut intel8080 = hardware::Intel8080::default();
    instructions::handle_instruction(0xFF, &mut intel8080);
}