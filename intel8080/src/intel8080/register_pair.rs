#[derive(PartialEq, Debug)]
pub enum RegisterPair {
    BC,
    DE,
    HL,
    PSW,
    SP,
}

impl RegisterPair {
    // some instructions use PSW and some SP for the value 3 so it's up to the caller to decide
    pub fn from_in(value: u8, fourth: RegisterPair) -> RegisterPair {
        if fourth != RegisterPair::SP && fourth != RegisterPair::PSW {
            panic!("Invalid register passed as fourth {:?}", fourth);
        }

        match value {
            0 => RegisterPair::BC,
            1 => RegisterPair::DE,
            2 => RegisterPair::HL,
            3 => fourth,
            _ => panic!("Invalid value for RP {}", value),
        }
    }
}
