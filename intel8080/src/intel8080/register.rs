// use crate::intel8080::register_pair::RegisterPair;
// 
// #[derive(Debug)]
// pub enum Register {
//     B,
//     C,
//     D,
//     E,
//     H,
//     L,
//     M,
//     A
// }
// impl Register {
//     pub fn get_pair_data(variation: &Self) -> (usize, RegisterPair, bool) {
//         match variation {
//             Register::B => (0, RegisterPair::BC, true),
//             Register::C => (1, RegisterPair::BC, false),
//             Register::D => (2, RegisterPair::DE, true),
//             Register::E => (3, RegisterPair::DE, false),
//             Register::H => (4, RegisterPair::HL, true),
//             Register::L => (5, RegisterPair::HL, false),
//             // Associated 10 so it will crash in case accessed
//             Register::FLAGS => (10, RegisterPair::PSW, false),
//             Register::A => (7, RegisterPair::PSW, true),
//             Register::M => panic!("M is not associated to a pair"),
//         }
//     }
// }
// 
// impl From<u8> for Register {
//     fn from(value: u8) -> Self {
//         match value {
//             0 => Register::B,
//             1 => Register::C,
//             2 => Register::D,
//             3 => Register::E,
//             4 => Register::H,
//             5 => Register::L,
//             6 => Register::M,
//             7 => Register::A,
//             _ => panic!("Got value higher than 7 for DDD {value}"),
//         }
//     }
// }