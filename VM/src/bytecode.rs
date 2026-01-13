use std::collections::HashMap;

#[repr(u8)] // Store enum as a single byte
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
    Halt = 0x00,
    Jump = 0x01,
    Jnz = 0x02,
    Jumpi = 0x03,
    Dup = 0x04,
    Swap = 0x05,
    Drop = 0x06,
    Push4 = 0x07,
    Push2 = 0x08,
    Push1 = 0x09,
    Add = 0x0A,
    Sub = 0x0B,
    Mul = 0x0C,
    Div = 0x0D,
    Mod = 0x0E,
    Eq = 0x0F,
    Ne = 0x10,
    Lt = 0x11,
    Gt = 0x12,
    Le = 0x13,
    Ge = 0x14,
    Not = 0x15,
    And = 0x16,
    Or = 0x17,
    Input = 0x18,
    Output = 0x19,
    Alloc = 0x1A,
    Load = 0x1B,
    Clock = 0x1C,
}

impl Opcode {
    /// Convert a byte to an `Opcode`, if it matches a valid opcode.
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0x00 => Some(Opcode::Halt),
            0x01 => Some(Opcode::Jump),
            0x02 => Some(Opcode::Jnz),
            0x03 => Some(Opcode::Jumpi),
            0x04 => Some(Opcode::Dup),
            0x05 => Some(Opcode::Swap),
            0x06 => Some(Opcode::Drop),
            0x07 => Some(Opcode::Push4),
            0x08 => Some(Opcode::Push2),
            0x09 => Some(Opcode::Push1),
            0x0A => Some(Opcode::Add),
            0x0B => Some(Opcode::Sub),
            0x0C => Some(Opcode::Mul),
            0x0D => Some(Opcode::Div),
            0x0E => Some(Opcode::Mod),
            0x0F => Some(Opcode::Eq),
            0x10 => Some(Opcode::Ne),
            0x11 => Some(Opcode::Lt),
            0x12 => Some(Opcode::Gt),
            0x13 => Some(Opcode::Le),
            0x14 => Some(Opcode::Ge),
            0x15 => Some(Opcode::Not),
            0x16 => Some(Opcode::And),
            0x17 => Some(Opcode::Or),
            0x18 => Some(Opcode::Input),
            0x19 => Some(Opcode::Output),
            0x1A => Some(Opcode::Alloc),
            0x1B => Some(Opcode::Load),
            0x1C => Some(Opcode::Clock),
            _ => None,
        }
    }
}

pub struct Bytecode {
    pub instructions: Vec<u8>,
}

impl Bytecode {
    /// Parse raw bytes into a Bytecode object
    pub fn from_raw_bytes(raw_bytes: &[u8]) -> Self {
        Bytecode {
            instructions: raw_bytes.to_vec(),
        }
    }

    /// Disassemble the bytecode into a human-readable format
    pub fn disassemble(&self) -> Result<String, String> {
        let instrs = &self.instructions;
        let mut program = String::from("");

        // Add labels to the addresses that are jumped too
        let mut labels = HashMap::new();

        let mut i = 0;
        let mut cnt = 0;

        while i < instrs.len() {
            let opcode: Option<Opcode> = Opcode::from_u8(instrs[i]);

            match opcode {
                Some(Opcode::Jump) => {
                    let addr = (instrs[i + 2] as u16) << 8 | instrs[i + 1] as u16;
                    labels.insert(addr, format!("label{cnt}"));
                    i += 2;
                    cnt += 1;
                }
                Some(Opcode::Jnz) => {
                    let addr = (instrs[i + 2] as u16) << 8 | instrs[i + 1] as u16;
                    labels.insert(addr, format!("label{cnt}"));
                    i += 2;
                    cnt += 1;
                }
                Some(Opcode::Dup) => {
                    i += 1;
                }
                Some(Opcode::Swap) => {
                    i += 1;
                }
                Some(Opcode::Push4) => {
                    i += 4;
                }
                Some(Opcode::Push2) => {
                    i += 2;
                }
                Some(Opcode::Push1) => {
                    i += 1;
                }
                Some(_) => {}
                None => return Err(format!("Invalid opcode {} at addr {}", instrs[i], i)),
            }
            i += 1;
        }

        i = 0;

        while i < instrs.len() {
            if let Some(label) = labels.get(&(i as u16)) {
                program.push_str(&format!("{label}:\n"))
            }

            let opcode: Option<Opcode> = Opcode::from_u8(instrs[i]);

            // uncomment the following line if you want the address of the
            // instruction to be printed at the beginning of each line. May be
            // useful for debugging purposes.

            // program.push_str(&format!("0x{:X}: ", i));

            i += 1;

            match opcode {
                Some(Opcode::Halt) => program.push_str("Halt\n"),
                Some(Opcode::Jump) => {
                    let addr = (instrs[i + 1] as u16) << 8 | instrs[i] as u16;
                    match labels.get(&addr) {
                        Some(label) => program.push_str(&format!("Jump {label}\n")),
                        None => {
                            return Err(format!("Jump: Unknown jump address {addr}"));
                        }
                    }
                    i += 2;
                }
                Some(Opcode::Jnz) => {
                    let addr = (instrs[i + 1] as u16) << 8 | instrs[i] as u16;
                    match labels.get(&addr) {
                        Some(label) => program.push_str(&format!("Jnz {label}\n")),
                        None => {
                            return Err(format!("Jnz: Unknown jump address {addr}"));
                        }
                    }
                    i += 2;
                }
                Some(Opcode::Jumpi) => program.push_str("Jumpi\n"),

                Some(Opcode::Dup) => {
                    program.push_str(&format!("Dup {}\n", instrs[i]));
                    i += 1;
                }
                Some(Opcode::Swap) => {
                    program.push_str(&format!("Swap {}\n", instrs[i]));
                    i += 1;
                }
                Some(Opcode::Drop) => program.push_str("Drop\n"),
                Some(Opcode::Push4) => {
                    let lit = (instrs[i + 3] as u32) << 24
                        | (instrs[i + 2] as u32) << 16
                        | (instrs[i + 1] as u32) << 8
                        | (instrs[i] as u32);
                    program.push_str(&format!("Push4 {lit}\n"));
                    i += 4;
                }
                Some(Opcode::Push2) => {
                    let lit = (instrs[i + 1] as u16) << 8 | (instrs[i] as u16);
                    program.push_str(&format!("Push2 {lit}\n"));
                    i += 2;
                }
                Some(Opcode::Push1) => {
                    let lit = instrs[i] as u8;
                    program.push_str(&format!("Push1 {lit}\n"));
                    i += 1;
                }
                Some(Opcode::Add) => program.push_str("Add\n"),
                Some(Opcode::Sub) => program.push_str("Sub\n"),
                Some(Opcode::Mul) => program.push_str("Mul\n"),
                Some(Opcode::Div) => program.push_str("Div\n"),
                Some(Opcode::Mod) => program.push_str("Mod\n"),
                Some(Opcode::Eq) => program.push_str("Eq\n"),
                Some(Opcode::Ne) => program.push_str("Ne\n"),
                Some(Opcode::Lt) => program.push_str("Lt\n"),
                Some(Opcode::Gt) => program.push_str("Gt\n"),
                Some(Opcode::Le) => program.push_str("Le\n"),
                Some(Opcode::Ge) => program.push_str("Ge\n"),
                Some(Opcode::Not) => program.push_str("Not\n"),
                Some(Opcode::And) => program.push_str("And\n"),
                Some(Opcode::Or) => program.push_str("Or\n"),
                Some(Opcode::Input) => program.push_str("Input\n"),
                Some(Opcode::Output) => program.push_str("Output\n"),
                Some(Opcode::Clock) => program.push_str("Clock\n"),
                Some(Opcode::Alloc) => program.push_str("Alloc\n"),
                Some(Opcode::Load) => {
                    let lit = (instrs[i + 3] as u32) << 24
                        | (instrs[i + 2] as u32) << 16
                        | (instrs[i + 1] as u32) << 8
                        | (instrs[i] as u32);
                    program.push_str(&format!("Load {lit}\n"));
                    i += 4;
                }
                None => return Err(format!("Invalid opcode at addr {}", i - 1)),
            }
        }
        return Ok(program);
    }
}
