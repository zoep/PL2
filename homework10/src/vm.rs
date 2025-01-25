use crate::bytecode::{Bytecode, Opcode};
use crate::heap::{Heap, Word};

pub const STACK_SIZE: usize = 1 << 14;
pub const HEAP_SIZE: usize = 1 << 20;

/// The VM struct
pub struct VM {
    pub bytecode: Bytecode,
    stack: [Word; STACK_SIZE], // Fixed-size stack of words
    stack_ptr: usize,          // Stack pointer. Points to the next free slot in the stack.
    ip: usize,                 // Instruction pointer
    heap: Heap,                // The heap
}

impl VM {
    /// Create a new `VM` with the given bytecode
    pub fn new(bytecode: Bytecode) -> Self {
        VM {
            bytecode,
            stack: [Word::from_int(0); STACK_SIZE], // Initialize stack with zeroes
            stack_ptr: 0,
            ip: 0,
            heap: Heap::new(HEAP_SIZE), // The heap
        }
    }

    #[cfg(debug_assertions)]
    fn print_state(&self) {
        print!("Stack: ");
        for i in 0..self.stack_ptr {
            print!("| {:?} ", self.stack[i]);
        }
        println!("|");

        let opcode: Option<Opcode> = Opcode::from_u8(self.bytecode.instructions[self.ip]);

        println!("IP 0x{:X}: {:?}", self.ip, opcode);
    }

    #[cfg(not(debug_assertions))]
    fn print_state(&self) {}

    pub fn run(&mut self) {
        panic!("Implement me!")
    }
}
