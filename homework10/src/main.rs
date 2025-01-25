#![allow(dead_code)]
use std::env;
use std::fs;

mod bytecode;
use bytecode::Bytecode;

mod vm;
use vm::VM;

mod heap;

fn main() {
    let args: Vec<String> = env::args().collect();

    let file_path = &args[1];

    let raw_bytes = fs::read(file_path).expect("Unable to read the file.");

    let bytecode = Bytecode::from_raw_bytes(&raw_bytes);

    let mut vm = VM::new(bytecode);

    vm.run();
}
