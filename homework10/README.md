# Stack Based Virtual Machine

The objective of this exercise is to implement a stack-based virtual machine in
Rust. The virtual machine must include a garbage collector to reclaim
dynamically allocated memory that is no longer reachable by the program.

To test your virtual machine, you can use the [MiniML
compiler](http://www.softlab.ntua.gr/~zoepar/miniml.html), which compiles MiniML
programs into the VM bytecode described in this exercise.

## VM State

The VM state consists of a stack and a heap. The stack contains 32-bit words
that can be integers or pointers to a heap address. If the word is an integer,
then the 31 higher-order bits represent the integer, and the lowest order bit is
set to `1`. If the word is a pointer, then the 31 higher-order bits represent
the heap address, and the lowest order bit is `0`. The stack has a predefined
size and is empty when the VM starts executing.

The heap contains words and has a predefined size. It is a contiguous block of
memory, addressable at word-granularity, which is allocated when the VM starts
executing. 

## Memory Layout

Heap-allocated block consist of consecutive words of variable length, structured as follows:

- The first word is the *header* that contains metadata about the block:
  - The 23 higher-order bits represent the number of fields, `n`, in the block.
  - The next 8 bits store the *tag*, which provides additional information about the type of the block.
  - The **lowest-order bit** is always `0`  

- The next `n` words are the *fields* of the block.

Valid pointers to the heap always point to the header of a block. Below is a
schematic representation of a block in the heap:


```
Pointer to block
│
└─────▶  ┌────────────────────────────────┐
 Word 0: │       Size       │   Tag   │ 0 │
(Header) └────────────────────────────────┘
         31                 9         1   0
         ┌────────────────────────────────┐
 Word 1: │           Field 0              │
         └────────────────────────────────┘
         ┌────────────────────────────────┐
 Word 2: │           Field 1              │
         └────────────────────────────────┘
                       ...
         ┌────────────────────────────────┐
 Word n: │         Field (n-1)            │
         └────────────────────────────────┘
```


## Instruction Set

A program is a sequence of bytes representing a series of instructions. Each
byte is located at a specific address, ranging from `0` to `2^16 - 1` (allowing
a maximum program size of 65,536 bytes).

Each instruction consists of an *opcode*, optionally followed by one or more
bytes representing an integer *little-endian order*. If the integer is
signed, it is represented using *two's complement*.

The instruction set is detailed below, with the opcodes for each instruction
provided in parentheses.

### Control Flow

- **`halt` (`0x00`)**  
  Terminates the execution of the VM.

- **`jump` (`0x01`)**  
  Transfers control to the address given by the next two bytes of the program
  that represent an unsigned integer (in little-endian order).

- **`jnz` (`0x02`)**  
  Pops the top value from the stack. If the value is nonzero, it transfers the
  control to the address given by the next two bytes of the program that
  represent an unsigned integer (in little-endian order).

- **`jumpi` (`0x03`)**  
  Performs an indirect jump. The target address is stored at the top of the stack and is popped during execution. It is interpreted as an unsigned integer.

### Stack Manipulation

- **`dup` (`0x04`)**  
  Copies the value of the element at depth `i` in the stack is copied and pushed
  it to the top of the stack.  
  The value of `i` (unsigned) is given by the next byte of the program.  
  Depth 0 refers to the top of the stack.

- **`swap` (`0x05`)**  
  Swaps the top element of the stack with the element at depth `i`.  
  The value of `i` (unsigned) is given by the next byte of the program.  
  Depth 0 refers to the top of the stack.
  
- **`drop` (`0x06`)**  
  Pops and discards the top element of the stack.

- **`push4` (`0x07`)**  
  Pushes an integer onto the stack. The integer is signed and is given by the
  next 4 bytes of the program.

- **`push2` (`0x08`)**  
  Pushes an integer onto the stack. The integer is signed and is given by the next 2 bytes of the program.

- **`push1` (`0x09`)**  
  Pushes an integer onto the stack. The integer is signed and is given by the next byte of the program.

### Arithmetic Operations

- **`add` (`0x0A`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes the result of `a + b`.

- **`sub` (`0x0B`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes the result of `a - b`.

- **`mul` (`0x0C`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes the result of `a * b`.

- **`div` (`0x0D`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes the result of `a / b` (integer division).

- **`mod` (`0x0E`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes the result of `a % b` (modulo of integer division).

### Comparison Operations

- **`eq` (`0x0F`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes `1` if
  `a == b` is true, and `0` otherwise.

- **`ne` (`0x10`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes `1` if
  `a != b` is true, and `0` otherwise.

- **`lt` (`0x11`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes `1` if
  `a < b` is true, and `0` otherwise.

- **`gt` (`0x12`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes `1` if
  `a > b` is true, and `0` otherwise.

- **`le` (`0x13`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes `1` if
  `a <= b` is true, and `0` otherwise.

- **`ge` (`0x14`)**  
  Pops two values `a` and `b` from the stack (in this order), and pushes `1` if
  `a => b` is true, and `0` otherwise.

### Logical Operations

- **`not` (`0x15`)**  
  Pops the top of the stack, and pushes `1` if it is zero, and `0` otherwise.

- **`and` (`0x16`)**  
  Pops two values `a` and `b` from the stack, and pushes `1` if both of the
  values are nonzero and `0` otherwise.
  
- **`or` (`0x17`)**  
  Pops two values `a` and `b` from the stack, and pushes `1` if at least one of
  the values is nonzero and `0` otherwise.

### Input/Output

- **`input` (`0x18`)**  
  Reads a character from the standard input and pushes its ASCII code to the
  top of the stack.

- **`output` (`0x19`)**  
  Pops the top of the stack and outputs the corresponding ASCII character.

### Memory Operations

- **`alloc` (`0x1A`)**  
  Allocates a block of memory on the heap. It pops two elements from the stack
  that correspond to the tag and the size `n` of the block (in this order).
  Then, it pops `n` elements from the stack that are the fields of the block
  (the last popped is the first field), and allocates the memory block. It
  pushes the address of the new block to the top of the stack.
  
- **`load` (`0x1B`)**  
  Pops the top element from the stack, which should be a pointer to the heap,
  and pushed to the stack the value stored at offset `i` from this address. The
  offset `i` (unsigned) is given by the next four bytes of the program. 

## System Operations

- **`clock` (`0x1C`)**  
  Outputs the time elapsed from the beginning of execution in seconds, with
  a precision of 4 decimal places.


## Garbage Collection
The heap is garbage collected to ensure that blocks that are no longer reachable
are correctly deallocated. There are many garbage collection algorithms. The
exercise asks you to implement [Cheney's
algorithm](https://dl.acm.org/doi/pdf/10.1145/362790.362798). The algorithm is
described below. 

### Cheney's Semispace Collector
Cheney's algorithm is a semispace copying garbage collector that divides the
heap into two areas of the same size: the to-space and the from-space. The
allocator allocates new blocks contiguously in the from-space. When there no
sufficient space for an allocation in the from-space, the garbage collector is
triggered to reclaim memory. The algorithm proceeds as follows:

Cheney's algorithm describes a semispace copying collector that works as follows. 

It divides the heap into two spaces: the to-space and the from-space. New blocks
are allocated contiguously in the from-space. When there is no more available
space for allocation then the garbage collector is called and performs the
following. 

- It copies all pointers that are reference by the root set, which contains all
  the memory locations directly accessible by the program. The root sets is all
  the pointers in the stack of the VM. The algorithm scans the roots, and for
  each pointer in the root set:

  1. If the pointer points to the header of a block in the from-space then the
    block is copied to the from-space. The pointer is updated to hold the new
    address in the to-space. The old memory location is updated to hold a pointer
    to the new address of the block. This is called a *forwarding pointer* and
    signifies that the block has been moved to a new location.

    2. If the pointer points to the to-space, the block has already been moved,
    and no action is needed.

    3. If the pointer points to a word in the from-space that contains a pointer
    to the to-space (a forwarding pointer). The value of the pointer is updated
    to the address of the forwarding pointer.
    
- The algorithm scans each copied word in the to-space and applies the above
  steps. This process may result in more words being copied to the to-space,
  which must also be scanned.

After this process is completed, each reachable block has been copied to the
to-space, and every pointer to a reachable block has been updated with its new
address in the to-space. New blocks will now be allocated in the remaining space
of the to-space. The from-space contains no live memory blocks and will serve as
the to-space in the next garbage collection cycle.

## MiniML Compiler

The [MiniML compiler](http://www.softlab.ntua.gr/~zoepar/miniml.html) compiles
MiniML code into the bytecode of the VM. The web interface of the compiler
outputs the resulting binary in Base64 encoding.

In order to convert a file in Base64 encoding into a binary file, you can use the
`base64` Unix utility:

```bash
base64 -d -i tests/MiniML/test.base64 -o tests/MiniML/test.bin
```

where `test.base64` is the input file containing the base-64 encoding and
`tests/MiniML/test.bin` the output file.

### MiniML Memory Layout

Algebraic data types in MiniML are represented with the memory layout described
above. The tag is used to differentiate between different data type constructors. For example the list `1::2::3[]` is represented as:

```
Pointer
│ 
└─────▶┌────────────────────────────────┐      ┌────────────────────────────────┐      ┌────────────────────────────────┐      ┌────────────────────────────────┐
       │      Size = 2    │   Tag = 3   │ ┌───▶│      Size = 2    │   Tag = 3   │ ┌───▶│      Size = 2    │   Tag = 3   │ ┌───▶│      Size = 0    │   Tag = 2   │ 
       └────────────────────────────────┘ │    └────────────────────────────────┘ │    └────────────────────────────────┘ │    └────────────────────────────────┘
       ┌────────────────────────────────┐ │    ┌────────────────────────────────┐ │    ┌────────────────────────────────┐ │    
       │              1                 │ │    │              2                 │ │    │              3                 │ │    
       └────────────────────────────────┘ │    └────────────────────────────────┘ │    └────────────────────────────────┘ │    
       ┌────────────────────────────────┐ │    ┌────────────────────────────────┐ │    ┌────────────────────────────────┐ │    
       │    Pointer to list element     │─┘    │    Pointer to list element     │─┘    │    Pointer to list element     │─┘   
       └────────────────────────────────┘      └────────────────────────────────┘      └────────────────────────────────┘      
```

## Objectives (Total points: 100 + 20 bonus)

1. Write a bytecode interpreter for the virtual machine described here. This
   step does not require the implementation of a garbage collector. (60 points)

   The executable program takes a command-line argument, which is the file that
   contains the bytecode to be executed. Examples of usage are given below.  

2. Implement a garbage collector based on Cheney's semispace collector for the
   VM. (60 points)
 
## Building the Rust Project

To build the project in debug mode type

```
cargo build
```

```
cargo run test.bin
```

Note that by default, the above commands compile the code in debug mode. Adding
the flag `--release` builds the program in release mode. You can take advantage
of this to print debugging information when compiling in debug mode (see the
definition of function `print_state` in the provided code).

## Examples

The directory `examples` contains several MiniML programs that can be used to
test the VM. Some of them require garbage collection to run in the available
heap space.

For example, the bytecode, in Base64, for the program `foo.ml` is 

```
ATIABAAbAQAAAAQBGwIAAAAEAQcAAAAADwIhAAQBASYAByoAAAAFAQYFAQYFAQYFAQMISgAIAwAHDwAAAAkACQEaCQIJARoFAQMIUgAFAQGDAAkACUUZCWwZCWEZCXAZCXMZCWUZCWQZCSAZCXQZCWkZCW0ZCWUZCToZCSAZHAkKGQAEAAkAFAKTAAkABQELCS0ZCQAFAQQACQoOBQEJCg0FAQUCCQEKBAEClQAFAQYEAAK4AAHEAAkBCwUBCTAKGQGwAAYJChkDCQEYBAAJLRAC2wAJ/wUCBgYYBwAAAAAFAQQACQoPAgYBBAAJMBECMgEEAAk5EgIyAQkwCwUBCQEKGAHiAAYEAAkADwIyAQkBCQAFAgkBCwUDBAEMBQEJCgwFAgoFAgQACQAPAmkBARUBCUUZCXIZCXIZCW8ZCXIZCToZCSAZCWIZCWEZCWQZCSAZCW4ZCXUZCW0ZCWIZCWUZCXIZCQoZAAYGDAUBAw==
```

After decoding it to a binary file `foo.bin`, you can run the VM as follows.

```
> cargo run --release -- foo.bin
15
Elapsed time: 0.0000
```

## Further Instructions

To implement the `output` opcode, you may find useful the following code that
reads exactly one byte from the standard input. 

```rust
let mut buffer: [u8; 1] = [0; 1]; // A buffer to store one byte
io::stdin()
    .read_exact(&mut buffer)
    .expect("Failed to read input");
```

## Bug Reports

If you believe that you have found a bug in the MiniML compiler please report it
to the instructor.
