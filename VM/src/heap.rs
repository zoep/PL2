use std::fmt::{self, Debug};

#[derive(Clone, Copy)]
pub struct Word {
    w: i32,
}

impl Word {
    pub fn from_pointer(ptr: usize) -> Word {
        Word {
            w: (ptr as i32) << 1 | 0,
        }
    }

    pub fn from_int(int: i32) -> Word {
        Word { w: int << 1 | 1 }
    }

    pub fn to_pointer(self) -> usize {
        (self.w >> 1) as usize
    }

    pub fn to_int(self) -> i32 {
        self.w >> 1
    }

    fn is_pointer(self) -> bool {
        (self.w & 1) == 0
    }
}

impl Debug for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_pointer() {
            write!(f, "Ptr({})", self.to_pointer())
        } else {
            write!(f, "Int({})", self.to_int())
        }
    }
}

pub struct Heap {
    pub heap: Box<[Word]>,
    // FILL IN HERE
}

impl Heap {
    pub fn new(total_words: usize) -> Self {
        let vec = vec![Word { w: 0 }; total_words];
        let memory = vec.into_boxed_slice();

        Heap {
            heap: memory,
            // FILL IN HERE
        }
    }

    // allocate a new block
    pub fn alloc(&mut self, _size: usize, _tag: u8, _words: &[Word]) -> Option<usize> {
        panic!("Implement me!")
    }
}
