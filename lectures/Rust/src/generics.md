# Polymorphism

Rust supports **parametric polymorphism** through _generics_. A generic type is
an abstract placeholder that gets instantiated with a concrete type when the
generic functionality is used. Generics provide a powerful abstraction for
writing reusable and type-safe code, eliminating duplication across types.

A very simple example of a polymorphic function is the identity function.

```rust,editable
fn id<T>(x:T) -> T {
    x
}

fn main() {
    println!("{}", id("Calling the id function"));
}
```

The syntax `<T>` indicates that the function is generic over type `T`, which can
represent any type. It takes an argument of type `T` and returns a value
of type `T`.

Functions can also be generic over multiple types. Here's an example:

```rust,editable
fn make_tuple<T,R>(x:T, y:R) -> (T,R) {
    (x, y)
}

fn main() {
    println!("{:?}", make_tuple(42,11));
}
```

## Cons List

Structs and enums can also be generic over various types.

Here's an illustrative example of a generic enum representing a cons list.
The example also illustrates macros in Rust.

```rust, editable
#[derive(Debug)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>)
}

use List::{Cons,Nil}; // To be able to use Cons and Nil without qualifying them.

// Define some macros for lists
macro_rules! list {
    // Empty list.
    [] => {
        Nil
    };

    // Singleton list.
    [ $head:expr ] => {
        Cons($head, Box::new(Nil))
    };

    // Recursive case: more than one item.
    [$head:expr, $($tail:expr),+] => {
        Cons($head, Box::new( list!($($tail),+) ))
    };
 }


impl<T> List<T> {

    // return a reference to the head of the list (if any) or nothing
    fn head(&self) -> Option<&T> {
        match self {
            Nil => None,
            Cons(x, _) => Some(x)
        }
    }

    // Reverse a list in place
    fn rev(&mut self) {
        let mut rev: List<T> = List::Nil; // The reversed list

         // Take ownership of the list in self
        let mut current: List<T> = std::mem::replace(self, List::Nil);

        // Note that we could not pattern-match self by value (match *self) because that would move out of &mut self.
        // Instead, we used std::mem::replace to swap self with an empty list, taking ownership of the original list.
        // Replace is implemented using unsafe code, but it provides a safe abstraction for this common pattern.

        while let Cons(value, mut next) = current {
            current = *next; // Move to the next node
            *next = rev; // Reverse the link
            rev = Cons(value, next); // Update the reversed list
        }

        *self = rev; // Assign the reversed list back to self
    }

    fn new() -> List<T> {
        Nil
    }

    fn length(&self) -> u64 {
        match self {
            Nil => 0,
            Cons(_, l) => 1 + l.length()
        }
    }
}

fn main() {
    let mut l = list![1, 2, 3];

    l.rev();

    println!("{:?}", l);
}
```

The code uses several concepts covered earlier, but also introduces key features
worth explaining:

- **Macros**
  We use the Rust [macro
  system](https://doc.rust-lang.org/reference/macros.html) to define convenient
  syntax for empty, singleton, and multi-element lists.


- **replace**
  We use [std::mem::replace](https://doc.rust-lang.org/std/mem/fn.replace.html)
  to swap the second argument (`List::Nil`) into the first argument (`self`)
  while returning the original value. This lets us take ownership of the list
  in `self` while leaving it with an empty list (`Nil`).

- **while let** syntax
  This syntax combines pattern matching with while loops. The loop continues
  as long as the pattern (here `Cons(value, mut next)`) matches the current value.
