# Polymorphism

Rust supports **parametric polymorphism** through _generics_. A generic type is
an abstract type that can be instantiated with a concrete type later, when the
generic functionality is used. Generics provide a powerful abstraction that
allows you to write reusable and type-safe code, avoiding duplication of
functionality that is common to all types.

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
represent any type. Then, it takes an argument of type `T` and returns a result
of type `T`.

Function can be generic over more than one types. This is illustrated in the
following example.

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

Here's is an illustrative example of a generic enum that represents a cons list.
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
            Cons(x,_) =>   Some(x)
        }
    }

    // reverse a list in place
    fn rev(&mut self) {
        let mut rev: List<T> = List::Nil; // The reversed list
        let mut current: List<T> = std::mem::replace(self, List::Nil); // Take ownership of the current list

        while let Cons(value, mut next) = current {
            current = *next; // Move to the next node
            *next = rev ; // Reverse the link
            rev = Cons(value, next); // Update the reversed list
        }

        *self = rev; // Assign the reversed list back to `self`
    }

    fn new() -> List<T> {
        Nil
    }

    fn length(&self) -> u64 {
        match self {
            Nil => 0,
            Cons(_,l) => 1 + l.length()
        }
    }
}

fn main() {
    let mut l = list![1,2,3];

    l.rev();

    println!{"{:?}",l}
}
```

For the most part, the code covers concepts we have already covered. However, it
also introduces few Rust features that are worth more explanation:

- **Macros**
  We use the Rust [macro
  system](https://doc.rust-lang.org/reference/macros.html) to define notations
  for empty, singleton and nil list.


- **replace**
  We use the function
  [std::mem::replace](https://doc.rust-lang.org/std/mem/fn.replace.html) that
  moves the second argument (`List::Nil`) into the location provided by the
  first argument (`self`) and returns the original value of self. This allows us
  to take ownership of the list stored in `self`, while leaving an empty list
  (`Nil`) in its place.

- **while let** syntax
  This syntax combines pattern matching and while loops. The while loop will
  continue its execution for as long as the pattern (here `Cons(value, mut
  next)`) matches the value of the body.
