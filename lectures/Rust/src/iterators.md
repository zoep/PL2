# Iterators

Rust provides an iterator abstraction that enables traversing over collections
like arrays, vectors, or custom types. Iterators implement a trait called
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html).

```rust, ignore
pub trait Iterator {
    type Item; // an associated trait type

    fn next(&mut self) -> Option<Self::Item>;

    // 75 hidden methods with default implementations
}
```

The iterator has a method called `next`, that when called return a value of type
`Item`. This type is defined inside the trait. This is called an  _associated
type_ and it is a placeholder that methods had use in the signatures.
Implementations of the trait tie this type to a concrete definition.

Using the `Iterator trait`, we can define a simple counter. 

```rust, editable
/// A Counter iterator that generates numbers in a range [start, end).
pub struct Counter {
    current: i32,
    end: i32,
}

impl Counter {
    /// Creates a new Counter iterator.
    pub fn new(start: i32, end: i32) -> Self {
        Counter {
            current: start,
            end,
        }
    }
}

impl Iterator for Counter {
    type Item = i32;
    /// Advances the iterator and returns the next value.
    /// Returns `None` when the current value reaches or exceeds the end value.
    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.end {
            None
        } else {
            let value = self.current;
            self.current += 1; // Increment by 1
            Some(value)
        }
    }
}

fn main() {
    // Create a Counter that generates numbers from 1 to 5 (exclusive).
    let counter = Counter::new(1, 5);

    // the for ... in ... construct can be used to iterate over an iterator.
    for value in counter {
        println!("{}", value);
    }
}
```

## Creating Iterators

A collection for a type `T` typically provide three methods to create an
iterator:

- `iter()`, which iterates over `&T`. This iterator gives read-only access to
  items. 
- `iter_mut()`, which iterates over `&mut T`. This iterator allows for in-place
  modification of items. 
- `into_iter()`, which iterates over `T`. This iterator consumes the collection
   and yields owned values.

The way in which a type is converted to an iterator is specified my implementing
the `IntoIterator` trait for a type. This has the following definition.

```rust, ignore
pub trait IntoIterator {
    type Item; // associated types for iterator item

    type IntoIter: Iterator<Item = Self::Item>; // associated iterator type

    // Conversion to an iterator
    fn into_iter(self) -> Self::IntoIter;
}
```

Notice the syntax `<Item = Self::Item>`. This specifies that the associated type
for the iterator is tied to `Self::Item`. 

The `Vec` implements three different `IntoIterator` traits, corresponding to the three methods for creating iterators:

- immutable borrow: `impl<'a, T> IntoIterator for &'a Vec<T>`
- mutable borrow: `impl<'a, T> IntoIterator for &'a mut Vec<T>`
- owned: `impl<T> IntoIterator for Vec<T>`

Below are some examples of usage of the three kinds of iterators. 

### Immutable Borrows

```rust, editable
fn main() {
    let numbers = vec![1, 2, 3, 4, 5];

    // Iterate using iter()
    for num in numbers.iter() {
        println!("Immutable borrow: {}", num);
    }

    // Original vector remains unchanged
    println!("Original vector: {:?}", numbers);
}
```

### Mutable Borrows

```rust, editable
fn main() {
    let mut numbers = vec![1, 2, 3];

    // Using IntoIterator for &mut Vec<T>
    let iter_mut = numbers.iter_mut(); // Equivalent to (&mut numbers).into_iter();
    for num in iter_mut {
        *num += 1;
    }

    println!("Modified vector: {:?}", numbers);
}
```

### Owned Values
```rust, editable
fn main() {
    let names = vec![
        "alice".to_string(),
        "bob".to_string(),
        "charlie".to_string(),
    ];

    // Create a new vector to hold the transformed values
    let mut uppercase_names = Vec::new();

    // Use a for loop with into_iter to consume `names`
    for name in names.into_iter() {
        // Transform the name and push it into the new vector
        uppercase_names.push(name.to_uppercase());
    }
    // `names` is no longer accessible here

    println!("Uppercase Names: {:?}", uppercase_names);
}
```

## Closures
Generally, functions in Rust written with `fn` cannot access their environment,
even though they can be nested. Rust support writing anonymous functions that
can captured their environment, i.e., closures. 

For example, a closure with two parameters `x` and `y`, that adds the two
parameters and a captured variable `z` is written `|x, y| x + y + z`. 


```rust,editable
fn main() {
    let outer_var = 42;

    // Write some closures
    let closure_annotated = |x: i32, y: i32| -> i32 { x + y + outer_var };
    let closure_inferred = |x, y| x + y + outer_var;

    // Call the closures
    println!("closure_annotated: {}", closure_annotated(1, 2));
    println!("closure_inferred: {}", closure_inferred(3, 4));
}
```

Note that closures cannot be polymorphic. The following example fails.

```rust,editable
fn main() {
    let id = |x| x;

    println!("Call 1: {}", id("hello"));
    println!("Call 2: {}", id(3));
}
```

Say that we want to write a higher-order function in Rust that takes a closure
as a a parameter. What type shall we give it?

The type of closures in Rust is not expressible in source-level syntax. Think of
it as a struct type of a closure, that explicitly contains the types of the
captured variables. 

Using a closure as a function parameter requires generics. For example, we could
do:

```rust, editable 
// `F` must be generic.
fn apply<F>(f: F) {
    f();
}

fn main() {
    let x = 42;

    let print = || println!("{}", x);

    apply(print);
}
```

However, the code still doesn't compile. We should declare that a generic type is
callable. This is done via the traits `Fn`, `FnMut`, or `FnOnce`. These specify
how can a closure be called and they differ on their  `self` type.

These trait put some restriction on how a closure can be called, depending on
what environment variables it captures. This ensures that ownership and
borrowing rules are not violated. The following table summarizes the differences
of each trait. 


| **Trait**         | **`self` Type**                     | **Code**                                     | **Call Site**                                |
|--------------------|-------------------------------------|---------------------------------------------|---------------------------------------------|
| `FnOnce`          | `self`                             | Can capture owned values and mutable references | Can only call the method once               |
| `FnMut`           | `&mut self`                        | Can capture mutable references              | Can call many times, only with unique access |
| `Fn`              | `&self`                            | Can capture immutable references            | Can call many times, with no restrictions    |



All of Rust's callable traits-—`Fn`, `FnMut`, and `FnOnce`-—have two associated
types: `Args`, which represents the types of arguments the callable takes
(expressed as a tuple), and `Output`, which represents the return type of the
callable. When writing trait bounds we can specify these with a special syntax
that resembles function types: `Fn(i32) -> i32` denotes a closure that takes as
input an `i32` and returns an `i32`.

For a more in depth explanation of how closures work in rust you can read
[this](https://huonw.github.io/blog/2015/05/finding-closure-in-rust/).

Here's the above example, adapted so that it compiles. 

```rust, editable 
// `F` must be generic.
fn apply<F>(f: F)
where
    F: Fn() -> (),
{
    f();
}

fn main() {
    let x = 42;

    let print = || println!("{}", x);

    apply(print);
}
```

### Higher-order Functions on Iterators
The `Iterator` trait provides a few higher-order abstraction inspired from
functional programming. Some common higher-order iterator methods are `map`,
`filter` and `fold`. These are all default methods of the `Iterator` trait, so
they are provided for free. Let's look at how the work. 

Here's an example from the standard library 

```rust, editable 
fn main() {
    let a = vec![1, 2, 3];

    let doubled: Vec<i32> = a
        .iter() // convert vec into an iterator
        .map(|&x| x * 2) // call map
        .collect(); // reconstruct an iterator

    println!("{:?}", doubled)
}
```

As an exercise try to change the `iter` method to `into_iter` to take ownership
of the vector and `iter_mut` to modify the vector in place. 

Below are some more examples. 

```rust, editable 
fn main() {
    let numbers = vec![1, 2, 3, 4, 5, 6];

    // Use fold to calculate the sum of all elements
    let sum = numbers.iter().fold(0, |acc, &x| acc + x);

    println!("Sum: {}", sum); // Output: Sum: 21
}
```


```rust, editable
fn main() {
    let numbers = vec![1, 2, 3, 4, 5, 6];

    // Filter out only even numbers and collect them into a new vector
    let even_numbers: Vec<i32> = numbers.into_iter().filter(|&x| x % 2 == 0).collect();

    println!("Even numbers: {:?}", even_numbers); // Output: [2, 4, 6]
}
```

## Iterators Example: Cons List
