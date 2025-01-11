# Traits

In Rust, traits are a way to define shared functionality across different types.
A trait specifies a set of methods that the implementing type must provide. They
are similar, but not the same, to interfaces, in languages like Java, and type
classes in Haskell.

As an example, we can define a trait `Shape`, that provides methods for calculating
the area and the perimeter of the type implementing the trait.

```rust, ignore
trait Shape {
    fn area(&self) -> f64; // Method to calculate area
    fn perimeter(&self) -> f64; // Method to calculate perimeter
}
```

Then we can implement `Shape` for a variety of types that provide this
functionality. For example, we can define a circle datatype and implement
`Shape` for it.

```rust, ignore
struct Circle {
    radius: f64,
}

// Implement Shape for Circle
impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }

    fn perimeter(&self) -> f64 {
        2.0 * std::f64::consts::PI * self.radius
    }
}
```

## Trait Bounds
With traits, we can add bounds to generic types and require that they implement
a certain functionality. The following function compares the area of two shapes.
The shapes can have any type, as long as it implements the `Shape` trait.


```rust, ignore
// Generic function to compare areas of two shapes
fn compare_areas<T: Shape, U: Shape>(shape1: &T, shape2: &U) -> String {
    let area1 = shape1.area();
    let area2 = shape2.area();

    if area1 > area2 {
        String::from("Shape 1 has a larger area")
    } else if area1 < area2 {
        String::from("Shape 2 has a larger area")
    } else {
        String::from("Both shapes have equal areas")
    }
}
```

### Where Clauses
Rust provides an alternative trait bound syntax using `where` clauses, that can
make function signatures cleaner when using too may trait bounds.

Using where clauses, we can rewrite the above function as:

```rust, ignore
// Generic function to compare areas of two shapes
fn compare_areas<T, U>(shape1: &T, shape2: &U) -> String
where
    T: Shape,
    U: Shape,
{
    let area1 = shape1.area();
    let area2 = shape2.area();

    if area1 > area2 {
        String::from("Shape 1 has a larger area")
    } else if area1 < area2 {
        String::from("Shape 2 has a larger area")
    } else {
        String::from("Both shapes have equal areas")
    }
}
```


## Full Example

The following example summarizes what we covered above.

```rust, editable
// Define a trait for geometric shapes
trait Shape {
    fn area(&self) -> f64; // Method to calculate area
    fn perimeter(&self) -> f64; // Method to calculate perimeter
}

// Circle
struct Circle {
    radius: f64,
}

// Implement Shape for Circle
impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }

    fn perimeter(&self) -> f64 {
        2.0 * std::f64::consts::PI * self.radius
    }
}

// Rectangle
struct Rectangle {
    width: f64,
    height: f64,
}

// Implement Shape for Rectangle
impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn perimeter(&self) -> f64 {
        2.0 * (self.width + self.height)
    }
}

// Triangle
struct Triangle {
    a: f64,
    b: f64,
    c: f64,
}

// Implement Shape for triangle
impl Shape for Triangle {
    fn area(&self) -> f64 {
        let s = (self.a + self.b + self.c) / 2.0; // Semi-perimeter
        (s * (s - self.a) * (s - self.b) * (s - self.c)).sqrt() // Heron's formula
    }

    fn perimeter(&self) -> f64 {
        self.a + self.b + self.c
    }
}

fn compare_areas<T: Shape, U: Shape>(shape1: &T, shape2: &U) -> String {
    let area1 = shape1.area();
    let area2 = shape2.area();

    if area1 > area2 {
        String::from("Shape 1 has a larger area")
    } else if area1 < area2 {
        String::from("Shape 2 has a larger area")
    } else {
        String::from("Both shapes have equal areas")
    }
}

fn main() {
    let circle = Circle { radius: 5.0 };
    let rectangle = Rectangle {
        width: 4.0,
        height: 6.0,
    };

    println!("Comparison: {}", compare_areas(&circle, &rectangle));
}
```

## Default Implementations
Some methods of a trait can have a **default implementation** provided inside
the trait definition. These methods do not need to be explicitly defined in
every implementation of the trait, unless the implementer wants to override the
default behavior.


## Standard Library Traits
We give a brief description of the most important traits in the Rust standard library.

### [`Display`](https://doc.rust-lang.org/std/fmt/trait.Display.html)

`Display` provides an implementation for formatting a type with the `{}`
 specifier. It is intended to produce user-facing output. Typically, it
implements a clean, human-readable format.

Implementing the `Display` trait gives an implementation of the `ToString` trait
for free.

The definition of the trait in the standard library is the following.
```rust, ignore
pub trait Display {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
```

#### Example

```rust, editable
struct Point {
    x: i32,
    y: i32,
}

// Implement Display for Point
impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}
fn main() {
    let p = Point { x: 1, y: 2 };

    // Display output
    println!("{}", p);
}
```

###  `Debug`
`Debug` is similar to display but is intended for debugging purposes and
typically implements a detailed, developer-oriented output.

The definition of the trait in the standard library is the following.

```rust, ignore
pub trait Debug {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
```

#### Example

```rust, editable
use std::fmt;

struct Point {
    x: i32,
    y: i32,
}

// Implement Debug for Point
impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Point {{ x: {}, y: {} }}", self.x, self.y)
    }
}

fn main() {
    let triangle = vec![
        Point { x: 0, y: 0 },
        Point { x: 1, y: 0 },
        Point { x: 0, y: 1 },
    ];

    // Debug output
    println!("{:?}", triangle);

    // Debug output, pretty printed
    println!("{:#?}", triangle);
}
```

#### Deriving Traits
Some traits in Rust are **automatically derivable** using the `#[derive]`
attribute. The `derive` attribute can be applied to a struct or enum to
automatically generate default implementations of certain traits. This is done
through **metaprogramming** provided by the Rust compiler, which reduces
boilerplate code.

For example, traits like `Debug`, `Clone`, `PartialEq`, and `Eq` are commonly
derivable. This allows developers to quickly add functionality like formatting,
comparison, or duplication to their custom types without manually implementing
these traits.

You can find a complete list of automatically derivable traits in the [Rust
documentation](https://doc.rust-lang.org/book/appendix-03-derivable-traits.html).

Using derive, the above code can be rewritten as:

```rust, editable
use std::fmt;

#[derive(Debug)]
struct Point {
    x: i32,
    y: i32,
}

fn main() {
    let triangle = vec![
        Point { x: 0, y: 0 },
        Point { x: 1, y: 0 },
        Point { x: 0, y: 1 },
    ];

    // Debug output
    println!("{:?}", triangle);

    // Debug output, pretty printed
    println!("{:#?}", triangle);
}
```


### `Eq`, `PartialEq`, `Ord` `PartialOrd`
These traits implement
[equivalence](https://en.wikipedia.org/wiki/Equivalence_relation) relations,
[partial equivalence]() relations, [total
ordering](https://en.wikipedia.org/wiki/Total_order) relations, and [partial
ordering](https://en.wikipedia.org/wiki/Partially_ordered_set#Partial_order) respectively.

They are all similar in nature in defined in the standard library module
[cmp](https://doc.rust-lang.org/std/cmp/index.html).

### [`Clone`](https://doc.rust-lang.org/std/clone/trait.Clone.html)

The `Clone` trait provides a way to explicitly create a duplicate of a value.
This allows for deep copies of heap allocated data. A type can implement `Clone`
if all of its components are `Clone`. `Clone` can be implemented manually or
derived automatically. Note that automatic derivation will place `Clone` bounds
on all generic types, even though this may not be necessary (e.g., a `&T` is
clone even is `T` is not).


```rust, editable
#[derive(Debug, Clone)]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

use List::{Cons, Nil}; // To be able to use Cons and Nil without qualifying them.

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

fn main() {
    // Create a cons list: 1 -> 2 -> 3 -> Nil
    let mut list1 = list![1, 2, 3];

    // Perform a deep copy of the list
    let list2 = list1.clone();

    list1 = {
        match list1 {
            Nil => Nil,
            Cons(_, rest) => Cons(42, rest),
        }
    };

    // Print both lists to verify they are independent
    println!("Original list: {:?}", list1);
    println!("Cloned list: {:?}", list2);
}
```

A manual implementation for `Clone` in the above would be:

```rust, ignore
impl<T: Clone> Clone for List<T> {
    fn clone(&self) -> Self {
        match self {
            List::Nil => List::Nil,
            List::Cons(value, next) => {
                List::Cons(value.clone(), Box::new(*next.clone())) // Recursively clone the list
            }
        }
    }
}
```

### [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html)

We have already seen that some types do not exactly obey ownership rules. For
example, the following snippet works just fine, even though it seems to violate
ownership rules.

```rust, editable
fn main() {
    let mut x = (1, 3);
    let x1 = x.1;

    x.1 = 42;

    println!("x1 is {}", x1);
}
```

This works because the value of `x.1` (an `i32`) is **copied**, not moved, into
`x1`. Types like `i32` implement the `Copy` trait, which means that they can be
duplicated without invalidating the original value. Types that have copy
semantics instead of move semantics are called `Copy` types.

The `Copy` trait performs a **bitwise copy** of a value into a new location in
memory. This is similar to what a **move** does under the hood, though sometimes
the compiler can optimize away the actual copy operation.

The key difference between a **copy** and a **move** is what happens to the
original value:

- In a **move**, the original owner is invalidated, and you can no longer access
  the value.
- In a **copy**, the original value remains valid and accessible, allowing
  multiple independent owners of the same value.

Note that copies happen implicitly when a type implements the `Copy` trait.
There is no explicit method to call for a copy to occur; the duplication is
handled automatically by the compiler whenever a value is assigned or passed.

In fact, the `Copy` trait itself does not define any methods. Its definition is:

```rust, ignore
pub trait Copy: Clone {}
```

This means that any type implementing `Copy` must also implement the `Clone`
trait, which is a **supertrait** of `Copy`. A type that is `Clone` can also be
`Copy` if the cloning performs a bitwise copy, and not a deep copy of the value.
That is, the `Clone` implementation only needs to return `*self`.

Types that can be `Copy` are all types whose components are `Copy`. Primitive
types, tuples (whose components are `Copy`), shared references `&T` are all
`Copy` types.

There are types that cannot implement copy safely. These are heap allocated
types (like `Vec<T>` and `String`) and mutable references `&mut T`.

Types can implement `Copy` either manually or using deriving. The default derive
implementation will place bounds on all generic types, even though this may not
be necessary.

Notice the difference in the following snippets. The second fails to compile.

```rust, editable
#[derive(Debug)]
struct AStruct<'a, T, R> {
    x: T,
    y: &'a R,
}

impl<'a, T, R> Clone for AStruct<'a, T, R>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        AStruct {
            x: self.x.clone(),
            y: self.y.clone(),
        }
    }
}

impl<'a, T, R> Copy for AStruct<'a, T, R> where T: Copy {}

fn main() {
    let v = vec![1, 2, 3];
    let mut s: AStruct<u32, Vec<u32>> = AStruct { x: 42, y: &v };

    let mut z = s; // copy s

    z.x = 43;

    println!("s is {:?}", s);
}
```


```rust, editable
#[derive(Debug, Clone, Copy)]
struct AStruct<'a, T, R> {
    x: T,
    y: &'a R,
}

fn main() {
    let v = vec![1, 2, 3];
    let s: AStruct<u32, Vec<u32>> = AStruct { x: 42, y: &v };

    let mut z = s; // copy s

    z.x = 43;

    println!("s is {:?}", s);
}
```

### [`Drop`](https://doc.rust-lang.org/std/ops/trait.Drop.html)
When a value is no longer needed (e.g., it goes out of scope), Rust will
deallocate it calling a constructor. Rust calls the `drop` method automatically
when a value goes out of scope. `drop` cannot be called manually (however, there
is [`std::mem::drop`](https://doc.rust-lang.org/std/mem/fn.drop.html) for
explicitly destructing values).

In most cases, `Drop` does not have to be implemented as Rust automatically
calls destructors on al field of a value. It is useful for defining a custom
logic that will be executed when a value is no longer needed and is about to be
deallocated. Some use cases of drop involve:
- Manually managing memory
- Managing an OS native resource (e.g., file handle, network sockets) with a
  Rust interface.


Note that the destructor is run at the end of the scope 

```rust, editable
#[derive(Debug)]
struct X<'a>(&'a i32);

impl Drop for X<'_> {
    fn drop(&mut self) {}
}

fn main() {
    let mut data = vec![1, 2, 3];
    let x = X(&data[0]);
    println!("{:?}", x);
    data.push(4);
}
```

### [`From`](https://doc.rust-lang.org/std/convert/trait.From.html) and [`Into`]()

The `From` and `Into` traits in Rust are used for type conversions. Both traits
a way to convert one type into another, consuming the original value.
Implementing `From` for a type automatically provides the inverse `Into`
implementation.
