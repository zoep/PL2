# Lifetimes

In Rust, references are valid for specific regions of code, known as *lifetimes*.
The borrow checker ensures that references do not outlive the lifetimes of their
owners and that lifetimes of mutable references do not overlap with any other
references to the same value.

Most of the time, lifetimes are implicit and inferred by the compiler. For example,
the following code fails to compile because the lifetime of the borrow ends before
the lifetime of the variable `z`.


```rust, editable
fn main() {
    let z : &Box<(u32,u32)>;

    {

       let y : Box<(u32,u32)> = Box::new((42, 44));

        z = &y;
    } // y's lifetime ends here. y is dropped.

    println!("{:?}", z)
}
```

However, there are situations where lifetime annotations are necessary to clarify
the relationships between lifetimes. Consider the following scenario:

```rust, editable
fn first<T>(a: &T, b: &T) -> &T {
    a
}

fn main() {
    let x : Box<(u32,u32)> = Box::new((32, 34));

    let z : &Box<(u32,u32)>;

    {
        let y : Box<(u32,u32)> = Box::new((42, 44));

        z = first(&x,&y);

    } // y's lifetime ends here. y is dropped.


    println!("{:?}", z)
}
```

The function `first` takes two references and returns one of them. However, the
compiler does not know whether the returned reference remains valid beyond the
lifetime of `y`. Since `z` is assigned the result of `first`, it could reference
`x` (which is valid) or `y` (which is dropped). The compiler will return an error
because the function type does not provide enough information about how the
lifetimes of the inputs relate to the lifetime of the output.

We can use *generic lifetimes* to instruct the compiler that the returned
lifetime is the same as some input lifetime.

## Lifetime Annotations

Rust's type system allows us to give a richer type to the function `first`
using *generic lifetime annotations*. Such annotations explicitly define the
relationships between the lifetimes of the function's inputs and outputs.


```rust, editable
fn first<'a,'b,T>(x: &'a T, y: &'b T) -> &'a T {
    x
}

fn main() {
    let x : Box<(u32,u32)> = Box::new((32, 34));

    let z : &Box<(u32,u32)>;

    {
        let y : Box<(u32,u32)> = Box::new((42, 44));

        z = first(&x,&y);

    } // y's lifetime ends here


    println!("{:?}", z)
}
```

Just as we can add generic type parameters to a function, we can also add
generic lifetime parameters. In the example above, we introduce two lifetime
parameters, `<'a, 'b>`, after the function name. These parameters represent the
lifetimes of the references passed to the function.

Next, we associate these lifetime parameters with the references in the function
signature. Writing `x: &'a T` indicates that the reference `x` has lifetime
`'a`, and `y: &'b T` indicates that `y` has lifetime `'b`. Furthermore, we
specify that the returned reference has the same lifetime as `'a`, the lifetime
of `x`.

The function now type checks because the borrow checker can verify that the
returned reference has the expected lifetime. The usage of `z` now type checks
because the type of `first` carries enough information for the compiler to deduce
that the reference in `z` is valid when it is printed.

The function `first` could also be given the following type:

```rust, ignore
fn first<'a, T>(x: &'a T, y: &'a T) -> &'a T {
    x
}
```

However, with this signature, we would not be able to use the variable `z`
outside of `y`'s scope.

Let's look at a more complex example involving vectors. This time the function
`longer` can return either of the two vectors. Therefore, the lifetime of the
returned reference must be the smaller of the two lifetimes.

As an exercise, try to fill in the lifetimes in the example below.

```rust, editable
fn longer<T>(v1:&Vec<T>, v2: &Vec<T>) -> &Vec<T> {
    if v1.len() >= v2.len() { v1 } else { v2 }
}

fn main() {
    let x : Vec<u32> = vec![1,2,3,4];

    let z : &Vec<u32>;

    {
        let y : Vec<u32> = vec![1,2,3];

        z = longer(&x,&y);
        println!("{:?}", z)

    }

    // println!("{:?}", z)
}
```

The call to `longer` type checks because Rust performs *lifetime coercion*,
which allows a longer lifetime to be coerced into a shorter one.


Note that we could also use slices (`&[T]`) instead of vectors (`&Vec<T>`) in
the above example. Slices are more general as they can represent views into
arrays, vectors, or other sequences of `T`s.  

```rust, editable
fn longer<'a, T>(v1: &'a [T], v2: &'a [T]) -> &'a [T] {
    if v1.len() >= v2.len() { v1 } else { v2 }
}

fn main() {
    let x: Vec<u32> = vec![1, 2, 3, 4];

    {
        let y: Vec<u32> = vec![1, 2, 3];

        let z = longer(&x, &y);   // &Vec<T> coerces to &[T] automatically
        println!("{:?}", z);
    }

    // println!("{:?}", z); // still not allowed (same reason as before)
}
```

## Lifetimes in Structs and Enums

When structs or enums hold references, they must also include lifetime annotations
for every reference field in their definition. This ensures that the lifetime of
each reference field is at least as long as the lifetime of the struct or enum
itself.

Here's an example that uses the
[`slice`](https://doc.rust-lang.org/std/primitive.slice.html) data type. The
slice data type is a view into a contiguous block of memory, which is part of a
larger collection like an array or a vector. It is a reference to a segment of
the collection, without owning the data.


```rust, editable
struct Chunks<'a, T> {
    read: &'a [T],
    read_write: &'a mut [T],
}

fn zero_out<'a>(chunks: &mut Chunks<'a, u32>) {
    for i in 0..chunks.read_write.len() {
        chunks.read_write[i] = 0;
    }
}

fn sum<'a>(chunks: &Chunks<'a, u32>) -> u32 {
    let mut sum = 0;
    for i in 0..chunks.read.len() {
        sum += chunks.read[i];
    }
    sum
}

fn main() {
    let mut v = vec![1, 2, 3, 4, 5];

    let (read_only, read_write) = v.split_at_mut(2);

    let mut chunks = Chunks {
        read: read_only,
        read_write: read_write,
    };


    println!("Sum of read-only part: {}", sum(&chunks));

    zero_out(&mut chunks);

    println!("After zero_out: {:?}", v);
}
```

Here is an example where distinct lifetimes for struct fields are useful:

```rust, editable
struct Chunks<'a,'b, T> {
    read: &'a [T],
    read_write: &'b mut [T],
}

fn zero_out<'a,'b>(chunks: &mut Chunks<'a,'b, u32>) {
    for i in 0..chunks.read_write.len() {
        chunks.read_write[i] = 0;
    }
}


fn main() {
    let mut v1 = vec![1, 2, 3, 4, 5];
    let s;

    {
        let v2 = vec![6,7,8];

        let mut chunks = Chunks {
            read: &v2[1..3],
            read_write: &mut v1[2..4],
        };

        zero_out(&mut chunks);

        s = chunks.read_write;

    }

  println!("Slice: {:?}", s);
  println!("After zero_out: {:?}", v1);

}
```

## Lifetime Elision

In Rust, the borrow checker can infer elided lifetimes in specific cases,
enabling more concise code. These inference rules allow developers to omit
explicit lifetime annotations in many scenarios. The rules are as follows:

- Each elided input lifetime becomes a distinct lifetime parameter.
- If there is exactly one input lifetime position (whether elided or explicit),
  that lifetime is applied to all elided output lifetimes.
- If there are multiple input lifetime positions, but one of them is `&self` or
  `&mut self`, the lifetime of `self` is applied to all elided output lifetimes.

If the borrow checker cannot infer lifetime relationships using these rules,
explicit lifetime annotations are required.

```rust, editable
struct Example {
    value: i32,
}

impl Example {
    // The method borrows self and returns a reference to its value.
    // The lifetime of &self is inferred to be the same as the returned reference.
    // Equivalent to: fn get_value<'a>(&'a self) -> &'a i32
    fn get_value(&self) -> &i32 {
        &self.value
    }
}

fn main() {
    let example = Example { value: 42 };

    println!("The value is: {}", example.get_value());
}
```

The signature of `longer` above requires explicit lifetime annotation because
lifetimes cannot be inferred using the above rules.

## Static

Rust has a special lifetime called `'static`. This lifetime represents memory that
lasts for the entire duration of the program's execution.

A reference `&'static T` is an immutable reference to data that is guaranteed
to be valid and safely accessible throughout the program's lifetime.

This can typically occur in two ways:

1. The value is hardcoded into the executable.
2. The value is a reference to leaked memory.

### `'static` Lifetime from Constants

Here is an example of the first case:

```rust, editable
fn main() {
    // A slice with a 'static lifetime (valid for the program's duration)
    let data: &'static [u32] = &[10, 20, 30];

    // The slice can be used throughout the program
    println!("Static slice: {:?}", data);
}
```

In this example, the slice `&[10, 20, 30]` has a `'static` lifetime because it
refers to a constant array embedded in the program's binary. The data remains
valid and accessible for the entire duration of the program.

Rust can promote the lifetime of a temporary value to `'static` under certain
conditions. This happens when the value is constant and immutable.

```rust, editable
fn foo() -> &'static [u32] {
    &[10, 20, 30]
}

fn main() {
    // A slice with a 'static lifetime (valid for the program's duration)
    let data = foo();

    // The slice can be used throughout the program
    println!("Static slice: {:?}", data);
}
```

### Leak

The second way to create a `'static` lifetime is by leaking memory. When memory
is "leaked," it is never deallocated, making it safe to use for the entire
program's execution.

```rust, editable
fn foo() -> &'static [u32] {
    // Create a Vec on the heap
    let dynamic_data = vec![1, 2, 3, 4, 5];

    // Leak the Vec to produce a static slice
    Box::leak(dynamic_data.into_boxed_slice())
}

fn main() {
    // A slice with a 'static lifetime created via leak
    let data = foo();

    // The slice can be used throughout the program
    println!("Static slice from leak: {:?}", data);
}
```