# References

Rust provides a reference type that allows you to borrow a value without taking
ownership of it. Reference types are denoted as `&T`, where `T` is the type
being referenced. References can also be mutable, written as `&mut T`.
References are created using the `&` and `&mut` operators.

References are like pointers in C/C++, but unlike these a reference is
guaranteed to point to a valid value of a particular type for the life of that
reference, preventing dangling references. That is, references cannot outlive
the lifetime of the original value. Rust ensures this statically using the
_borrow checker_.

For the most part, references can be used as values of the referenced type.
However, when a reference goes out-of-scope, is not dropped. The original owner
retains responsibility for managing the value's lifecycle.

## Simple Examples

Let's look at some simple examples of references. We will start with references
to stack allocated values.

```rust, editable
fn main() {
    let mut x: u32 = 42;
    // get a reference to x
    let r: &u32 = &x;

    println!("Hello, it is {} again.", r);
}
```

Multiple immutable references can coexist at the same time. For example:

```rust, editable
fn main() {
    let mut x: u32 = 42;
    // get two references to x
    let r1 = &x;
    let r2 = &x;

    println!("Hello, it is {} again.", r2);
}
```
Now, let's say that we want to change the value that the reference point to. We
can do this with a dereferencing operator, similar to C/C++. For example, we can
write `*r1 = 41;`.

If we try editing the above code to do this, the compiler will complain, as `r1`
is not declared as a mutable reference.

To do this, we have to declare the reference as mutable.

```rust, editable
fn main() {
    let mut x: u32 = 41;
    // take a mutable reference of x
    let r: &mut u32 = &mut x;
    *r += 1;
    println!("Hello, it is {} again.", r);
}
```

During the _lifetime_ of a mutable borrow, we cannot borrow the value in any
other way (mutable or immutable). That is, a mutable borrow is the only way to
access the memory it points at.


The following code snippets all fail to compile.

```rust, editable
fn main() {
    let mut x: u32 = 41;
    // take a mutable reference of x
    let r: &mut u32 = &mut x;
    *r += 1;
    // take a reference of x. NO NO.
    let r2: &u32 = &x;
    println!("Hello, it is {} again.", r);
}
```

```rust, editable
fn main() {
    let mut x: u32 = 41;
    // take a mutable reference of x
    let r: &mut u32 = &mut x;
    // take a second mutable reference of x. BIG NO.
    let r2: &mut u32 = &mut x;
    *r += 1;
    println!("Hello, it is {} again.", r);
}
```

While the value of `x` is mutably borrowed we are not able to access the value
through the owner. The following snippet also fails to compile.

```rust, editable
fn main() {
    let mut x: u32 = 41;
    let r: &mut u32 = &mut x;
    *r += 1;
    println!("Hello, it is {} again.", x);
    println!("Hello, it is {} again.", r);
}
```

With these restrictions, Rust prevent subtle memory errors like iterator
invalidation. It also prevents data races at compile time. A data race occurs
when two or more threads access the same memory concurrently in an
unsynchronized manner, and at least one of those accesses is a write operation.

Data races can lead to undefined behavior and are a common source of subtle,
hard-to-debug issues in multithreaded programs. By enforcing strict ownership
and borrowing rules, Rust eliminates data races entirely at compile time,
ensuring safe concurrent programming.

Notice that the following works just fine. Can you imagine why?

```rust, editable
fn main() {
    let mut x: u32 = 41;
    let r: &mut u32 = &mut x;
    *r += 1;
    println!("Hello, it is {} again.", x);
}
```

The lifetime of a borrow ends then the borrow is last used. In this example, this is right after line 4.

Similarly, the following examples work fine.

```rust, editable
fn main() {
    let mut x: u32 = 40;

    let r1: &mut u32 = &mut x; // r1's lifetime begins here
    *r1 += 1;
    println!("{}.", r1); // r1's lifetime ends here

    let r2: &mut u32 = &mut x; // r2's lifetime begins here
    *r2 += 1;
    println!("Hello, it is {} again.", r2); // r2's lifetime ends here
}
```

In the above the lifetimes of `r1` and `r2` do not overlap. The following example is also similar.


```rust, editable
fn main() {
    let mut x: u32 = 40;

    let r1: &mut u32 = &mut x; // r1's lifetime begins here
    *r1 += 1;
    println!("{}.", r1); // r1's lifetime ends here

    let r2: &u32 = &x; // r2's lifetime begins here
    println!("Still {}.", r2); // r2's lifetime ends here
}
```

## Borrowing Rules

To recap, references (also known as borrows) allow values to be passed around
without transferring ownership. Rust’s borrow checker enforces strict rules to
guarantee memory safety and prevent common bugs like data races or dangling
pointers. Here are the rules:


- No borrow can outlive the scope of of the owner.
- At any given time, You Can Have Either
  - one mutable reference XOR
  - any number of immutable references
- A borrow's lifetime ends when it is last used.


## More examples

Here's an example of trying to create a reference whose lifetime would outlive the lifetime of the owner.

```rust, editable
fn nope<'a>() -> &'a u32 {
    // 'a is a lifetime variable. We'll discuss this later in detail. You may ignore it for now.
    let x = 42;
    return &x; // attempting to return a reference to x
}

fn main() {
    println!("Will this work? {}", nope());
}
```

The variable `x` is owned by the `nope` function. When the function returns, its
stack frame is deallocated, and all local variables, including `x`, are dropped.
Returning a reference to `x` means returning a reference to invalid memory,
which would lead to undefined behavior.

The Rust's borrow checker detects that the reference to `x` would outlive its
owner (`x`), so it prevents the code from compiling.

## Creating Scopes

We can use curly braces to create (nested) scopes. When a scope ends the
lifetime of the variables creates within the scope ends.

```rust, editable
fn main() {
    let mut x = 40;

    {
        let z = &mut x;
        *z += 1;
    } // z's lifetime ends here

    let y = &mut x;
    *y += 1;
    println!("Hello, it is {} again.", x);
}
```

Nothing too fancy here. In the next example, notice how the borrow checker will
prevent borrows that outlive the scope of the owner

```rust, editable
fn main() {
    let x: &mut u32;

    {
        let mut z = 41;
        x = &mut z;
    } // z's lifetime ends here

    *x += 1;
    println!("Hello, it is {} again.", x);
}
```

However, the following works fine.
```rust, editable
fn main() {
    let mut x: &mut u32;

    {
        let mut z = 41;
        x = &mut z;
        println!("Hello, it is {} again.", x);
    } // z's lifetime ends here

    let mut y = 10;
    x = &mut y;
    *x += 1;
    println!("Hello, now it is {}.", x);
}
```

## Vectors, again

Let's now go back to our vector example. Recall that to call a function to sum
the elements of a vector and be able to reuse the vector after this we had to
pass the ownership around. This can become very tedious but thankfully we can
use reference to make it easier.


```rust, editable
fn sum(v: &Vec<u32>) -> u32 {
    // sum takes a reference to the vector.
    let mut sum = 0;

    for i in 0..v.len() {
        // 0 <= i < v.len() - 1.
        sum += v[i]
    }
    return sum;
}

fn main() {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);
    vec.push(2);
    vec.push(42);

    println!("The sum of the elements of the vector is {:?}", sum(&vec));

    vec.push(22);

    println!("The sum of the elements of the vector is {:?}", sum(&vec));

    // vec can be safely dropped here
}
```


### More Examples

The following example showcases passing a mutable reference to a vector as a parameter.

```rust, editable
fn add_one(v: &mut Vec<u32>) {
    // That's not idiomatic Rust. We will learn how to do this with iterators.

    for i in 0..v.len() {
        // 0 <= i < v.len() - 1.
        v[i] += 1
    }
}

fn main() {
    let mut vec = vec![1, 2, 3];

    add_one(&mut vec);
    println!("The vector is {:?}", vec);
}
```



```rust, editable
fn main() {
    let mut data = vec![1, 2, 3];
    let mut x = &data[0];

    println!("{}", x);

    data.push(4);

    x = &data[3];
    println!("{}", x);
}
```
