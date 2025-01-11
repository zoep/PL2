# Ownership

So far, we’ve only discussed stack-allocated types. In Rust, a tuple is one such
stack-allocated type. In the following example, the tuple `t` is allocated on
the stack frame of main and is deallocated once the function returns and its
stack frame is popped. When stack-allocated objects are assigned to a variable
or passed as arguments to functions, their values are copied.

One can create a tuple, pass it to a function to compute the sum of its
components, and then continue using the original tuple afterward:

```rust, editable
fn addt(t: (u32, u32)) -> u32 {
    t.0 + t.1
}

fn main() {
    let t = (3, 4);

    println!("The sum is: {}", addt(t));

    println!("The first component is: {}", t.0);
}
```

Nothing unusual about that; we do this all the time in various programming
languages.

However, for heap-allocated objects, Rust introduces the concept of ownership to
ensure memory safety without requiring a garbage collector.

Ownership dictates that a heap-allocated object has exactly one owner at any
given time. In other words, there is exactly one variable that “owns” (or
“holds”) a pointer to the heap-allocated data structure at any point during a
program's execution.

When a variable that has a type that is heap allocated gets reassigned or passed
as an argument, then pointer to the heap allocated will be copied, but not the
data itself. In such cases we say that the ownership of the value has been
_moved_. Once the ownership is moved the the previous pointer (i.e., original
owner of the value) becomes _invalidated_ and cannot be used anymore.

Since a value has only one owner, Rust knows exactly when the object is no
longer in use (when it goes out of scope). At that point, the memory can be
safely deallocated without the risk of dangling pointers or memory leaks.

In programming language theory, Rust’s ownership model is referred to as an
affine type system, a specialized form of substructural type systems. Such
systems constrain how resources—like memory—are accessed. In particular, affine
types limit each resource to a single “use” (or owner) at a time, which
guarantees memory safety without requiring a garbage collector.

## Heap Allocated Types

### Vectors

As our first example of a heap-allocated type in Rust, let’s look at
[vectors](https://doc.rust-lang.org/std/vec/struct.Vec.html#). Vectors are
dynamic, growable arrays whose size is not known at compile time. Because they
can grow or shrink at runtime, their contents live on the heap. Internally, a
vector is represented by a pointer to its heap-allocated data, plus two
additional fields to track its length and capacity.


```rust, editable
fn main() {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);
    vec.push(2);
    vec.push(42);

    println!("The vector is {:?}", vec);
    println!("The length of the vector is {}", vec.len());
    println!("The second element is {}", vec[1]);

    // vec goes out of scope here. The rust compiler can safely drop the value.
}
```


Let's write a function to sum the elements of a vector.

```rust, editable
fn sum(v: Vec<u32>) -> u32 {
    let mut sum = 0;

    for i in 0..v.len() {
        // 0 <= i < v.len() - 1.
        sum += v[i]
    }

    return sum;

    // v is the owner of the vector value now.
    // Once v goes out of scope the value can be dropped.
}

fn main() {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);
    vec.push(2);
    vec.push(42);

    println!("The sum of the elements of the vector is {:?}", sum(vec));
}
```

In the above code, ownership of vec is moved to the function parameter `v` in
`sum`. After this move, the original `vec` in `main `is invalidated and can no
longer be used. Rust’s ownership rules ensure that once `v` goes out of scope
inside sum, the memory can be deallocated safely—-or dropped, in Rust
terminology.


Consider the following example, where we attempt to use vec after calling sum:

```rust, editable
fn sum(v: Vec<u32>) -> u32 {
    let mut sum = 0;

    for i in 0..v.len() {
        // 0 <= i < v.len() - 1.
        sum += v[i]
    }
    return sum;

    // or just:
    // v.iter().sum()
}

fn main() {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);
    vec.push(2);
    vec.push(42);

    println!("The sum of the elements of the vector is {:?}", sum(vec));

    vec.push(21);
}
```

When you compile this, you’ll see an error indicating that `vec` has been moved
and is no longer valid. This error occurs because Rust prevents any further
usage of the vector after its ownership has been transferred to sum.

When ownership is transferred, a _shallow copy_ of the data is performed. This
means that only the pointer to the heap-allocated data is copied, not the actual
data itself. In Rust, this process is referred to as a _move_.

In contrast, a deep copy would clone the entire data structure on the heap. Rust
does not perform deep copies of heap allocated objects automatically, ensuring
efficiency and avoiding unintentional performance overhead.

Likewise, if you assign `vec` to another variable, the same move semantics
apply—ownership is transferred, and the original variable can no longer be used.

```rust, editable
fn main() {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);
    vec.push(2);
    vec.push(42);

    let mut vec2 = vec;

    vec.push(21);

    println!("The length of the vector is {:}", vec2.len());
}
```

Rust’s move semantics effectively prevent aliasing, meaning that once a value
has been moved, there is no longer any valid reference (or owner) left behind to
access the original data.

To work around this, the function receiving ownership could simply return it
back to the caller. This way, once the function completes, the caller regains
ownership of the value and can continue using it.


```rust, editable
fn sum(v: Vec<u32>) -> (u32, Vec<u32>) {
    let mut sum = 0;

    for i in 0..v.len() {
        // 0 <= i < v.len() - 1.
        sum += v[i]
    }
    return (sum, v);

    // or just:
    // v.iter().sum()
}

fn main() {
    let mut vec1 = Vec::new(); // calling the constructor

    vec1.push(1);
    vec1.push(2);
    vec1.push(42);

    let (sum1, mut vec2) = sum(vec1); // vec2 must be made mutable for us to modify it

    println!("The sum of the elements of the vector is {:?}", sum1);

    vec2.push(22);

    let (sum2, _) = sum(vec2);
    println!("The sum of the elements of the vector is {:?}", sum2);
}
```

Returning ownership on every function call would be cumbersome and non-idiomatic
in Rust. Instead, Rust provides references, which let you borrow a value without
transferring ownership. This borrowing mechanism keeps the compiler’s guarantees
about safety and ensures that you can still access the data without having to
move or clone it every time a function needs to look at it.

Note that in order for the function parameter to take ownership of a vector and
mutate it, we must declare the function parameter as mutable.

```rust, editable
fn add_one(mut v: Vec<u32>) -> Vec<u32> {
    // That's not idiomatic Rust. We will learn how to do this with iterators.

    for i in 0..v.len() {
        // 0 <= i < v.len() - 1.
        v[i] += 1
    }
    return v;
}

fn main() {
    let mut vec = vec![1, 2, 3];

    let v = add_one(vec);

    println!("The vector is {:?}", v);
}
```


### Bounds checking

By default, Rust performs bounds checks on accesses to container types like
vectors. This ensures you never access invalid memory and helps prevent
out-of-bounds errors at runtime. In contrast, C/C++ forgo such checks to
prioritize performance.

Still, Rust offers [a few
ways](https://nnethercote.github.io/perf-book/bounds-checks.html) to avoid or
minimize bounds-checking overhead without resorting to unsafe code:

- Use iterators rather than direct indexing.
- Add assertions that can help the compiler infer that certain bounds checks are
unnecessary.



## Strings

Another common heap allocated type in Rust is strings.

Rust has a type `str` that ....

a growable, mutable, owned, UTF-8 encoded string type
