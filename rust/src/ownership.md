# Ownership

## Heap Allocated Types

So far we have only seen stack allocated types. 

For example, a tuple will, by default, be allocated on the stack.

One can create a tuple, then pass it to a function to compute the sum of its
components and then use it again in the rest of the program.

```rust, editable

fn addt(t : (u32,u32)) -> u32 {
    t.0 + t.1
}

fn main() {

    let t = (3,4);
    
    println!("The sum is: {}", addt(t));

    println!("The first component is: {}", t.0);
}

```

Nothing wrong with this, right? We do such things it all the time in all sorts of
programming languages. 

Well, almost. 

For heap allocated objects Rust has a concept called _ownership_.  Ownership
ensures memory safety without requiring a garbage collector.

A heap allocated object has _exactly one owner_ at each point in time. This
means that a heap allocated value is attached to one variable, which is the
value's _owner_.

Ownership can be transferred by moving a value to another variable. This happens
during assignment or when passing the value as a function argument. After the
value is moved, the previous owner can no longer access it. Attempting to use
the value after it has been moved results in a compile-time error. 

Since a value has only one owner, Rust knows exactly when the object is no
longer in use (when it goes out of scope). At that point, the memory can be
safely deallocated without the risk of dangling pointers or memory leaks.

In programming language theory, the ownership system of Rust is called an
_affine type system_, which is a special case of _substructural type systems_.
Such systems constraint access to system resources types are called affine types
and are _substructural type systems_.


## Vectors

As a first example of a heap allocated type we will look at vectors. Vectors are
dynamic, growable arrays. Their size is not known at compile time and they can
grow or shrink at any time. A vector is represented using the pointer to the
vector, the length of the vector, and the capacity of the vector.


```rust, editable
fn main () {
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


Let's write a function that sums the elements of a vector. 

```rust, editable
fn sum (v : Vec<u32>) -> u32 {
    let mut sum = 0;
  
    for i in 0..v.len() { // 0 <= i < v.len() - 1.
        sum += v[i]
    }

    return sum;

    // v is the owner of the vector value now. 
    // Once v goes out of scope the value can be dropped.
}


fn main () {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);    
    vec.push(2);
    vec.push(42);

    println!("The sum of the elements of the vector is {:?}", sum(vec));
}
```

So far so good. 

What do you think it will happen if we try to use `vec` after the call to the
`sum` function? 


```rust, editable
fn sum (v : Vec<u32>) -> u32 {
    let mut sum = 0;
  
    for i in 0..v.len() { // 0 <= i < v.len() - 1.
        sum += v[i]
    }
    return sum;

    // or just: 
    // v.iter().sum()
}


fn main () {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);    
    vec.push(2);
    vec.push(42);

    println!("The sum of the elements of the vector is {:?}", sum(vec));
    
    vec.push(21);
}
```

Oops. The compiler complains that the value of `vec` has been moved. 


This makes sense. Using `vec` after the call to `sum` would violate Rust
ownership. When calling the sum function, ownership of the `vec` is moved to the
parameter `v` on the function `sum`.  The original variable `vec` is
invalidated, and any attempt to use it results in a compile-time error. Rust’s
ownership model ensures that the vector is properly deallocated when it goes out
of scope in the `sum` function.


When ownership is transferred, a _shallow copy_ of the data is performed. This
means that only the pointer to the heap-allocated data is copied, not the actual
data itself. In Rust, this process is referred to as a _move_.

Instead, a deep copy would duplicate the entire data structure, including
heap-allocated data. Rust does not automatically perform deep copies to ensure
efficiency and avoid unintended performance overhead.

A similar thing will happen if we assign `vec` to an other variable. 

```rust, editable
fn main () {
    let mut vec = Vec::new(); // calling the constructor

    vec.push(1);    
    vec.push(2);
    vec.push(42);

    let mut vec2 = vec; 
    
    vec.push(21);
    
    println!("The length of the vector is {:}", vec2.len());
}
```

That is, the move semantics of Rust entirely prevent aliasing. 

In order to get around this, the sum function would have to pass the ownership
of the vector back to its caller. 


```rust, editable
fn sum (v : Vec<u32>) -> (u32, Vec<u32>) {
    let mut sum = 0;
  
    for i in 0..v.len() { // 0 <= i < v.len() - 1.
        sum += v[i]
    }
    return (sum,v);

    // or just: 
    // v.iter().sum()
}


fn main () {
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

Of course this is tedious and not idiomatic Rust. Rust allows us to do this
using references that provide a way to borrow a value without transferring
ownership.


## Strings 

Another common heap allocated type in Rust is strings.


Rust has a type `str` that .... 

a growable, mutable, owned, UTF-8 encoded string type