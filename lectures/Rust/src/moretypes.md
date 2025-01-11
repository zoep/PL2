# User Defined Types

Rust type system has algebraic data types that allows constructing complex data
types form simpler ones. Specifically, one can define new data types with
structs (a generalization of product types) and enums (a generalization of sum
types).


## Structs

Here's a simple example of a struct.

```rust, editable
struct Point {
    x: i32,
    y: i32,
}

fn add(a: Point, b: Point) -> Point {
    Point {
        x: a.x + b.x,
        y: a.y + b.y,
    }
}

fn main() {
    let point1 = Point { x: 1, y: 2 };
    let mut point2 = Point { y: 4, x: 3 }; // fields don't have to be in order

    point2.x += 1; // move point2

    let point3 = add(point1, point2);

    println!("The point is at ({}, {})", point3.x, point3.y);
}
```

By convention, struct names begin with a capital letter and are written in
CamelCase.

There are also unit structs (with no fields) and tuple structs.

```rust, editable
struct Unit;

#[derive(Debug)] // derive the implementation of the Debug trait, to display values with the {:?} format specifier
struct Point {
    x: i32,
    y: i32,
    z: i32,
}

#[derive(Debug)]
struct TwoPoints(Point, Point);

fn add(ps: TwoPoints) -> Point {
    let TwoPoints(pA, pB) = ps; // tuple structs can be pattern matched

    return (Point {
        x: pA.x + pB.x,
        y: pA.y + pA.y, // dot notation also works
        z: pA.z + pB.z,
    });
}

fn main() {
    let pointA = Point { x: 0, y: 0, z: 0 };
    let pointB = Point { y: 5, ..pointA }; // this is called "update syntax"

    let both = TwoPoints(pointA, pointB);

    let _unused = Unit;

    println!("The points are {:?}", both);
    println!("Its sum is {:?}", add(both));
}
```

Structs are by default stack allocated.

### Struct Methods

Structs in Rust can have associated functions, known as methods. These methods
are defined within an `impl` block for the respective struct type and are called
in the context of a struct instance.

The first parameter of a method is always named `self` and refers to the struct
instance the method is called on. Methods can take ownership of the struct
instance or a (mutable) reference to it, written `&self` (resp. `&mut self`)
which is a shorthand for `self: &Self` (resp. `self: &mut self`).

Here’s an example illustrating struct methods:


```rust, editable
#[derive(Debug)]
struct Point {
    x: i32,
    y: i32,
}

impl Point {
    // distance from origin
    fn dist0(&self) -> f64 {
        // converts to f64 and calculares the square root
        ((self.x ^ 2 + self.y ^ 2) as f64).sqrt()
    }

    // distance from any point
    fn dist(&self, p: Point) -> f64 {
        // converts to f64 and calculares the square root
        (((self.x - p.x) ^ 2 + (self.y - p.y) ^ 2) as f64).sqrt()
    }

    // add two points
    fn add(&self, p: Point) -> Point {
        Point {
            x: self.x + self.x,
            y: self.y + self.y,
        }
    }

    fn moveUp(&mut self) {
        self.y += 1
    }
}

fn main() {
    let mut point1 = Point { x: 1, y: 2 };
    let point2 = Point { x: 3, y: 4 };

    point1.moveUp();

    println!("The distance from (0,0) is {}", point1.dist0());
    println!("The sum of p1 and p2 is {:?}", point2.add(point1));
}
```

## Enums

Enums in Rust enable you to define types that represent one of several possible
variants. Each variant can optionally carry associated data, which can be a
single value, a tuple, or a struct.

Enum types can be pattern matched to handle their different variants. They can
also have associated methods in `impl` blocks just like structs.

Here's an illustrative example.

```rust, editable
enum Shape {
    Circle(f64),
    Rectangle { width: f64, height: f64 },
    Triangle(f64, f64, f64),
}

impl Shape {
    fn area(&self) -> f64 {
        match self {
            // Circle
            Shape::Circle(radius) => std::f64::consts::PI * radius.powi(2),
            // Rectangle
            Shape::Rectangle { width, height } => width * height,
            // Triangle
            Shape::Triangle(a, b, c) => {
                // Heron's formula
                let s = (a + b + c) / 2.0;
                (s * (s - a) * (s - b) * (s - c)).sqrt()
            }
        }
    }
}

fn main() {
    let circle = Shape::Circle(3.0);
    let rectangle = Shape::Rectangle {
        width: 4.0,
        height: 5.0,
    };
    let triangle = Shape::Triangle(3.0, 4.0, 5.0);

    println!("Area of the circle: {}", circle.area());
    println!("Area of the rectangle: {}", rectangle.area());
    println!("Area of the triangle: {}", triangle.area());
}
```

## Recursive Types
Rust allows definition of recursive structs that can refer to themselves Recursive types have some restrictions:

- They must be under some struct or enum.
- They must be finite.

### The Problem with Infinite Size
If we attempt to define a recursive enum like this:

```rust, editable
#[derive(Debug)]
enum OpKind {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug)]
enum Exp {
    Lit(i64),
    Op { op: OpKind, lhs: Exp, rhs: Exp },
}

fn main() {
    let e = Lit(42);
    println!("{}", e);
}
```

The compiler will generate an error saying: `recursive type Exp has infinite
size`.

This happens because, by default, Rust stores data on the stack, which requires
the size of all types to be statically known. A recursive type like `Exp` would
require an infinitely large amount of stack memory, as it contains itself
directly.

To resolve this, we can use heap allocation. Instead of storing the recursive
value directly, we store a pointer to the heap where the value resides. Rust
provides the `Box` type to heap-allocate values.

### Box Types

A type `Box<T>` represents a type `T` that is allocated on the heap of the
program. Technically, a box is pointer type that uniquely owns a heap location
storing a value og type `T`. A Box type can be used just as the underlying type.

A box can be created with its constructor `Box::new` that allocates memory on
the heap and places the given value into it.

```rust, editable
fn main() {
    let b: Box<u32> = Box::new(1);
    println!("The number is {}", b);
}
```

### Recursive Types with Box Types

Using box types, we can fix the above example.

```rust, editable
#[derive(Debug)]
enum Op {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Debug)]
enum Exp {
    Lit(i64),
    Op {
        op: Op,
        lhs: Box<Exp>,
        rhs: Box<Exp>,
    },
}

impl Exp {
    fn eval(&self) -> i64 {
        match self {
            // Literals
            Exp::Lit(n) => *n, // TODO why is this &i64
            // Binary Operators
            Exp::Op { op, lhs, rhs } => {
                let e1 = lhs.eval();
                let e2 = rhs.eval();
                match op {
                    Op::Add => e1 + e2,
                    Op::Sub => e1 - e2,
                    Op::Mul => e1 * e2,
                    Op::Div => e1 / e2,
                }
            }
        }
    }
}

fn main() {
    // e = 10 + 2 * 6
    let e = Exp::Op {
        op: Op::Add,
        lhs: Box::new(Exp::Lit(10)),
        rhs: Box::new(Exp::Op {
            op: Op::Mul,
            lhs: Box::new(Exp::Lit(2)),
            rhs: Box::new(Exp::Lit(6)),
        }),
    };

    println!("The answer is {}", e.eval());
}
```
