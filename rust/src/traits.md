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
    let rectangle = Rectangle { width: 4.0, height: 6.0 };

    println!("Comparison: {}", compare_areas(&circle, &rectangle));
}
```

## Deriving Traits

## Standard Library Traits

### Clone
### Copy 
### Display
### PartialEq
TODO double bounds

### Iterators
 