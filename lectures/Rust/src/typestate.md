# Typestate Pattern

The typestate pattern in Rust is a pattern for designing API's in Rust in a way
that types encode information about an object's runtime state.

Each state is represented as a distinct type, and transitions between states are
implemented as methods that consume the object and return a new object in a
different state. This pattern makes it easy to enforce the order of operations
on an object statically, ensuring invalid transitions are impossible at compile
time. This eliminates the need for runtime checks, improving safety and
performance.

Some useful references:

- https://blog.systems.ethz.ch/blog/2018/a-hammer-you-can-only-hold-by-the-handle.html
- https://yoric.github.io/post/rust-typestate/
- https://cliffle.com/blog/rust-typestate/#typestate-in-the-wild-serde

## Example

```rust, editable
/// Represents the unauthenticated state.
pub struct Unauthenticated;

/// Represents the authenticated state.
pub struct Authenticated;

/// A generic User struct with a specific state (Unauthenticated or Authenticated).
pub struct User<S> {
    pub username: String,
    password: String,
    pub state: S,
}

impl User<Unauthenticated> {
    /// Create a new unauthenticated user.
    pub fn new(username: String, password: String) -> Self {
        User {
            username,
            password,
            state: Unauthenticated,
        }
    }

    /// Transition the user to the authenticated state if credentials are valid.
    pub fn authenticate(self) -> Result<User<Authenticated>, String> {
        // Mock authentication logic for demonstration.
        if self.username == "admin" && self.password == "password" {
            Ok(User {
                username: self.username,
                password: self.password,
                state: Authenticated,
            })
        } else {
            Err("Invalid username or password".to_string())
        }
    }
}

impl User<Authenticated> {
    /// Perform an action as an authenticated user.
    pub fn get_top_secret(&self) -> &'static str {
        "The answer to the ultimate question of life, the universe, and everything is 42"
    }

    /// Log out and transition back to the unauthenticated state.
    pub fn logout(self) -> User<Unauthenticated> {
        User {
            username: self.username,
            password: self.password,
            state: Unauthenticated,
        }
    }
}

fn main() {
    let mut user = User::new("admin".to_string(),"password".to_string());
    let mut secret;

     match user.authenticate() {
        Ok(user) => secret = user.get_top_secret(),
        Err(_) => secret = "cannot read secret",
     }

     println!("{}", secret);
}
```

## A More Complex Example