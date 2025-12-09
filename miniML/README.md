# MiniML

This Haskell project implements a typechecker and interpreter for MiniML, a
simply-typed lambda calculus extended with various types and language
constructs. In the following assignments we will extend the language with
various features.

## Syntax

MiniML is a simply typed lambda calculus extended with integers, booleans, unit,
product types, sum types, lists, references, and lazy evaluation. Its concrete
syntax and a brief description of each language construct is given below.

- **Functions**:
  - Type: `t1 -> t2`
  - Introduction form: `fun (x : t) -> e` (anonymous functions).
  - Elimination form: `e1 e2` (function application).

- **Integers**: Integers are represented primitively and come with arithmetic
(`+`, `-`, `*`, `/`.) and comparison (`<`, `<=`, `>`, `>=`, `==`) operators.

- **Booleans**:
  - Type: `bool`
  - Constructors: `true`, `false`.
  - Elimination form: `if e then e1 else e2`
  - Operators: conjunction: `&&`, disjunction: `||`, negation `not`.

- **Unit**
  - Type: `()`
  - Value: `()`

- **Product Types**:
  - Type: `t1 * t2`
  - Introduction form: `(e1, e2)` (pairs).
  - Elimination forms:
    - `fst e`: Projects the first element of a pair.
    - `snd e`: Projects the second element of a pair.

- **Sum Types**:
  - Type: `t1 + t2`
  - Introduction forms:
    - `inl[t2] e`: Constructs a value of type `t1 + t2`, where `t1` is
       the type of `e` and `t2` is given as a type annotation.
    - `inr[t1] e`: Constructs a value of type `t1 + t2`, where `t2` is
       the type of `e` and `t1` is given as a type annotation.
  - Elimination form: `case e of | inl x -> e1 | inr y -> e2`.

- **Lists**:
  - Type: `list t`
  - Introduction forms:
    - `nil[t]`: empty list of type t
    - `e::es`: list cons
  - Elimination form: `case e of | nil -> e1 | x::xs -> e2`.

- **References**:
  - Type: `ref t`
  - Introduction form: `ref e` (creates a new reference).
  - Elimination form: `!e` (dereferences).
  - Mutation: `e1 := e2` (assignment).

- **Lazy Evaluation**:
  - Type: `lazy t`
  - Introduction form: `lazy e` (suspends computation).
  - Elimination form: `force e` (forces evaluation and memoizes result).

- **Let Bindings**:
  - Syntax: `let x : t = e1 in e2`
  - Semantics: Introduces a variable `x` with type `t` bound to the value of
    `e1` in the scope of `e2`.

- **Recursive Functions**:
  - Syntax: `let rec f (x : t1) : t2 = e1 in e2`
  - Semantics: Defines a recursive function `f` with parameter `x` of type `t1`
    and return type `t2`. The function body `e1` may call `f` recursively. The
    function is bound in the scope of `e2`.


Note that all type annotations are optional. Our language does not (yet) have
type inference, so at this point all type annotations are required for
typechecking.

```
Types
-----

t := () | int | bool | t1 -> t2 | t1 * t2 | t1 + t2 | list t | ref t | lazy t | (t)

Terms
-----

e := let x = e in e
   | let rec f (x : t) : t = e in e
   | let rec f x : t = e in e
   | let rec f (x : t) = e in e
   | let rec f x = e in e
   | fun (x : t) -> e | fun x -> e
   | e e
   | x
   | true | false
   | if e then e else e
   | e || e | e && e
   | n
   | e + e | e - e | e * e | e / e
   | e < e | e <= e | e > e | e >= e | e == e | e && e | e || e
   | not e
   | (e, e)
   | fst e
   | snd e
   | inl[t] e | inl e
   | inr[t] e | inr e
   | case e of | inl x -> e | inr y -> e
   | e := e
   | !e
   | ref e
   | nil[t] | nil t
   | e::e
   | case e of | nil -> e | x::xs -> e
   | lazy e
   | force e
   | ()
   | (e)

where x, y are variables
```


### Associativity and Precedence

The following rules define the associativity and precedence of MiniML operators
so that the grammar is unambiguous. The rules are given from the highest to
the lowest precedence.

Expressions:

- Parentheses: `(e)`
- Projections: `fst e`, `snd e`, injections: `inl(t) e`, `inr(t) e`, lazy and force: `lazy e`, `force e`
- Dereference: `!e`
- Function application: `e1 e2` (left-associative)
- Unary negation: `not e`
- Multiplicative operators: `*`, `/` (left-associative)
- Additive operators: `+`, `-` (left-associative)
- List cons: `::` (right-associative)
- Comparison operators: `<`, `<=`, `>`, `>=`, `==` (non-associative)
- Conjunction: `&&`
- Disjunction: `||`
- Assignment: `:=`
- Let binding: `let x = e1 in e2`, `let rec f (x : t) : t = e1 in e2`, conditional: `if e then e1 else e2`,
  case analysis: `case e of | inl x -> e1 | inr y -> e2`, `case e of | nil -> e1 | x::xs -> e2`,
  lambda abstraction: `fun (x : t) -> e`

Types:
- Parentheses: `(t)`
- Reference and lazy types: `ref t`, `lazy t`, `list t`
- Product type: `*` (left-associative)
- Sum type: `+` (left-associative)
- Arrow: `->` (right-associative)


## Directory Structure

The project directories are structured as follows:

### `src/`
The source directory for MiniML, containing all core language definitions and functionality.

- **`MiniML/Syntax.hs`**: Defines the abstract syntax of MiniML types and expressions.
- **`MiniML/Print.hs`**: Provides pretty-printing facilities for MiniML types and expressions.
- **`MiniML/Error.hs`**: Handles error reporting and management.
- **`MiniML/Lex.x`**: Defines the lexer for MiniML using Alex.
- **`MiniML/Parse.y`**: Defines the parser for MiniML using Happy.
- **`MiniML/TypeCheck.hs`**: Implements type checking and type inference.
- **`MiniML/Eval.hs`**: Implements the interpreter/evaluator.
- **`MiniML/ClosureConv.hs`**: Implements closure conversion transformation.
- **`MiniML/Lazy.hs`**: Implements `lazy` and `force` as derived forms.
- **`MiniML.hs`**: A top-level module that exports all MiniML components.

### `CLI/`
Contains code for the command-line interface (CLI) executable.

- **`CLI/Main.hs`**: Implements the top-level executable for MiniML.

### `test/`
Contains the test suite for MiniML that includes property-based testing using QuickCheck.

- **`test/Main.hs`**: Defines and runs the tests.
- **`test/Gen.hs`**: Implements random data generators for property-based testing.

### `examples/`
Contains various small MiniML programs.

## Building and Using MiniML

The following commands should be executed in the root MiniML directory.

- To build the executable use:

  `cabal build miniML`

- To run the executable use:

  `cabal run miniML -- --<option> <file>`

  where `<option>` is one of the following:

  - `--pretty-print`: Pretty-prints the MiniML source code.
  - `--pretty-print-cc`: Pretty-prints the closure-converted code.
  - `--type-check`: Type-checks a MiniML program and prints its type.
  - `--eval`: Evaluates the MiniML program and prints the result.
  - `--eval-cc`: Evaluates the closure-converted MiniML program and prints the result.

- To build the test suite use:

  `cabal build`

- To run the test suite use:

  `cabal test`

- To clean the build use:

  `cabal clean`


## MiniML Playground

You can enter the REPL with all the MiniML libraries loaded with the following command:

`cabal repl lib:miniML`

This provides an interactive environment that is very helpful for debugging and
experimenting with MiniML. For example, you can type the following sequence of
commands:

```
ghci> Right exp = parse $ lexer $ "(fun (x : int) -> x + 1) 42"
... some warning about non-exhaustive pattern matching ...
ghci> :t exp
exp :: Exp
ghci> printExp exp
(fun ( x : int ) -> x + 1) 42
ghci> typeCheckTop exp
Right TInt
```

You may want to write your own helper functions to facilitate debugging and
experimentation.

## Known Bugs

Below is a list of known bugs in the MiniML implementation. Please report any
additional bugs to the instructor. Contributions to bug fixes are welcomed.

- Expressions like `(n-1)` are incorrectly parsed as `n (-1)` (interpreted as `n`
  applied to `-1`). Use spaces  e.g., `(n - 1)`