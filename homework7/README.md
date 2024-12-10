# MiniML

## Syntax

MiniML is a simply typed lambda calculus extended extended integers, booleans,
unit, product types, sum types, and references. Its concrete syntax and a brief
description of each language construct is given below.

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
    - `inl(t) e`: Constructs a value of the left type.
    - `inr(t) e`: Constructs a value of the right type.
  - Elimination form: `case e of | inl x -> e1 | inr y -> e2`.
  - Notes: Constructors os sum types are annotated with the type of the other
    component of the sum type, to enable type checking. For example, `inl(int)
    true` has type `int + true` and `inr((int,int)) 42` has type `int * int + true`.

- **References**:
  - Type: `ref t`
  - Introduction form: `ref e` (creates a reference).
  - Elimination forms:
    - `!e`: Dereferences the value stored in a reference.
    - `e1 := e2`: Updates the value of the reference `e1` to the value of `e2`.

- **Let Bindings**:
  - Syntax: `let x : t = e1 in e2`
  - Semantics: Introduces a variable `x` with type `t` bound to the value of
    `e1` in the scope of `e2`.

- **Recursive Functions**:
  - Syntax: `let rec f (x : t1) : t2 = e1 in e2`
  - Semantics: Defines a recursive function `f` with parameter `x` of type `t1`
    and return type `t2`. The function body `e1` may call `f` recursively. The
    function is bound in the scope of `e2`.

```
Types
-----

t := () | Int | Bool | t1 -> t2 |  t1 * t2 | t1 + t2 | ref t | (t)

Terms
-----

e := let x = e in e
   | let rec f (x : t) : t = e in e
   | fun (x : t) -> e
   | e e
   | x
   | true | false
   | if e then e else e
   | e || e | e && e
   | n
   | e + e | e - e | e * e | e / e
   | e < e | e <= e | e > e | e >= e | e == e | e && e | e || e
   | ~ e
   | (e, e)
   | fst e
   | snd e
   | inl(t) e
   | inr(t) e
   | case e of | inl x -> e | inr y -> e
   | e := e
   | !e
   | ref e
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
- Reference: `ref e`, dereference: `!e`, projections: `fst e`, `snd e` ,
  injections: `inl(t) e`, `inr(t) e`
- Function application: `e1 e2` (left-associative)
- Unary negation: `~e` (right-associative)
- Multiplicative operators: `*`, `/` (left-associative)
- Additive operators: `+`, `-`(left-associative)
- Comparison operators: `<`, `<=`, `>`, `>=`, `==` (non-associative)
- Conjunction: `&&`
- Disjunction: `||`
- Assignment: `:=`
- Let binding: `let x = e1 in e2`, `let rec f (x : t) : t = e1 in e2`, conditional: `if e then e1 else e2`,
  case analysis: `case e of | inl x -> e1 | inr y -> e2`, lambda abstraction: `fun (x : t) -> e`

Types:
- Parentheses: `(t)`
- Reference type: `ref t`
- Product type: `+` (left-associative)
- Sum type: `+` (left-associative)
- Arrow: `->` (right-associative)

## Exercise Objectives

The project defines a lexer and a parser for MiniML, along with pretty printing
facilities and a semi-complete typechecker.

The exercise involves completing the following components (Total points: 100).

1. Extend the type checker to handle recursive functions and references.
   (TODO 1, file `src/MiniML/Typechecking.hs`, 20 points)
2. Write an environment-base interpreter that supports all MiniML operations and
   accurately implements the semantics of MiniML.
   (TODO 2, file `src/MiniML/Typechecking.hs`, 30 points)
3. Test your definitions using QuickCheck.
   - Write a well-typed term generator.
   - Use the generator to test that well-typed expressions produced by the
     generator pass the type checker.
   - Test type soundness: if an expression is well-typed, it should evaluate
     successfully to a value of the same type. 
     (TODO 3, file `src/test/Main.hs`, 50 points)

### Further instructions
- Only edit the files `src/MiniML/Typecheck.hs`, `src/MiniML/Eval.hs`,
  `test/Main.hs`, `test/Gen.hs`
- Do not edit existing code unless instructed to do so.
- Do not change the directory structure and file names.
- Your solutions should work without any modification to existing code.
- The submitted code should compile.

## Directory Structure

The project directories are structured as follows:

### `src/`
The source directory for MiniML, containing all core language definitions and functionality.

- **`MiniML/Syntax.hs`**: Defines the abstract syntax of MiniML types and expressions.
- **`MiniML/Print.hs`**: Provides pretty-printing facilities for MiniML types and expressions.
- **`MiniML/Error.hs`**: Handles error reporting and management.
- **`MiniML/Typechecker.hs`**: Implements the MiniML typechecker (TODO 1).
- **`MiniML/Values.hs`**: Defines data types for MiniML values, used by the interpreter.
- **`MiniML/Eval.hs`**: Implements the MiniML interpreter (TODO 2).
- **`MiniML/Lex.x`**: Defines the lexer for MiniML.
- **`MiniML/Parse.y`**: Defines the parser for MiniML.
- **`MiniML.ml`**: A top-level module that exports all MiniML components.

### `CLI/`
Contains code for the command-line interface (CLI) executable.

- **`CLI/CLI.hs`**: Implements the top-level executable for MiniML.

### `test/`
Contains the test suite for MiniML that includes property-based testing using QuickCheck.

- **`test/Main.hs`**: Defines and runs the tests (TODO 3).
- **`test/Gen.hs`**: Implements random data generators for property-based testing.

### `examples/`
Contains various small MiniML programs.

## Building and Using MiniML

The following commands should be executed in the root MiniML directory.

- To build the executable use:

  `cabal build miniML`

- To run the executable use:

  `cabal run MiniML -- --<option> <file>`

  where `--<option>` is one of the following:

  - `--pretty-print`: Formats and prints the MiniML source code.
  - `--type-check`: Type-checks the MiniML program and reports its type.
  - `--eval`: Evaluates the MiniML program and outputs the result.

- To build the test suite use:

  `cabal build`

- To run the test suite use:

  `cabal test`

- To run the test suite type

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

Similarly, you can enter a REPL for the test suite with:

`cabal repl test`

Then you can type commands like the following:

```
ghci> import Test.QuickCheck
ghci> quickCheck typeSoundness
+++ OK, passed 100 tests.
```

## Known Bugs

Below is a list of known bugs in the MiniML implementation. Please report any
additional bugs to the instructor. Contributions to bug fixes are welcomed.

- Expressions like `(n-1)` are incorrectly parsed as `n (-1)` (interpreted as `n`
  applied to `-1`). Use spaces  e.g., `(n - 1)`