# Assignment 6 (120 points)

You are given a lexer, parser, typechecker and interpreter for the language
MiniML. A description of the language, build instructions and the usage of the
typechecker and evaluator are described in `README.md`.

## Deliverables
Submit the files `TypeCheck.hs`, `ClosureConv.hs` and `Lazy.hs` to the Helios
submission page. Do not submit zip files. Your files should compile with the
rest of the cabal project without any modification to the given code.

## Part 1: Closure Conversion (60 points)
In the last assignment, we saw that functions are evaluated to closure values:
pairs consisting of the code together with the environment of the function.

A common way to implement languages with first-class functions is to employ a
_closure conversion_ pass that explicitly converts function values to closures.
In this way, a higher-order language can be compiled to a first-order language
where functions are represented as data structures (pairs of code and environment).

After such a pass, closures need not be represented as special runtime values, but
can be implemented as simple tuples containing a code pointer and an
environment. Typically, after such a pass all functions can be un-nested to the
top-level of a program (but we will not do this as part of this assignment).

In the file `ClosureConv.hs` fill in the closure conversion transformation. 

A program must evaluate to the same value before and after closure conversion. 
For example: 

```
> cabal run miniML -- --eval examples/fold.ml
10
> cabal run miniML -- --eval-cc examples/fold.ml
10
```

### Implementation 

The key idea of closure conversion is to transform every function into a pair
(tuple) containing:
1. The code of the function (with an extended parameter that includes the
   environment)
2. The environment capturing all free variables in the function body

#### Converting Functions 

A lambda abstraction `fun (x : t) -> e` is converted as follows:

1. **Compute free variables**: Find all free variables in `e` excluding the
   parameter `x` (you can use the function `freeVars` in the file
   `Syntax.hs`). Let's call this set `{fv₁, fv₂, ..., fvₙ}`.

2. **Create environment tuple**: Package the free variables into a tuple `(fv₁, fv₂, ..., fvₙ)`.

3. **Transform function body**: The function now takes a pair `(x, env)` as its argument instead of just `x`.
   Recursively transform the body `e`, and at the beginning of the transformed function, unpack
   the environment by binding each `fvᵢ` to `proj i env`.

4. **Create closure**: Return a tuple `(transformed_function, environment)`.

For example, consider:
```ocaml
let y = 11 in
let z = 42 in
fun (x : int) -> x + y * z
```

The free variables of the function are `y` and `z`. This gets converted to:
```ocaml
let y = 11 in
let z = 42 in
let _code = fun (_arg : int * (int * int)) -> 
  let x = proj 0 _arg in
  let _env = proj 1 _arg in
  let y = proj 0 _env in
  let z = proj 1 _env in
  x + y * z
in
let env = (y, z) in
(_code, env)
```

You will need to do this for recursive (`let rec`) functions as well in a
similar way. Be careful to correctly compute free variables and handle recursion
appropriately. 

#### Converting Function Applications

When we have a function application `e1 e2`, we cannot simply apply `e1` to `e2`
because after closure conversion, `e1` evaluates to a closure (a pair), not a function.

The conversion proceeds as follows:

1. **Transform subexpressions**: Recursively convert both `e1` and `e2`
2. **Extract closure components**: 
   - Let `_clo = transformed(e1)`
   - Extract the code: `_fun = proj 0 _clo`
   - Extract the environment: `_env = proj 1 _clo`
3. **Apply with environment**: Call the function with a pair of the argument and environment:
   `_fun (transformed(e2), _env)`

For example, the application `f 42` where `f` is a closure becomes:
```ocaml
let _clo = f in
let _fun = proj 0 _clo in
let _env = proj 1 _clo in
_fun (42, _env)
```

This ensures that when the function code executes, it receives both its argument
and the captured environment containing all the free variables.

#### Important Notes on Binder Names

Your transformation will introduce new binders (like `_clo`, `_fun`, `_env`, `_code`, `_arg`).
Be careful that these new binders:
- Do not shadow existing binders in the program (as this would change the program's semantics)
- Do not shadow each other

You can assume that all binders in the source program start with a lowercase letter.
Therefore, your transformation can safely introduce binders starting with an underscore
(like `_x`) without risking name collisions with existing binders.

## Part 2: Lazy and Force (60 points)
We extend the type system of our language with a new type `lazy t` that represents 
a suspended computation of type `t`. 

```
t := ... | lazy t
```

Correspondingly, we extend our language with two operators `lazy e` and `force e`: 

```
e := ... | lazy e | force e
```

The operator `lazy e` suspends the computation of `e`, and the operator `force e`
forces its evaluation. Forcing a suspended computation evaluates it and
memoizes the result so that any subsequent force operation uses the
already computed value.

The following example should evaluate to 42.

```
let r : ref int = ref 1 in
let x : lazy int = lazy (let u : () = r := !r + 5 in !r) in
let y : lazy () = lazy (r := 24) in
let f : lazy int -> int = fun (x : lazy int) -> force x * (force x + 1) in
!r * f x
```

In the abstract syntax tree of MiniML, `lazy e` and `force e` are represented as
`Primitive p "lazy" e` and `Primitive p "force" e`, where `p` is the source code
position.

1. In `TypeCheck.hs`, fill in the type-checker for `lazy` and `force`. (6 points)

2. In `Lazy.hs`, fill in the definitions of `lazy` and `force` as derived forms 
   using the other constructs of the language. (40 points)

3. Assume that the language has user-defined algebraic types like 
   ML and OCaml. Answer the following questions (write your answers inside the 
   designated space in the file `Lazy.hs`). Your answers should be in ML-like pseudocode.
   
   a) How would you define a stream (lazy list)? (7 points)
   
   b) How would you implement a lazy computation of the n-th Fibonacci number? (7 points)


   

