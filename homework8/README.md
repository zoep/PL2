# Type Inference for MiniML

Type inference (or reconstruction) is a technique that deduces the type of an
expression in a typed language, even when some type information (i.e., type
annotations) is missing. It is a core feature in many contemporary programming
languages, such as OCaml, Haskell, Rust, TypeScript, Scala, and Kotlin. The type
inference algorithm studied here is the classic [Algorithm W proposed by Robin
Milner in 1978](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/milner-type-polymorphism.pdf). 

The objective of this exercise is to implement type inference for MiniML. The
given MiniML language is nearly identical to the language from exercise 7. The
language is extended with lists and references are omitted. Crucially, all type
annotations may be omitted. The formal description of the syntax is given at the
end of the file.

A brief description of type inference is given below. For a more detailed
explanation refer to chapter 22 of _Types and Programming Languages_. You may find [these lecture
notes](https://courses.softlab.ntua.gr/pl2/2007b/slides/slides-01-lambda-typeinfer.pdf)
useful. 

## Monomorphic Type Inference

The _algorithm W_ for type inference can be broken down into two main stages:

1. **Constraint Generation**: Collecting constraints on types based on the
   expression's structure.

2. **Unification**: Solving the constraints to deduce the most general type of
   an expression.


### Type Variables

The abstract syntax of types is extended with type variables, which represent
unknown types during constraint generation. These variables are introduced when
encountering terms whose types are not yet known. Finding a solution of the
generated constraints amounts to finding a _substitution_ that maps type
variables to types.

Note that, for simplicity, the user cannot provide type annotations that include
type variables in the concrete syntax of MiniML.


### Constraint Generation

The first step of type inference is traversing the term and generating typing
constraints. This step does not perform type checking but instead produces
constraints of the form `t1 = t2`, which means that the type `t1` must be equal
to `t2`. These constraints will be solved during unification.

The constraint typing relation is written `Γ ⊢ e : t | C` and denotes that the
term `e` has type `t` under the constraints `C`.

Whenever the algorithm encounters a term with an unknown type, it introduces a
_fresh type variable_--—a type variable that has not yet been used in the
program, the environment, or the constraints.

Some rules for constraint-based typing are given below. The rules can be
extended is a mostly straight forward way to handle all constructs of MiniML.

```
      x : t ∈ Γ
----------------------CT-Var
    Γ ⊢ x : t | {} 


        Γ, x : t1 ⊢ e : t2 | C
---------------------------------------------CT-AbsAnnot
    Γ ⊢ (fun x : t1 -> e) : t1 -> t2 | C


        Γ, x : α ⊢ e : t2 | C
---------------------------------------CT-Abs                           α is fresh
    Γ ⊢ (fun x -> e) : α -> t2 | C


             Γ ⊢ e1 : t1 | C1
             Γ ⊢ e2 : t2 | C2        
-------------------------------------------------CT-App                 α is fresh
    Γ ⊢ e1 e2 : α | {t1 = t2 -> α} ∪ C1 ∪ C2



----------------------------CT-True
    Γ ⊢ true : bool | {} 


----------------------------CT-False
    Γ ⊢ false : bool | {} 


        Γ ⊢ e1 : t1 | C2       Γ ⊢ e2 : t2 | C2       Γ ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------CT-ITE
   Γ ⊢ if e1 then e2 else e3 : t2 | { t1 = bool, t2 = t3 } ∪ C1 ∪ C2 ∪ C3


         Γ ⊢ e : t | C
-----------------------------------CT-Inl            α is fresh
      Γ ⊢ inl e : t + α | C 


         Γ ⊢ e : t | C
----------------------------CT-Inr              α is fresh
    Γ ⊢ inr e : α + t | {} 


      Γ ⊢ e1 : t1 | C1       Γ, x : α ⊢ e2 : t2 | C2       Γ, y : β ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------------------CT-Case             α, β are fresh
    Γ ⊢ case e1 of | inl x -> e2  | inr y -> e3 | {t1 = α + β, t2 = t3}  ∪ C1 ∪ C2 ∪ C3

```


### Type Substitutions

After generating constraints `C`, the next step is to find a _substitution_ `σ`
that satisfies all constraints. A substitution maps type variables to specific
types. The goal is to find the most general solution, ensuring any other
solution is a specialization of this one.

A substitution `σ` is a solution for a set of constraints C if `σ(t1) = σ(t2)`
for any `t1 = t2 ∈ C`. 

Moreover, the solution for the set of constraints should be the _most general
one_, meaning that for any other substitution `σ'` that is a solution to the set
of constraints, there exist a substitution `δ` such that `σ' = δ ∘ σ`. 

Given `Γ ⊢ e : t | C` an a `σ` that is a solution of the set of constraints `C`, 
the type `σ(t)` is the _principal_ type of `e`.

The operator `∘` denotes the composition of two substitutions: 
`σ1 ∘ σ2 (t) = σ1 (σ2 (t))`. 


### Unification Algorithm

The unification algorithm for type constraints is given below in pseudocode.
Given a set of constraints, it will find a solution (i.e., a substitution) that
is the _most general unifier_ for the given set of constraints, if such solution
exists, or it will fail otherwise.  


```
unify(C) = case C of
  {} -> []
  {t1 = t2} ∪ C' ->
    if t1 == t2 then unify(C)
    else if t1 == α and α not free in t2 then unify([α |-> t2]C') ∘ (α |-> t2)
    else if t2 == α and α not free in t1 then unify([α |-> t1]C') ∘ (α |-> t1)
    else if t1 = t11 -> t12 and t2 = t21 -> t22 then unify({t11 = t21, t12 = t22} ∪ C')         (similarly for other type constructors)
    else FAIL
```


The side conditions that a type variable must not occur free in the type is
known as _occurs check_ and ensures that the solution will not involve circular
substitutions. 

It can be proved that the unification algorithm always terminates (can you argue
why?) and it will always return the most general unifier is one exists (theorem
22.4.5, Types and Programming Languages).


## Let Polymorphism

Consider the following miniML program: 

```
let f = fun y -> y in
(f 42, f true)
```

Type reconstruction would assign the type `α -> α` to `f` for some fresh type
variable `α` and then will generate constraints `α = int` and `α = bool` for the
type variable `α`. Unification will fail as there is no substitution that can
satisfy such constraints. 

To get around this limitation, the type of `f` should should be assigned the
polymorphic type `∀α. α -> α`, allowing `α` to be instantiated with different
types.

We will extend the above approach to allow for let-polymorphism (also known as
ML-style or Damas-Milner polymorphism). This allows type variables to be
universally quantified, but only at the outermost of the type of a let-bound
variable. This is a restriction of System F that has decidable type checking.

### Type Schemes

To support polymorphism, we introduce type schemes, which allow universal
quantification at the outermost level of a type. Their syntax is:

```
s := t | forall α, s
```

The typing context will now map variables to type schemes. Note, that a type can
be trivially made a type scheme. Therefore, function arguments (which cannot
have a polymorphic type) can still be added to the environment. 

### Inferring Polymorphic Types

In order to infer a polymorphic type for an expression of the form `let x = e1
in e2` during constraint generation, we proceed as follows:

1. We use the constraint typing rules to infer a type `t1` together with a
   constraint set `C1`. 

2. We use the unification algorithm to find a most general solution `σ` and
   apply it to `t1`, to find the most general type `σ(t1)` of `e1`

3. We generalize all the remaining type variables of `σ(t1)`, to obtain a type
   scheme `s1`. For example if `σ(t1)` is `(α -> β) -> α -> β`, then the
   resulting type will be `∀ α β, (α -> β) -> α -> β`.
   
   However, we must be careful to generalize only the variables that are local to
   `σ(t1)` and do not appear anywhere else at the typing environment, as this
   would lead to unsound types. 

   As an example consider the following ill-typed program: 

   ``` 
   fun x -> 
     let f = fun g -> g x in 
     if f (fun z -> ~ z) then 42 else z
   ```
  
   Generalizing the type of `f` without being careful to exclude the type
   variables that are already in the environment would allow us to give a type
   to this program. 

4. We add `x : s1` to the environment and carry on with finding a type and a
   constraint set for `e2`.

5. We modify the constraint typing rule for variables to instantiate the
   generalized typing variables with _fresh_ type variables. 
 

    ```
          x : s ∈ Γ
          t = instantiate(s)
    ---------------------------CT-Var
       Γ ⊢ x : t | {} 
    ```

    For example, if `s = forall α β, (α -> β) -> α -> β`, then the instantiated
    type would be `(γ -> δ) -> γ -> δ` for some type variables  `γ` and `δ` that
    are not used anywhere else.


## Objectives (Total points: 200 + 20 bonus)

1. Implement monomorphic type inference for MiniML (100 points)
2. Extend the monomorphic type inference with let-polymorphism (80 points)
3. Extend the approach with the ability to define polymorphic functions (20 points)
   
   This means that functions defined with let-rec can be used with various types
   after their definitions (for example see `examples/map1.ml`).

4. Adapt the well-typed term generation approach from exercise 7 to test your
   type inference implementation (20 bonus points). 
   
   You don't (necessarily) need to generate polymorphic types. This will get
   significantly harder as not all types will be inhabited. 
   
   If you generate terms of monomorphic types only, type inference may be able
   to infer a more general type scheme. Your property checker should check that
   the monomorphic type is an instance of the more general type scheme.

### Further instructions
- Only edit the files `src/MiniML/Typeinf.hs`, `test/Main.hs`, `test/Gen.hs`
- Do not edit existing code unless instructed to do so.
- Do not change the directory structure and file names.
- Your solutions should work without any modification to existing code.
- The submitted code should compile.

## Syntax

MiniML is a simply typed lambda calculus extended extended integers, booleans,
unit, product types, sum types, and lists. Its concrete syntax and a brief
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
    - `inl e`: Constructs a value of the left type.
    - `inr e`: Constructs a value of the right type.
  - Elimination form: `case e of | inl x -> e1 | inr y -> e2`.

- **Lists**:
  - Type: `list t`
  - Introduction form: `
    - `[]`: empty list
    - `e::es`: list cons 
  - Elimination form: `case e of | [] -> e1 | x:xs -> e2`.

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

t := () | Int | Bool | t1 -> t2 |  t1 * t2 | t1 + t2 | list t | (t)

Terms
-----

e := let x = e in e
   | let rec f (x : t) : t = e in e
   | let rec f (x : t) = e in e
   | let rec f : t = e in e
   | let rec f = e in e
   | fun (x : t) -> e | | fun x -> e
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
   | []
   | e:e
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
- Projections: `fst e`, `snd e` , injections: `inl(t) e`, `inr(t) e`
- Function application: `e1 e2` (left-associative)
- Unary negation: `~e` (right-associative)
- Multiplicative operators: `*`, `/` (left-associative)
- Additive operators: `+`, `-`(left-associative)
- List cons: `::` (right-associative)
- Comparison operators: `<`, `<=`, `>`, `>=`, `==` (non-associative)
- Conjunction: `&&`
- Disjunction: `||`
- Assignment: `:=`
- Let binding: `let x = e1 in e2`, `let rec f (x : t) : t = e1 in e2`, conditional: `if e then e1 else e2`,
  case analysis: `case e of | inl x -> e1 | inr y -> e2`, lambda abstraction: `fun (x : t) -> e`

Types:
- Parentheses: `(t)`
- Reference type: `list t`
- Product type: `+` (left-associative)
- Sum type: `+` (left-associative)
- Arrow: `->` (right-associative)


## Directory Structure

The project directories are structured as follows:

### `src/`
The source directory for MiniML, containing all core language definitions and functionality.

- **`MiniML/Syntax.hs`**: Defines the abstract syntax of MiniML types and expressions.
- **`MiniML/Print.hs`**: Provides pretty-printing facilities for MiniML types and expressions.
- **`MiniML/Error.hs`**: Handles error reporting and management.
- **`MiniML/Typeinf.hs`**: Implements type inference for MiniML.
- **`MiniML/Lex.x`**: Defines the lexer for MiniML.
- **`MiniML/Parse.y`**: Defines the parser for MiniML.
- **`MiniML.ml`**: A top-level module that exports all MiniML components.

### `CLI/`
Contains code for the command-line interface (CLI) executable.

- **`CLI/CLI.hs`**: Implements the top-level executable for MiniML.

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

  `cabal run MiniML -- --<option> <file>`

  where `<option>` is one of the following:

  - `--pretty-print`: Formats and prints the MiniML source code.
  - `--type-inf`: Infer a type for a MiniML program and print it at the standard output.
  
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
ghci> inferTypeTop exp
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
