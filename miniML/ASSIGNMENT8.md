# Assignment 8 (120 points)

## Description
This assignment extends MiniML with type inference. The top-level type inference
function should be implemented in `src/MiniML/Infer.hs`. A new command-line 
option `--infer` has been added in CLI.hs to invoke the type inference algorithm.

## Deliverables
Submit the file `Infer.hs` to the Helios submission page.
Do not submit zip files. Your file should compile with the rest of the cabal
project without any change to the given code.

## Type Inference for MiniML

Type inference (or reconstruction) is a technique that deduces the type of an
expression in a typed language, even when some type information (i.e., type
annotations) is missing. It is a core feature in many contemporary programming
languages, such as OCaml, Haskell, Rust, TypeScript, Scala, and Kotlin. The type
inference algorithm studied here is the classic [Algorithm W proposed by Robin
Milner in 1978](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/milner-type-polymorphism.pdf). 

The objective of this assignment is to implement type inference for MiniML. The
given MiniML language is almost the same as the language from Assignment 6, with 
the only difference being that all type
annotations may be omitted.

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
_fresh type variable_: a type variable that has not yet been used in the
program, the environment, or the constraints.

Some rules for constraint-based typing are given below. The rules can be
extended in a mostly straightforward way to handle all constructs of MiniML.

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


        Γ ⊢ e1 : t1 | C1       Γ ⊢ e2 : t2 | C2       Γ ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------CT-ITE
   Γ ⊢ if e1 then e2 else e3 : t2 | { t1 = bool, t2 = t3 } ∪ C1 ∪ C2 ∪ C3


         Γ ⊢ e : t | C
-----------------------------------CT-Inl            α is fresh
      Γ ⊢ inl e : t + α | C 


         Γ ⊢ e : t | C
----------------------------CT-Inr              α is fresh
    Γ ⊢ inr e : α + t | C 


      Γ ⊢ e1 : t1 | C1       Γ, x : α ⊢ e2 : t2 | C2       Γ, y : β ⊢ e3 : t3 | C3
-------------------------------------------------------------------------------------------CT-Case             α, β are fresh
    Γ ⊢ case e1 of inl x -> e2 | inr y -> e3 : t2 | {t1 = α + β, t2 = t3} ∪ C1 ∪ C2 ∪ C3

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

Given `Γ ⊢ e : t | C` and a `σ` that is a solution of the set of constraints `C`, 
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
    if t1 == t2 then unify(C')
    else if t1 == α and α not free in t2 then unify([α |-> t2]C') ∘ (α |-> t2)
    else if t2 == α and α not free in t1 then unify([α |-> t1]C') ∘ (α |-> t1)
    else if t1 = t11 -> t12 and t2 = t21 -> t22 then unify({t11 = t21, t12 = t22} ∪ C')         (similarly for other type constructors)
    else FAIL
```


The side conditions that a type variable must not occur free in the type is
known as _occurs check_ and ensures that the solution will not involve circular
substitutions. 

It can be proved that the unification algorithm always terminates (can you argue
why?) and it will always return the most general unifier if one exists (theorem
22.4.5, _Types and Programming Languages_).


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

To get around this limitation, the type of `f` should be assigned the
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
   `σ(t1)` and do not appear anywhere else in the typing environment, as this
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


## Objectives (Total points: 120)

1. Implement monomorphic type inference for MiniML (60 points)
2. Extend the monomorphic type inference with let-polymorphism (30 points)
3. Extend the approach with the ability to define polymorphic recursive functions (20 points)
   
   This means that functions defined with let-rec can be used with various types
   after their definitions (for example see `examples-typeinf/pass/map1.ml`).

4. Bonus: Answer the question in the file Infer.hs. (10 points)

### Further instructions
- You can ignore primitive functions and `lazy` and `force` operators.
- You can assume that tuples are always 2-tuples.
- A new set of examples have been added in the directory `examples-typeinf`
- Only edit the file `src/MiniML/Infer.hs`
- Do not edit existing code unless instructed to do so.
- Do not change the directory structure and file names.
- Your solutions should work without any modification to existing code.
- The submitted code should compile.