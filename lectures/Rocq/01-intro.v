From Stdlib Require Import Lists.List Init.Nat.

Import ListNotations.

(** * A Small Introduction to The Rocq Proof Assistant (I): Functional Programming with Proofs **)


(** Rocq is a pure functional programming language and a theorem
    prover. Its underlying formal language is Calculus of Inductive
    Constructions (CiC) which is a dependently-typed, pure functional
    language with inductive types. This small but expressive language
    can be used to write purely functional programs, using a syntax
    similar to the ML family, express logical propositions, and write
    proofs. Coq can be used for:

    - Developing functional programs.

    - Expressing and proving mathematical statements.

    - Writing and proving formal specifications about programs written
      in the same language.

    The proofs can be developed interactively and they are checked for
    validity by Coq's built-in proof checker.

    The core features of the language include:

    - (Recursive) functions and function application

    - Inductive types (a generalization of ML's algebraic data types)

    - Pattern matching on inductive types

    - Type polymorphism

    - Dependent types

    - Coinductive types

    In this course we will use Coq extensively to model programming
    languages and study their properties. But before delving into
    this, we will first learn some basic usage.  *)


(** ** Rocq Code Development and Execution *)

(** Rocq files are commonly developed interactively, as we will do in
    the lectures. For this it is imperative to have an IDE with
    support for interactive Rocq development.

    Rocq also support batch compilation with the `coqc` command
    file `file.v` can also be compiled from the command line, using
    the command `coqc file.v`. This produces

    To execute Rocq code, the Rocq system provides extraction commands,
    that translate Rocq code to a functional language (OCaml, Haskell
    or Scheme). This process erases proofs and all information that is
    not relevant for computation. The files then can be compiled and
    executed as normal OCaml/Haskell/Scheme files. This allows us to
    build software in Rocq that comes with correctness proofs and
    extract it in one of these languages. This software is commonly
    called [certified]. *)


(** ** Rocq Types *)

(** Rocq has very few primitive types:

       - The function type: [->] or [forall _, _].  The type of types:
       - [Type] and [Sort] (a special case of [Type]).  [Prop] the
       - type of logical propositions

    Rocq comes with an extensive #<a
    href="https://coq.inria.fr/doc/V8.19.0/stdlib/">standard
    library</a># that provides common data structures (e.g., booleans,
    list, numbers, pairs, maps, and more). These are not primitives --
    they are defined using inductive types. We will cover many of
    these in this lecture.

    Note: "Primitive Objects" including 63-bit machine integers and
    persistent arrays, have been added to recent versions Rocq, but we
    will not cover them in this class. *)


(** *** Functions *)

(** At the heart of Rocq's language we have functions.  The
    [Definition] keyword allows us to declare a function (or a
    constant). *)


Definition foo (x y : nat) := x * (y + 1).

(** Rocq provides a number of useful commands to interact with the
    system. These are not expressions of the functional language but a
    way to communicate with the system. Some of these are [Check],
    [Print], [Compute], [Search] and others. We will use these
    extensively.

    [Check]: check the type of an expression
    [Print]: print a definition
    [Search]: find definition and lemmas in the current file or
              imported files whose name or type satisfies a number
              of conditions
    [Compute]: evaluate an expression *)


Check foo.

Print foo.

Compute (foo 6 6).


(** **** Polymorphic Functions *)

Definition id_nat (x : nat) := x.

Check id_nat.

(** The above function only works for [nat] -- but it doesn't need to!
    Its definition makes no assumptions on the type of the input.

    Let's try to define the identity function in a polymorphic way: *)


Fail Definition id x := x.


(** The above definition fails as Rocq cannot infer the type of [x].
    We must pass the **type argument** explicitly: *)
   

Definition id (A : Type) (x : A) : A := x.

(** The above definition takes as arguments a _type_ parameter [A], a
    parameter [x] of type [A] and returns [x]. *)

Check id.


(** Prints:

[id : forall A : Type, A -> A] *)

(** The above type has a *for all quantifier*.

    This is similar to the type constructor [->], but allows us to
    find the type to a name (here [Type] is bound to [A] and use it
    in the rest of the type.

*)


(** When applying [id] to an argument we must also provide the
    concrete type parameter.

    For example, we want to apply the [id] function to a natural
    number, say 3, and a boolean value, say [true]. To do that we must
    explicitly provide the type parameters, [nat] and [bool]
    respectively. *)

Compute (id nat 3).

Compute (id bool true).

(** We can also apply [id] to [id] itself.

    Quiz: what will the concrete value of the type parameter [A] be in this case?

*)

Fail Check (id _ (* ? *) id).


(** Note: in languages like ML or OCaml this call is not possible like
    this, as they only allow type quantification at the outermost
    position in the type of a definition (prenex polymorphism).  That
    is, type variables may not be instantiated with polymorphic types
    as we did above. Rocq has a more expressive type system that lets
    us do this kind of thing. *)

Compute (id (forall A : Type, A -> A) id).

(** Prints:

[fun (A : Type) (x : A) => x : forall A : Type, A -> A] *)


(** The above syntax introduces an anonymous function. *)

Check (fun (A : Type) (x : A) => x).


(** The following two definitions are equivalent *)


Definition id_1 (A : Type) (x : A) : A := x.

Definition id_2 := fun A (x : A) => x.


(** Since the result of the last application is a polymorphic
    function, we can also apply it to arguments of different types. *)

Compute (id (forall A : Type, A -> A) id nat 3).

Compute (id (forall A : Type, A -> A) id bool true).

Compute (id (forall A : Type, A -> A) id (forall A : Type, A -> A) id).


(** Functions in Rocq must be _total_. This means they must return an
    output for each element of their domain. They cannot loop forever
    or error out. This is important for the logical consistency of the
    system. We will revisit this concept again in the course. *)


(** **** Implicit Parameters*)

(** It is not always convenient to explicitly provide the type of the
    arguments. In many cases, these can be inferred by type inference.
    Rocq lets us omit them either using an underscore, or by declaring
    in a definition that some arguments are implicit using curly
    braces [{ ... }].

    For example: *)

Compute (id _ 3).

(** In the above, Rocq figures out that the type argument is [nat] *)

(** We can also tell Rocq that an argument is implicit during the
    definition of the
    function. *)

Definition id' {A : Type} (x : A) : A := x.

(** This way, we don't have to provide a type argument for [id'], [A]
is implicit: *)

Check (id' 3).

(** Using the [@] symbol before a function's name, we can tell Rocq to
    treat all arguments as explicit. *)

Check (@id' nat 3).


(** ** Proofs *)

(** Rocq allows the development of mathematical proofs in an
    interactive way.

    During a proof we have a _goal_ that is the statement to be
    proved. We also have a _proof context_ that has premises that we
    know to be true at a certain point during the proof.

    Proof development in Rocq is done through a language of so-called
    _tactics_. Tactics allow us to apply rules of logical reasoning to
    the goal and the proof context.

    Tactics construct an internal representation of the proof, called
    a _proof term_. This is then checked by Rocq's proof checker for
    validity.  For now, we will treat this as a black box. *)

Lemma id_equality : forall (A : Type) (x : A), id A x = x.
Proof.
  (* The [intros] tactic moves universally quantified variables and
     and implications from the goal to the proof context. *)
  intros A x.

  unfold id. (* The [unfold id] tactic replaces [id] with its
                definition. *)

  reflexivity. (* [reflexivity] proves a goal of the form [e = e], for
                  some expression [e]. *)

  (* A complete proof ends with [Qed] which exits the interactive
     proof mode.  It stands for the Latin phrase "quod erat
     demonstrandum" which is traditionally used in mathematical text
     to finish a proof. *)
Qed.

(** Now [id_equality] is a defined term and its type is exactly the
    statement we proved. *)

Check id_equality.

Print id_equality. 

(** *** Skipping Parts of a Proof *)

(** When developing large and complex proofs, it is often convenient
    to assume some part of them to make progress and come back to them
    later. This can be done with the [admit] and [Admitted]
    keywords. *)

Lemma id_equality_admitted : forall (A : Type) (x : A), id A x = x.
Proof.
  intros A x.
  unfold id. 
  admit. (* proves the goal! *)

  (* A proof with admitted or unfinished subproofs cannot be completed
     using [Qed].  It has to end with the keyword [Admitted] that
     assumes the current proof without it being finished. *)
Admitted.

(** An admitted proof can be used in other proofs to derive facts.
    Admitting proofs must be used with caution, as admitting an
    invalid statement makes the system inconsistent as we can derive
    other false statements when using it. *)

(** ** Inductive Types *)

(** *** The Structure of an Inductive Type *)
      
(** Inductive types in Rocq are a generalization of ML's algebraic
    datatypes. The definition of an inductive type tells us how we can
    build values of this type.

    The inductive type is an enumeration of different ways to build
    values that belong to this type. *)


Inductive day :=
| Mon : day (* optionally we can write the type of each constructor *)
| Tue
| Wed
| Thu
| Fri
| Sat
| Sun.


(** We can build values of type [day] and also examine them (i.e.,
    destruct them) using pattern matching *) 

Definition my_favorite_day : day := Fri.

Definition is_PL_day (x : day) : bool :=
  match x with
  | Fri => true
  | _ => false (* wildcard: catch-all case *)
  end.

Print is_PL_day.

(** All possible cases of a pattern matching must be defined (either
    explicitly or with a wildcard).  Otherwise the function is not
    total and Rocq rejects it. *)  

Fail Definition is_PL_day_fail (x : day) : bool :=
  match x with
  | Fri => true
  | Mon => false
  | Thu => false
  end.

(** We will go through some very common inductive types in the Rocq
    standard library *)

(** *** Booleans *)

(** Note: Because Rocq's standard library already includes these
    definitions, we put them in a separate namespace that we create
    using a [Module].

    If we don't explicitly import the module, these names will refer
    to the definitions in the standard library. *)

Module Bool.

  
  (** The boolean data type is an inductive type with two constructors:
      [true] and [false] *)

  Inductive bool : Type :=
  | true : bool
  | false : bool.

  (** We can define functions that operate on this type. We define
      negation, conjunction and disjunction.*)
  
  Definition negb (x : bool) :=
    match x with
    | true => false
    | false => true
    end.

  Definition andb (x y : bool) :=
    match x with
    | true => y
    | false => false
    end.

  Definition orb (x y : bool) :=
    match x with
    | true => true
    | false => y
    end.

(** Again, we can ask Rocq what is the type of a definition: *)

Check true.

(** Prints:

[true : bool]

*)


Check andb.

(** Prints:

[andb : bool -> bool -> bool]

*)


(** We can also ask it to print a definition. *)

Print andb.

(** We can use such functions to perform computations on booleans. *)

Compute (negb true).

(** Prints:

[= false : bool]

*)

Compute (andb (orb false true) true).

(** Prints:

[= true : bool]

*)


(** Rocq allows us to define syntax extensions that modify the way
    Rocq parses and prints objects. This can be done with the
    [Notation] command.

    Below, we use it to define familiar syntax for boolean
    operators. *)

Notation "x && y" := (andb x y) (at level 40, left associativity).

Notation "x || y" := (orb x y) (at level 50, left associativity).

(** We can ask Rocq to give us information about a particular notation
    using the command [Locate]. *)

Locate "&&".

Check (true || false).


(** Tip: Rocq IDEs provide keybindings that allow us to quickly use
    [Print], [Check], [Search], and [Locate].


<<
       | VsCode + PG keybindings extension | Emacs + PG
-------------------------------------------------------------------------
Print  | shift+ctrl+P | ctrl+c ctrl+a ctrl+p
Check  | shift+ctrl+S | ctrl+c ctrl+a ctrl+c
Search | shift+ctrl+K | ctrl+c ctrl+a ctrl+a
Locate | shift+ctrl+L | ctrl+c ctrl+a ctrl+l
>>

You can modify these keybindings from your editor's settings.
 *)


(** Crucially, we can prove facts about our definitions. *)

Lemma or_true_false : true || false = true.
Proof.

  (* The [simpl] tactic simplifies the goal performing possible
     computation steps *)
  simpl.

  (* The reflexivity tacric proves an equality that has the same term on
     both sides *)
  reflexivity.
Qed.


(** Let's attempt to prove more interesting facts about booleans *)

Lemma de_morgan_law : forall (x y : bool), (* universal quantifier *)
    (negb x) && (negb y) = negb (x || y).
Proof.
  (* The [intros] tactic moves universally quantified variables and
     premises from the goal to the proof context. *)
  intros x y.

  (* We proceed by case analysis. We can do this with the tactic
     [destruct]. [destruct] will introduce two proof goals, one for
     when [x = true] and one for when [x = false]. *)
  destruct x.

  (* Case 1: x = true *)
  - (* This is a bullet. We use them to organize the proof script into
       cases. They are optional but are good practice in general. *)
    simpl. reflexivity.

  (* Case 2: x = false *)
  - simpl. reflexivity.

Qed.

(** Rocq also has conditional statements (if-then-else) that can be
    used instead of pattern matching to write the above functions: *)

Definition orb' (b1:bool) (b2:bool) : bool := if b1 then true else b2.

(** Recall that [bool] is not a primitive type. The if-then-else
    construct is just syntactic sugar for pattern matching and can be
    used to eliminate _any_ inductive type with exactly two
    constructors.  The "then" branch is taken if the guard evaluates
    to the first constructor of the type and the "else" branch is
    taken if the guard is evaluated to the second constructor of the
    type. *)

End Bool.

(** *** Natural Numbers *)

(** We can represent numbers in a variety of ways, using different
    bases. Common examples are binary (base-2) and decimal (base-10)
    representations.

    For example, we can use the [bool] datatype to define a binary
    number with a certain bit-width. *)

Inductive bin_num4 : Type :=
| Num : bool -> bool -> bool -> bool -> bin_num4.

(** [Num] is a constructor that takes 4 arguments and returns a
    [bin_num4 ].  Its type is: *)

Check Num.

(** Prints:

[Num : bool -> bool -> bool -> bool -> bin_num4]

**)

(** We could also define operations on such numbers (e.g., addition,
    multiplication, etc). You can try this as an exercise at home.

    However, we would like a representation for truly infinite
    mathematical numbers, and not numbers of certain bit width.

    We could define a datatype for infinite binary numbers, and such
    representations are included in Rocq's standard library.  Binary
    numbers, however, are a good way for representing numbers on a
    machine and performing operations on them with logical circuits.
    But when it comes to proofs, they are not a very convenient
    representation.

    We will use a representation that is simpler than binary numbers:
    unary numbers (base 1). That is, we will use a single digit to
    represent positive numbers. The idea is similar to counting using
    tally marks:

    I represents 1, II represents 2, III represents 3, and so on.

    We can define this as an inductive type in Rocq:

*)

Module Nat.

  Inductive nat :=
  | O : nat
  | S : nat -> nat.

  (** Intuitively, the constructor [O] represents zero and [S] applied
      to any number represents the successor of this number.

      In mathematical language, we would describe the set of [nat]s as
      the smallest set that

      - [O] is in the set

      - if [n] is in the set then [S n] is in the set

     These are often called Peano numbers, as the mathematician Peano
     used this representation in his axiomatic formulation of natural
     numbers in the 19th century.

   *)

  Check (S (S (S (S O)))). (* Which number is this? *)

  (** Let's define some useful functions on natural numbers. *)

  (** The predecessor of a number *)
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n => n
    end.

  (** A function that check if a number is zero *)
  Definition is_zero (n : nat) : bool :=
    match n with
    | O => true
    | S _ => false
    end.

  (** **** Recursion *)

  (** Since [nat] is a recursive datatype, we can define recursive
      functions on them.  Recursive functions are defined using the
      [Fixpoint] keyword.  *)

  (** Addition **)
  Fixpoint add (n1 n2 : nat) : nat :=
    match n1 with
    | O => n2
    | S n1' => S (add n1' n2)
    end.

  (** Subtraction **)
  Fixpoint sub (n1 n2 : nat) : nat :=
    match n1 with
    | O => O
    | S n1' => match n2 with
               | O => n1
               | S n2' => sub n1' n2'
               end
    end.

  (** We could also write this as: *)
  Fixpoint sub' (n1 n2 : nat) : nat :=
    match n1, n2 with
    | O, _ => O
    | _, O => n1
    | S n1', S n2' => sub' n1' n2'
    end.

  (** This is just syntactic sugar for nested pattern matching: *)
  Print sub'.

  (** Note that the argument to the recursive call of [add] is n1'
      which is structurally smaller than n1. The same is true for both
      arguments of the function [sub]. Rocq requires that there is one
      argument that gets structurally smaller in each recursive call.
      This guarantees that all functions will terminate which is
      necessary for logical consistency.

      Such functions are called structurally recursive. Trying to
      define a non structurally recursive function will produce an
      error.

      Note: In Rocq, there are ways to define generally recursive
      functions (that terminate but are not structurally recursive),
      but we will not see this in this course.  *)


  Fail Fixpoint test (n : nat) : nat :=
    match n with
    | O => O
    | _ => test (sub n (S (S O)))
    end.


  (** We can also define boolean equality on natural numbers *)
  Fixpoint eqb (n1 n2 : nat) : bool :=
    match n1, n2 with
    | O, O => true
    | S n1', S n2' => eqb n1' n2'
    | _, _ => false
    end.

End Nat.

(** From now on we will use the standard library's [nat], which is
    identical to our definition above. **)

Print nat.
Print add.


(** Searching about [nat] will retrieve all the definitions (including
    theorems) that involving [nat]. This comes in quite handy in
    proofs. *)

Search nat.

(** Coq has defined notation for natural numbers that lets us use
    ordinary decimal notation for natural numbers and also notation
    for arithmetic operations. *)

Check 5.

Set Printing All.

Check 5.

Unset Printing All.

(** For all common operations on numbers, there is the usual notation
    defined in the standard library. *)
Locate "+".

Compute (4 + 5).

(** We can now start proving properties for natural numbers and their
    operations. *)

(** Adding a number to zero is equal to the number. (Zero is the
    neutral element of addition) *)
Lemma add_O_n :
  forall n : nat, O + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.


(** Hint: We can also search for specific term patters. This can be
    very effective when we are looking for theorems in the library
    that apply in a specific case. For example the following command
    will return all theorems that have the pattern [_ + _ = _]. 

 *)

Search (_ + _ = _). 

(** Let's prove that equality on natural numbers is transitive. *)

Lemma eq_transitive :
  forall x y z : nat,
    x = y -> y = z -> x = z.
Proof.
  intros x y z.

  intros Heq1 Heq2.

  (* The [rewrite] tactic allows us to replace a term with another, if
     we have a proof that they are equal.  For example, [rewrite Heq1]
     will replace the left-hand side of the equality [Heq1] with the
     right-hand side in the goal. *)
  rewrite Heq1.

  (* We can also replace the right-hand side of an equality with the
     left-hand side. We can use the annotation [<-] to denote the
     direction of the rewrite.

     For example, [rewrite <- Heq1] will replace the right-hand side
     of the equality [Heq1] with the left-hand side in the goal.

     Note: In this case, this will undo the previous rewrite, but it
     is only for demonstration purposes. *)
  rewrite <- Heq1.

  (* Rewrites can be applied not only to the goal, but also to
     specific hypotheses in the context using the keyword [in].

     For example, [rewrite <- Heq1 in Heq2] will replace the
     right-hand side of the equality [Heq1] with the left-hand side in
     the hypothesis [Heq2]. *)
  rewrite <- Heq1 in Heq2.

  (* the [assumption] tactic allows us to derive a goal that is
     already present as a hypothesis in the context. *)
  assumption.
Qed.

(** Let's prove that adding two pairs of equal numbers results in two
    equal numbers. *)

Lemma add_eq_example:
  (* Coq has type inference, so it can figure out the types of
     variables [n1], [n2], [n3] and [n4], from the context they are
     used without us providing annotations. *)
  forall n1 n2 n3 n4,
    n1 = n2 ->
    n3 = n4 ->
    n1 + n3 = n2 + n4.
Proof.
  intros n1 n2 n3 n4 Heq1 Heq2.
  rewrite Heq1, Heq2.
  reflexivity.
Qed.

(** **** Notions of Equality *)

(** It is important to note that the operator [=] will _not_ test
    natural numbers for equality. A statement of the form [x = y]
    simply states a _logical claim_. We can reason about its validity
    by doing a proof, like above, but we cannot compute its result.

    But it is normal to expect that there is a boolean equality
    operator. This is part of the library and it is called [eqb].

    As a simple exercise you can try defining [eqb] from scratch.  *)

Check eqb.

(** [n =? m] is a convenient notation for [eqb n m]. We can use Coq's
    locate command to print information about a notation. *)
Locate "=?".

(** As expected, we can use [=?] for computation *)

Check (3 =? 3). 
Compute (3 =? 3).

Check (3 = 3). 
Compute (3 = 3).

Compute (4 =? 2).

(** Let's prove that the successor of a number cannot be equal to
    zero. *)
Lemma succ_not_zero: forall n, 1 + n =? 0 = false.
Proof.
  (* Note: writing [1 + n] is the same (up to simplification) with writing [S n] *)
  intros n. simpl. reflexivity.
Qed.


(** One can expect that boolean equality is sound and complete with
    respect to logical equality. *)

Search  (_ =? _ = true <-> _ = _).

Check PeanoNat.Nat.eqb_eq.

(** **** Injectivity and Distinctness of Constructors. *)

(** The constructors of natural numbers have some important properties:

    - If [S n = S m] then it must be [n = m]. (_injectivity_)

    - It cannot be that [S m = O]. (_distinctness_)

    These principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal. Coq provides tactics that let us
    reason about these two facts.
*)

Lemma S_injective :
  forall n m,
    S n = S m ->
    n = m.
Proof.
  intros n m Heq.

  (* The [injection] tactic can be applied to a hypothesis of the form
     [C n_1 ... n_k = C m_1 ... n_k] and will reduce it to an
     hypothesis of the form [n_1 = m_1 /\ ... /\ n_k = m_k].
     It can take a name to explicitly name the new hypotheses. *)

  injection Heq as Heq'.
  assumption.
Qed.

(** It is worth noting that injectivity is not a primitive property
    that is encoded in the logic. It is a property that can be proved
    using the properties of equality.

    We could prove the above lemma primitively, without using
    injectivity, as shown below. The [injectivity] tactic does this
    for us so that we don't have prove a separate lemma for each
    constructor. *)

Lemma S_injective_prim :
  forall n m,
    S n = S m ->
    n = m.
Proof.
  intros n m Heq.

  (* applying a function to equal inputs yields the same output. *)
  assert (Heq' : pred (S n) = pred (S m)).
  { rewrite Heq. reflexivity. }
  
  simpl in Heq'. assumption.
Qed.



(** Constructors of inductive types are distinct, meaning that values
    constructed from different constructor must be different. This
    means that [S n = O] is an absurd statement. In logic, we can
    prove anything from a false assumption. This is referred to as the
    principle of explosion or, in Latin, "Ex falso quodlibet".

    We can exploit distinctness of constructors using the
    [discriminate] tactic, as reflected in the following lemmas. *)

Lemma O_eq_S_absurd :
  forall x,
    O = S x ->
    3 = 4.
Proof.
  intros x H.
  (* [discriminate] can be applied to a hypothesis of the form [C1 x_1 ... x_n = C2 y_1 ... y_m],
     where [C1] =/= [C2]. It will prove any goal. *)
  discriminate H.
Qed.

(** We can apply this principle to booleans as well (or any other inductive type). *)
Lemma true_eq_false_absurd :
  true = false -> 3 = 4.
Proof.
  intros H.
  discriminate H.
Qed.


(** **** Destructing Inductive Types *)

(** Let's now try to prove something similar *)
Lemma add1_not_zero:
  forall n, n + 1 = 0 -> False.
Proof.
  (* Note: writing [n + 1] _does not_ simplify to [S n]. Can you see why? *)
  intros n Heq. simpl in Heq.

  Fail discriminate Heq.

  (* We proceed by considering cases for [n] *)

  (* Using destruct, will generate subgoals for each possible
     constructor of a variable that belongs to an inductive type. Here
     it generates cases for when [n] is [O] and for when [n] is the
     successor of a number.  *)
  destruct n as [ | n'] eqn:Heq'.

  - (* case [n = 0] *)
    simpl in *. discriminate Heq.
    
  - (* case [n = S n'] *)
    simpl in *. discriminate Heq.
Qed.


(** When we used destruct we used two extra annotations [[ | n' ]] and
    [eqn:Heq].

    The annotation [as [ l1 | l2 | ... | l_n ]] is called an
    _introduction pattern_. Each [l_i] is a (possibly empty) list of
    variable names and it corresponds to each case of the destruct.
    Each variable list [l_i] specifies the names of the constructor
    arguments that correspond to this case.

    If we don't specify any variable names, Coq will automatically
    pick some for us (that may not be the best choices). It is
    generally a good practice to give explicit names.

    In the previous proof, we used [[ | n' ]] that denotes that in the
    first subgoal we don't use any new variable names, since the [O]
    constructor doesn't take any arguments, and in the second subgoal
    we use n' for the argument of [S].

    The annotation [eqn:H] tells [destruct] to remember the equalities
    [n = 0] and [n = S n'] and put them in the context with the name
    [H]. In the first case, Coq will add [Heq : n = 0] to the proof
    context and in the second case it will add [Heq : n = S n'].  *)



(** In the previous proof we observe that [0 + 1] directly simplifies
    to [n].

    However the same does not happen for expressions like [n + 0]. Can
    you see why?

    Of course, it ought to be equal to it. Let's prove it once and for
    all, so we can use it in proofs.  (As you might expect, such
    statement is also part of the standard library.)  *)

Lemma add_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl. (* does nothing *)

  (* Let's try destruct again *)
  destruct n as [ | n' ].

  - (* case n = 0 *)
    reflexivity.

  - (* case n = S n' *)
    simpl.

    (* [assert] lets us prove individual statements within a proof,
       and then puts the statement in the proof context with the
       chosen name, here [Heq']. It can be very handy as it allows as
       to prove intermediate results during a proof. *)
    assert (Heq' : n' + 0 = n').
    { (* How do we prove this? *)
      admit.
      (* The tactic [admit] lets us "assume" some logical claim
         without proving it. It can be useful when constructing a
         complex proof with many different parts. However, in this
         case we cannot end the proof with [Qed]. We have to end it
         using the keyword [Admitted] that signifies that the
         statement is assumed rather than proved. We can also use the
         keyword [Abort] that aborts the current proof (without
         assuming the statement under proof. *)
    }

    rewrite Heq'. reflexivity.

Abort. (* The keyword [Abort] aborts the current proof. *)

(** But how can we prove that admitted statement? It seems that we
    need a more powerful reasoning principle to prove this fact.
    This principle is the _principle of induction_. *)

(** **** Proof by Induction *)

(** The induction principle over natural numbers says, informally,
    that:
    - if we can prove that a claim is valid for [0] and that
    - if the claim's validity for a number implies that the claim is
      valid for its successor

    then the claim ought to be valid for all natural numbers.

    Put more formally:

    Let [P] be a predicate on natural numbers and that we wish to prove
    [P(n)].

    If

     (1) [P(0)] holds (**base case***)

     (2) For any [n], if [P(n)] holds then so does [P(n+1)] (**inductive case**)

         Note: The premise [P(n)] is called the _inductive hypothesis_.

     Then, for all [n], [P(n)] holds.

     Therefore, to show a goal of the form [forall n, P n], it
     suffices to show (1) and (2)

     Let's see this in practice.
*)

Lemma add_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n. simpl.

  induction n as [ | n' IHn' ].

  - (* Base case: n = 0 *) simpl. reflexivity.

  - (* Inductive case: n = S n' *)
    simpl.

    (* Now, we have the induction hypothesis [IHn'] in the context.
       It says that the statement holds for n'. We must prove it for
       [S n']. *)
    rewrite IHn'. reflexivity.
Qed.

(** Next, let us prove that addition is commutative. *)
Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n' IHn' ].
  - (* case n = 0 *)
    simpl. rewrite add_n_O. reflexivity.
  - (* case n = S n' *)
    simpl.
    rewrite IHn'.
    (* we can rewrite with the previous lemma *)
    rewrite <- PeanoNat.Nat.add_succ_r.
    reflexivity.
Qed.

(** *** Pairs *)

Module Pairs.

  (** In Coq, and type theory in general, the type of a pair is called
      a "product". We can define a type for product that is parametric
      (i.e., polymorphic) on the type of the elements. This is written
      as: *)

  Inductive prod (A B : Type) : Type :=
  | pair : A -> B -> prod A B.

  Check prod.

  Check pair.

  (** In order to construct pairs we call the [pair] constructor. The
      type tells us that we first have to provide the types of the
      arguments and then the arguments.  *)

  Check (pair nat bool 42 true).


  (** Luckily, Rocq has type inference that lets us elide the type
      arguments. We could write an underscore [_], and Rocq would
      infer the type argument.  *)

  Check (pair _ _ 42 true).

  (** Prints:

      [pair nat bool 42 true : prod nat bool]

   *)


  (** We can also tell Rocq that the type arguments are implicit and can
      be elided.  *)

  Arguments pair {A} {B}.

  (** This allows us to write the less clunky: *)
  Check (pair 42 true).


  (** Now the type of pair has changed a bit: *)
  Check pair.

  (** We can still use the version with explicit type argument with
      the following notation: *)
  Check @pair.

  Check (@pair nat bool 42 true).

  (** We again define convenient notations *)

  Notation "( x , y )" := (pair x y).
  Notation "A * B" := (prod A B) : type_scope.

  (** We also define the usual projection functions *)

  Definition fst {A B : Type} (x : A * B) : A :=
    match x with
    | (a, _) => a (* Note that we can use wildcard for unused components of the pattern *)
    end.

  (* Formal parameters in curly braces indicate that these parameters
     are implicit. *)

  Compute (fst (4,2)).

  Definition snd {A B : Type} (x : A * B) : B :=
    match x with
    | (_, b) => b
    end.

End Pairs.

(** Let's prove that if the first and the second components of two
    pairs are equal, then the two pairs are equal

    Notice that in the following theorem, we don't have to insert type
    annotations in [A], [B] and [y]. Its type can be inferred by Rocq.

 *)

Lemma fst_snd_eq :
  forall A B (x : A * B) y,
    fst x = fst y ->
    snd x = snd y ->
    x = y.
Proof.
  intros A B x y Heq1 Heq2.

  (* To proceed let's destruct the pairs. *)

  destruct x as [a1 b1] eqn:Heqa.
  (* The intro pattern [a1 b1] is again optional. It lets us pick
     names for the two components of the pair. If we don't use it Rocq
     will pick names for us. *)

  destruct y as [a2 b2].

  simpl in *.

  (* If there are hypotheses of the form [x = expr] in the context,
     the [subst] tactic will replace [x] with [expr] in the proof
     state (goal and hypotheses) and will remove the equality from the
     context.

     We could as well use use [rewrite Heq1. rewrite Heq2.]  or the
     equivalent, but more concise [rewrite Heq1, Heq2.]  *)
  subst.

  reflexivity.

Qed.


(** *** Lists *)

Module Lists.

  (** Let us now define another very commonly used type: lists. The
      definition is similar to the one we know from ML. *)

  Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

  Check nil. Check cons.

  (** As with pairs, we declare implicit arguments and convenient
      notations. *)

  Arguments nil {A}.
  Arguments cons {A}.

  (** We define "levels" (of precedence) and associativity to avoid
      ambiguity *)
  
  Notation "x :: y" := (cons x y) (at level 60, right associativity).
  Notation "[ ]" := nil.

  (** This is some notation "magic" that lets us write arbitrarily long
      notations. *)
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

  Check ([]).
  Check ([1;2;3]).
  Compute (0::[1;2;3]).

  (** Do you see any difference with the definition of lists and
      pairs?

      Similar to nat, list is inductively defined. A larger list is
      built from a smaller list with the constructor [cons]. The base
      case is the constructor [nil].

      Therefore we can write recursive functions on list and reason
      about lists with induction. *)

  (** Let's define some standard functions on list: append ([app]),
      reverse ([rev]), and length *)

  Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
    match l1 with
    | [] => l2
    | x :: xs => x :: (app xs l2)
    end.

  Fixpoint rev {A:Type} (l:list A) : list A :=
    match l with
    | [] => []
    | h :: t => app (rev t) [h]
    end.
  (* Hint: [rev] is not very efficient *)

  Fixpoint length {A : Type} (l : list A) : nat :=
    match l with
    | [] => 0
    | _ :: l' => S (length l')
    end.


  (** Common notation for [app] *)
  Notation "x ++ y" := (app x y) (at level 60, right associativity).

  Example test_rev : rev [1;2] = [2;1].
  Proof. reflexivity. Qed.

  Example test_length: length [1;2;3;4] = 4.
  Proof. reflexivity. Qed.

  Example test_app: [1;2] ++ [3;4] = [1;2;3;4].
  Proof. reflexivity. Qed.

  (** Note: the keyword [Example] is similar to [Lemma]. The
      difference is just aesthetic. Similar keywords are [Theorem] and
      [Corollary]. *)

  (** We can also write higher-order functions: functions that take as
      arguments other functions. A common example is list map *)

  Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
    match l with
    | [] => []
    | x :: l' => f x :: map f l'
    end.

  Compute (map S [1;2;3]).

  (* And we can also introduce anonymous functions *)
  Compute (map (fun x => x * 2) [1;2;3]).

End Lists.

(** Let's switch to the lists from the standard library that are
    identical to our definitions above, and prove some lemmas *)

(** To prove the following lemmas we will use induction on lists. The
    principle of induction on lists asserts that:

    If, for a predicate on lists [P] we can show that

    (1) [P([])] (_base case_)

    (2) for all [x] and [l], if [P(l)] (inductive hypothesis) then [P(x::l)] (_inductive case_)

    Then, we can deduce [forall l, P(l)].

*)

Lemma length_app :
  forall A (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2. induction l1 as [ | x l1' IHl1 ]; simpl.

  (* Note: we can use [;] to sequence tactics.

     When we write [tactic1; tactic2], [tactic2] will be applied to
     all goals generated by [tactic1].

     This can be very useful tool to automate proofs and write smaller
     proof scripts. We will use it very often.

   *)

  - (* case l1 = [] *)
    reflexivity.

  - (* case l1 = x :: l1' *)
    rewrite IHl1. reflexivity.

Qed.


(** Let's figure out what it means to map two functions subsequently
    to a list ...

    Hint: let's first define function composition. This is a
    function-returning function.  *)

Definition comp {A B C} (g : B -> C) (f : A -> B) : A -> C :=
  fun (x : A) => g (f x).

Lemma map_compose :
  forall A B C (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (comp g f) l.
Proof.
  intros A B C f g l.

  induction l as [ | x l' IHl].

  - reflexivity.

  - simpl. rewrite IHl.

    reflexivity.
Qed.

(** Recall that our version of [rev] is not fast... (What is its
    complexity?).

    We wish to write a faster version of [rev] and prove that it
    coincides with rev.

    We will use a very common functional programming pattern: a tail
    recursive function with an accumulator. Instead of appending
    elements to the end of the list, we will accumulate them in a
    separate parameter that is fed back to the recursive call of the
    function. At the end of the recursion we will return the
    accumulator, that happens to be the list in reverse. *)

Fixpoint rev_fast_aux {A} (l : list A) (acc : list A) : list A :=
  match l with
  | [] => acc
  | x :: l' => rev_fast_aux l' (x :: acc)
  end.

(** A top-level function that calls the function with the accumulator
    with an empty list as the accumulator. *)
Definition rev_fast {A} (l : list A) : list A := rev_fast_aux l [].

Lemma rev_rev_fast :
  forall A (l : list A), rev l = rev_fast l.
Proof.
  intros A l. unfold rev_fast.
  induction l as [| x l' IHl']; unfold rev_fast; simpl.
  - reflexivity.
  - unfold rev_fast in *.
    (* [unfold def in *.] unfolds a definition [def] in the goal and
       all of the hypotheses in the context. *)
   (* ..... *)
   (* What do you think is wrong here? *)
Abort.

(** The inductive hypothesis is not general enough. We have to reason
    about any recursive call of [rev_fast], not just the top
    level. Therefore, we need to talk about what happens with any
    value of the accumulator, not just []. We must prove a more
    general lemma. *)

Lemma rev_rev_fast_aux_first_try :
  forall A (l : list A) (acc : list A),
    rev l ++ acc = rev_fast_aux l acc.
Proof.
  intros A l acc.  induction l as [| x l' IHl']; simpl.

  - (* case l = [] *)
    reflexivity.

  - (* case l = x :: l' *)
    simpl.
    Fail rewrite <- IHl'. (* Why? *)

    (* Ugh, this is still not very good. What is wrong here? What is
       the [P] of induction *)

    (* The inductive hypothesis is still not general enough. It talks
       about a specific [acc], whereas we need to talk about all
       possible values of [acc].*)
Abort.

(* Let's fix this. *)

Lemma rev_rev_fast_aux :
  forall A (l : list A) (acc : list A),
    rev l ++ acc = rev_fast_aux l acc.
Proof.
  intros A l.
  (* [revert] is the opposite of [intros]. *)
  (* We could also just do: [intros A l.] *)

  (* What is the [P] of induction now? *)

  induction l as [| x l' IHl']; simpl.

  - (* case l = [] *)
    intros acc. reflexivity.

  - (* case l = x :: l' *)
    intros acc.
    rewrite <- IHl'.

    (* That's way better! We know that this should be true, but we
       need a way to prove this. *)

    (* [app] is an associative operator, meaning that [(rev l' ++
       [x]) ++ acc = rev l' ++ ([x] ++ acc)] *)

    (* But we need a lemma to prove this in order to use it. Luckily
       we can search in the Rocq data base that contains all known
       definitions and theorems to see if we can find something. *)

    (* We can search a definition and find all the relevant
       lemmas: *)
    Search app.

    (* We can also search for specific patterns: *)
    Search ((_ ++ _) ++ _).

    rewrite <- app_assoc. simpl. reflexivity.
Qed.

(** Finally, we can use the above [Lemma] to prove a top-level
    theorem about [rev_fast]. *)

Theorem rev_rev_fast :
  forall A (l : list A), rev l = rev_fast l.
Proof.
  intros A l.
  unfold rev_fast.
  rewrite <- rev_rev_fast_aux.

  Search (_ ++ []).
  rewrite app_nil_r. reflexivity.
Qed.


(** Let's write a function that returns the nth element of a list.  *)

Fail Fixpoint nth {A:Type} (n : nat) (l : list A) : A :=
  match l with
  | [] => _ (* What should happen here? *)
  | x :: l' => match n with
               | O => x
               | S n' => nth n' l'
               end
  end.

(* One option is to return a default element, of type [A], that we
   pass as argument *)

Fixpoint nth {A:Type} (n : nat) (l : list A) (def : A) : A :=
  match l with
  | [] => def
  | x :: l' =>
      match n with
      | O => x
      | S n' => nth n' l' def
      end
  end.

(** Another option, is to use an [option] type to encode that the
    function does not return a result in all cases. *)

(** *** Option *)

(** Another common datatype is [Option]. Among other things, [Option]
    is useful to encode partial functions. Recall that functions in Rocq
    have to be total. By using an option result type we can indicate
    the "absence" of result in certain cases, while still writing a
    total function. *)

Module Option.

  Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None.

  Arguments Some {A}.  Arguments None {A}.

End Option.


Fixpoint nth_option {A:Type} (n : nat) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: l' =>
      match n with
      | O => Some x
      | S n' => nth_option n' l'
      end
  end.
