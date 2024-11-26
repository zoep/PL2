(** * Proofs as Programs *)


(** As we have noted before in the course, there is a straight-forward
    _syntactic_ correspondence between formal systems of logic and
    type systems.

    The simplest witness of this isomorphism is simply-typed lambda
    calculus (STLC) and propositional logic.

    In its most basic form, the STLC corresponds to the implicational
    fragment of propositional logic. By extending the calculus to
    include constructs such as pairs, sums, and the unit type, we can
    recover the full expressiveness of propositional logic.

    Below, we provide a concise overview of these two formal systems
    and the correspondence between them. *)

(** ** Propositional Logic *)

(** *** Formulas *)

(** We assume a countably infinite set of atomic propositions
    (propositional variables) [P], [Q], etc.

    A The set of formulas is generated by the following grammar.

<<
s    A, B := P
         | A => B   (implication)
         | A /\ B   (conjunction)
         | A \/ B   (discumntion)
         | T        (true)
         | F        (false)
>>

    Negation : [~ A ≡ A => F] (derived form)


    - A formula is *satisfiable* if there exists a satisfying assignment 
    - A formula is *valid* if it is true for a all possible assignment
    - A formula is *unsatisfiable* if there is no satisfying assignment 


    Examples of valid statements (tautologies) 
    
    - [T]
    - [A => A]
    - [A \/ B => A]
    - [(A => B) => A => B]
    ...


    Examples of unsatisfiable statements

    - [F]
    - [A /\ ~ A]
    ... 

*)

(** *** Natural Deduction *)


(** A (sound and complete) proof system for propositional logic, such that

    1. If a formula is provable it is logically valid (soundness)
    2. If a formula is logically valid then it is provable (completeness)

We can derive judgments of the form [Γ |- Α], where [Γ] is an
environment containing the _assumptions_. This statement reads as
"A is true under the assumptions in Γ, A is true".


The inference rules of the system are: 

<<

    --------- (Truth)
     Γ |- T



    ---------(Axiom)  if A \in Γ
     Γ |- A



       Γ |- A                            Γ |- B
    --------------- (Or-Intro-l)     --------------- (Or-Intro-r)
      Γ |- A \/ B                      Γ |- A \/ B


      Γ |-  A \/ B     Γ, A |-  C     Γ, B |- C
    -------------------------------------------- (Or-Elim)
                         Γ |-  C



      Γ |- A    Γ |- B
    -------------------- (And-Inro)
         Γ |- A /\ B


      Γ |- A /\ B                     Γ |-  A /\ B
    -------------- (And-Elim-l)     ---------------- (And-Elim-r)
       Γ |- A                           Γ |- B



      Γ, A |- B
    -------------- (Impl-Inro)
     Γ |- A => B



      Γ |- A => B     Γ |- A
    --------------------------(Impl-Elim)
              Γ |- B


    --------- (True-Intro)
     Γ |- T


      Γ |- F
    -------------- (False-Elim)
      Γ |- A



>> *)

(** ** Simply Typed Lambda Calculus *) 


(** Lambda calculus is a universal models of computation, formulated
    by Alonzo Church in the 1930s. It is computational power is
    equivalent to this of Turing machines and recursive functions.

   That is, "A function is λ-computable if and only if it is Turing
   computable, and if and only if it is general recursive" (Church,
   Turing, Kleene). Or, schematically:

<<
   Lambda Calculus (Church) <-> Turing machine (Turing) <-> Recursive functions (Gödel)
>>
*)


(** *** Syntax *)

(** *** Types *)

(*  We assume a countably infinite set of variables base types A, B, C, etc.

Types are generated by the following grammar.

<<
   A, B, C :=  A -> B  (function type)
           |   A x B   (product)
           |   A + B   (sum)
           |   1       (unit)
           |   0       (empty)
>>
*)

(** **** Terms *)

(**  We assume a countably infinite set of variables  x, y, z, etc.

Terms are generated by the following grammar.

<<
    t := x                                          (variable)
       | λ (x : A). t | t1 t2                       (functions)
       | (t1, t2) | fst t | snd t                   (pairs)
       | inl t | inr t                              (sums)
       | case t of Inl x => t1 | Inr y => t2        (case analysis)
       | ()                                         (Unit)
       | case0 t                                    (empty type elimination) 
>> *)


(** *** Typing Rules *)

(** A typing judgment has the form [Γ |- t : A] and denotes that in
    the environment [Γ] the term [t] has type [A].

    An environment is mapping from variable names to types, and
    assigns types to the free variables of a term.

    The inference rules are given below. *)

(** 
<<

    -------------- (Unit)
     Γ |- () : 1


       Γ(x) = A
    -------------- (Var)  
     Γ |- x : A



           Γ |- t : A                              Γ |- t : B
    ---------------------- (Sum-Intro-l)     ----------------------- (Sum-Intro-r)
      Γ |- Left t : A + B                     Γ |- Right t : A + B


      Γ |-  t : A + B     Γ, x : A |-  t1 : C    Γ, x : B |- t2 : C
    ------------------------------------------------------------------ (Sum-Elim)
          Γ |-  (case t of Inl x => t1 | Inr x => t2) : C



      Γ |- t1 : A    Γ |- t2 : B
    ------------------------------ (Prod-Intro)
         Γ |- (t1, t2) : A x B


      Γ |- t : A x B                      Γ |-  t: A x B
    ------------------- (Prod-Elim-l)   ------------------ (Prod-Elim-r)
      Γ |- fst t : A                      Γ |- snd t : B



          Γ, x: A |- t : B
    ---------------------------- (Function-Inro)
      Γ |- λ(x : A). t : A -> B



      Γ |- t1 : A -> B     Γ |- t2 : A
    ------------------------------------(Function-Elim)
                Γ |- t1 t2 : B


    -------------- (Unit-Intro)
     Γ |- () : 1


         Γ |- t : 0 
    -------------------- (Empty-Elim)
      Γ |- case0 t : A


>>
*)

(** ** Curry-Howard Correspondence *)

(** The Curry-Howard Correspondence states that there is a
    correspondence between formulas of logic with types and proofs
    with programs. Schematically:

<<
formulas <--> types

proofs <--> programs
>>

   In particular, a formula Γ |- A is provable in propositional logic iff
   there exists a simply-typed lambda calculus program such that
   Γ |- t : A.  

   Note: the above statment is somewhat "handwavy" as the type A is
   not syntactically equal to a proposition A (but rather
   isomorphic). In addition [Γ] in natural deduction does not include
   variable names. However, there is a systematic way to convert
   between the two representations.

*)
(** 

Some examples of propositions with their corresponding _proof term_. 
<<
   Proposition                            |    Program 
----------------------------------------------------------------------------------------------------------------------------------
                                          |
   A  -> A                                |    λ (x : A).  x
                                          |
                                          | 
   A /\ B ->  A                           |    λ (x : A x B). fst x
                                          | 
                                          |
   A \/ B -> (A -> C) -> (B -> C) -> C    |    λ (x : A + B) (f : A -> C) (g : B -> C). case x of Inl y => f y | Inr y => g y
                                          |
                                          |
>>
**)


(** *** Proof Terms *)

(** Some examples of proof terms in Coq. *)

Context (A B C : Prop).

Lemma tauto : A -> A.
Proof. intros H. apply H. Qed.

Print tauto.

Definition tauto' : A -> A := fun x => x. 


Lemma proj1 : A /\ B -> A.
Proof. intros H1. destruct H1 as [H3 H4]. apply H3. Qed.

Print proj1. 
 
Definition proj1' : A /\ B -> A := fun x => proj1 x.

Lemma sum_app : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof. 
  intros Hor Hf Hg. destruct Hor.
  - apply Hf. apply H.
  - apply Hg. assumption.
Qed. 

Print sum_app.

Definition sum_app' : A \/ B -> (A -> C) -> (B -> C) -> C :=
  fun x f g =>
    match x with
    | or_introl y1 => f y1
    | or_intror y2 => g y2
    end.

Lemma modus_ponens : (A -> B) -> A -> B.
Proof.
  intros H1 H2. apply H1. assumption.
Defined.

Print modus_ponens.

Definition modus_ponens' : (A -> B) -> A -> B :=
  (fun x => x) (fun (H1 : A -> B) (H2 : A) => H1 H2). 

Lemma modus_ponens_eq : modus_ponens = modus_ponens'.
Proof. reflexivity. Qed.


Lemma or_commut :
  A \/ B <-> B \/ A.
Proof.
  exact
    (conj
       (fun H : A \/ B =>
          match H with
          | or_introl x => or_intror x
          | or_intror x => or_introl x
          end)
       (fun H : B \/ A =>
          match H with
          | or_introl x => or_intror x
          | or_intror x => or_introl x
          end)). 

  (* Proof with tactics: *)
  (* split. *)
  (* - intro H. destruct H. *)
  (*   + right. assumption. *)
  (*   + left. assumption. *)
  (* - intros H. destruct H. *)
  (*   + right. assumption. *)
  (*   + left. assumption. *)
Qed.
  

Print or_commut. 


Lemma transitivity : (A -> B) -> (B -> C) -> A -> C.
Proof.
  exact (fun f g => (fun x => g (f x))). 
Qed. 

Lemma and_app : (A -> B) -> (A -> C) -> A -> B /\ C.
Proof.
  exact (fun f g a => conj (f a) (g a)). 

  (* Proof with tactics: *)
  (* intros H1 H2 H3. *)
  (* split. *)

  (* - (* proof of B *) *)
  (*   apply H1. eassumption. *)

  (* - (* proof of C *) *)
  (*   apply H2. eassumption. *)

Qed.


Print and_app. 

 
(** ** System F: Type Polymorphism *)

(** System F (Girard 1972) introduces quantification over types. In
    logic, this corresponds to quantification over
    propositions. Therefore, System F corresponds to second-order
    propositional logic, which is a propositional logic extended with
    quantification over propositions. *)


(** *** Syntax *)

   (** The syntax of lambda calculus is extended as follows. *)

   (** Types *)
(*
<<
   A  := ...
       | forall α, X    (quantification over types)
       | α              (type variables)
  
>>
*)

(** ** Terms *)

(*
<<
    t := ...
       | Λ α. t        (type abstraction -- term parametized by a type) 
       | t A           (type application -- instantiation of an abstract type)
>>
*)

(** *** Typing rules *)

(** We introduce two new typing rules. *)

(*
<<         
          Γ, α |- t : B
    ------------------------------- (Λ-intro) 
        Γ |- Λ α. t : forall α. B


        Γ |- t : forall α. B
    --------------------------------- (Λ-elim)
        Γ |- t Α : B [Α / α]
>>
*)

(** *** Examples *)

Definition conj_intro : forall (A B : Prop), A -> B -> A /\ B :=
  fun (A B : Prop) (x : A) (y : B) => conj x y.

Definition contra : forall (A B : Prop), (A -> B) -> (~ B -> ~ A) :=
  fun (A B : Prop) (f : A -> B) (g : ~ B) (x : A) =>  g (f x). 


(** System F, introduces terms _that depend on types_. We have already
    seen terms whose value depend on other terms: the usual lambda
    abstractions of lambda calculus.

    As we will see we can also have types that depend on types and
    types that depend on terms (the so-called _dependent_ types). All
    of these features together, gives us the full expressively of
    higher-order logic. *)

(** ** Types that depend on types: Type operators *)

(** In STLC, [->] is a type constructor: a "function" that takes as
    inputs two types a returns another type.

    System λω, extends this STLC by introducing _type operators_,
    which are type-level functions. These allow abstraction and
    application to occur at the level of types. For example:

    - [λΑ. Α -> Α]: type-level function that maps a type A to the type
      of functions from A to A.


    - [λΑ.λB. (Α -> B) -> B]: A type operator that takes two types A
      and B and produces the type [(A -> B) -> B].

    By convention, we use the same notation for type-level and
    term-level abstractions and applications.

    In this system, the same type can be write in more than one ways,
    for example [Bool -> Bool] and [(λΑ. Α -> Α) Bool]. The system
    ensures that if [Γ |- t : T] and [T] is equivalent to [T'], then
    [Γ |- t : T']. *)

(** *** Kinds *)

(** To ensure well-typedness of types, System λω introduces the
    concept of kinds: types for types and type operators.

    - [*]: is the kind of "proper" types
    - [* -> *]: is the kind of type operators
    - [* -> * -> *]: two-argument type operator (curried)
    - [(* -> *) -> *]: the kind of functions from type operators to proper types 

     Examples of Kinds:

     - Bool : *

     - [λA. A -> A] : * -> *

     - [λA.λB. (A -> B) -> B] : * -> * -> *

     - [λT.λB. T B] : (* -> *) -> *   (Higher-order kind)
*)

(** Such system on its own is rather strange as seen as a logic, but
    when combined with System F, it corresponds to higher-order
    predicate logic. *)

(** *** Further Reading  *)

(** A more detailed formalism of the system can be found in Types and
    Programming languages, Chapter 29.

    The following course notes also provide a nice summary.
    https://www.cs.cornell.edu/courses/cs4110/2021fa/lectures/lecture31.pdf
*)

(** *** Examples *)

Definition ty_op1 (A B : Type) := A -> B.

Check ty_op1.

Definition ty_op2 (A B : Type) := (A -> B) -> list A -> list B.

Require Import List.

Definition map' : ty_op2 nat bool := @map nat bool.

(** ** Types that depend on terms: Dependent types *)

(** Another extension is to allow types to depend on terms. This
    extension allows for very expressive types that can express
    program specifications. 

    Type-checking dependently typed programs needs 
    
  *)

(** ** Putting Everything Together: Calculus of Constructions *)

(** Calculus of Construction, the underlying system of Coq, combines
    all of this extensions together. Logically this corresponds to
    higher-order predicate logic. *) 



(** ** More Examples *)

Inductive vector (T : Type) : nat -> Type :=
| Vnil : vector T 0
| Vcons : forall n, T -> vector T n -> vector T (S n).

Arguments Vnil {_}.
Arguments Vcons {_}.

Definition head {T} {n : nat} (v : vector T (S n)) : T :=
  match v with
  | Vcons _ x _ => x
  end.

Definition tail {T} {n : nat} (v : vector T n) : vector T (pred n) :=
  match v with
  | Vnil => Vnil
  | Vcons _ _ l => l
  end.

Definition append {T} {n m : nat} (v1 : vector T n) (v2 : vector T m) : vector T (n + m).
Proof.
  induction v1.
  - exact v2.
  - rewrite plus_Sn_m.
    constructor. exact t. exact IHv1.
Qed.


Lemma induction_principle :
  forall (P : nat -> Prop), P 0 -> (forall n, P n -> P (1 + n)) -> (forall n, P n). 
Proof.
  intros P Hbase IH.

  exact (fix f (n : nat) : P n :=
            match n with
            | 0 => Hbase
            | S n' => IH n' (f n')
            end). 
                     
Qed.
