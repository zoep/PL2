Require Import Coq.Strings.String Coq.Init.Nat Lia.

(** * Simply Typed Lambda Calculus **)

(** In this section, we formalize type safety for the Simply Typed
    Lambda Calculus (STLC), adding a few simple extensions to the
    language.

    The extensions we consider are:

    - Type of booleans 
    - Type of natural numbers
    - Sum type
    - Product type


    Each type comes with its own operations. We first give an informal
    account of the added contructs and we describe its static and
    dynamic semantics. *)

(** ** Booleans *)

(** - Type: [Bool]

- Description: The usual boolean datatype, representing truth values.

- Constructors: [true] and [false]

- Values: [true] and [false]

- Elimination form: Conditional expressions of the form [if b then e1 else e2] 

- Static semantics:


<<

      --------------------(Ty_true)
         Γ ⊢ true : Bool


      --------------------(Ty_false)
        Γ ⊢ false : Bool


       Γ ⊢ b : Bool   Γ ⊢ a1 : A   Γ ⊢ a2 : A  
      -----------------------------------------(Ty_if)
           Γ  ⊢ if b then e1 else e2 : A

>>


- Dynamic semantics:

<<
      ----------------------------------(step_if_true)
        if true then e1 else e2 --> e1


      ----------------------------------(step_if_false)
        if false then e1 else e2 --> e2


                            e --> e'
      ----------------------------------------------------(step_if)
        if e then e1 else e2 -->  if e' then e1 else e2
>>
*)




(** ** Natural Numbers *)

(** - Type: [Nat]

- Description: Non-negative integers.

- Constructors: 0,1,2,3, etc.

- Values: 0,1,2,3, etc.

- Elimination form: We don't add explicit elimination forms, like a
  case analysis construct for natural numbers. This behavior can be
  simulated with the binary operators and the if-the-else construct.

- Static semantics:
<<
      --------------------(Ty_nat)
            Γ ⊢ n : Nat
>>

- Dynamic semantics: See binary operators below.

*)

(** *** Binary and Unary Operators on Booleans and Naturals *)

(** To make the language easier to use we add a number of primitive
    binary and unary operators as primitives. These are:

    - Addition (+), subtraction (-), multiplication ( * )

    - Disjunction (||), conjunction (&&)

    - Less-than (<), equal (=)

    - Negation (~)  


- Static semantics:

<<
             Γ ⊢ e1 : Nat      Γ ⊢ e2 : Nat
      -----------------------------------------(Ty_Bop_nat)   if ⊕ ∈ {+, -, *} 
                  Γ ⊢ e1 ⊕ e2 : Nat


             Γ ⊢ e1 : Bool     Γ ⊢ e2 : Bool
      -----------------------------------------(Ty_Bop_bool)  if ⊕ ∈ {&&, ||} 
                  Γ ⊢ e1 ⊕ e2 : Bool


             Γ ⊢ e1 : Nat      Γ ⊢ e2 : Nat
      -----------------------------------------(Ty_Bop_cmp)   if ⊕ ∈ {<, =} 
                  Γ ⊢ e1 ⊕ e2 : Bool


                   Γ ⊢ e : Bool
      -----------------------------------------(Ty_Uop) 
                  Γ ⊢ ~ e : Bool
>>

- Dynamic semantics:

  Let ⊕ be a boolean operator, we denote its interpretation as [⊕]. 

<<
      ---------------------------(step_bop_nat)    if ⊕ ∈ {+, -, *}
        n1 ⊕ n2  --> n1 [⊕] n2


      ---------------------------(step_bop_bool)   if ⊕ ∈ {&&, ||}
        b1 ⊕ b2  --> b1 [⊕] b2


      ---------------------------(step_bop_cmp)    if ⊕ ∈ {<, =}
        n1 ⊕ n2  --> n1 [⊕] n2


              e1 --> e1'
      ---------------------------(step_bop_l) 
        e1 ⊕ e2  --> e1' ⊕ e2


              value v1
              e1 --> e2'
      ---------------------------(step_bop_r) 
        v1 ⊕ e2'  --> v1 ⊕ e2'




      ---------------------------(step_uop_true)
        ~ true  -->  false


      ---------------------------(step_uop_bool)
        ~ false  -->  true



               e --> e'
      ---------------------------(step_uop)
            ~ e  --> ~ e'
>>

*)

(** ** Unit type *)

(** - Type: [Unit]

- Description: A type with one value and no operations on it.

- Constructors: [unit]

- Values: [unit]

- Elimination form: None. 

- Static semantics:


<<

      --------------------(Ty_unit)
         Γ ⊢ unit : Unit

>>


- Dynamic semantics: No added rules.
*)

(** ** Product Type *)

(** - Type: [A * B] where [A] and [B] are types.

- Description: A pair of values of types [A] and [B].

- Constructors: [(a, b)] where [a] and [b] are terms of the respective type.

- Values: [(a, b)] when [a] and [b] are values.

- Elimination form: First projection [e.1] and second projection [e.2]

- Static semantics:


<<

               Γ ⊢ e1 : A      Γ ⊢ e2 : B
      -----------------------------------------(Ty_Pair) 
                Γ ⊢ (e1, e2) : A * B


                  Γ ⊢ e : A * B
      -----------------------------------------(Ty_Fst) 
                   Γ ⊢ e.1 : A


                  Γ ⊢ e : A * B
      -----------------------------------------(Ty_Sbd) 
                   Γ ⊢ e.2 : B

>>

- Dynamic semantics:
<<


          value v1    value v2
      ---------------------------(step_fst_v)
           (v1, v2).1 --> v1


          value v1    value v2
      ---------------------------(step_snd_v)
           (v1, v2).2 --> v2



                t --> t'
      ---------------------------(step_fst)
              t.1 --> t'.1

                t --> t'
      ---------------------------(step_fst)
              t.2 --> t'.2


              e1 --> e1'
      ---------------------------(step_pair_l)
        (e1, e2) --> (e1', e2)


              value v1
              e1 --> e2'
      ---------------------------(step_pair_l)
        (v1, e2) --> (v1, e2')
>>
*)


(** ** Sum Type *)

(** - Type: [A + B] where [A] and [B] are types.

- Description: A value of a sum type is either a value of type [A],
  wrapped in the constructor [inl], or value of type [B], wrapped in
  the constructor [inlr]. A generalization of the sum type is tagged
  union types (or variants).

- Constructors: [inl a] or [inr b], where [a] and [b] are terms of the
  respective type. 

- Values: [inl a] or [inr b], when [a] and [b] are values.

- Elimination form: Case analysis of the form [case e of | inl y1 => e1 | inr y2 => e2].
  At each arm of the case the binders [y1] and [y2] bind the inner
  value of the sum constructors [inl] and [inr].

- Static semantics:


<<

                 Γ ⊢ e1 : A
      -----------------------------------------(Ty_Inl)
              Γ ⊢ inl e1 : A + B


                 Γ ⊢ e2 : B
      -----------------------------------------(Ty_Inr)
              Γ ⊢ inl e2 : A + B


                      Γ ⊢ e : A + B
          Γ, y1 : A ⊢ e1 : C      Γ, y2 : B ⊢ e2 : C
      ------------------------------------------------------(Ty_Fst)
        Γ ⊢ case e of | inl y1 => e1 | inr y2 => e2 : C
>>

- Dynamic semantics:
<<


                                  value v
      --------------------------------------------------------------------(step_case_inl)
        case inl v of | inl y1 => e1 | inr y2 => e2  --> [y1 := v]e1


                                  value v
      --------------------------------------------------------------------(step_case_inr)
        case inr v of | inl y1 => e1 | inr y2 => e2  --> [y2 := v]e1


                                  t --> t'
      ----------------------------------------------------------------------------------------(step_case)
        case t of | inl y1 => e1 | inr y2 => e2 --> case t' of | inl y1 => e1 | inr y2 => e2



              e1 --> e1'
      ---------------------------(step_inl)
          inl e1 --> inl e1'


              e2 --> e2'
      ---------------------------(step_inr)
          inl e2 --> inl e2'
>>
*)

(** ** Let binding *)

(** We also add let bindings as a primitive of the language and not as
    a derived form (syntactic sugar).

- Static semantics:

<<
        Γ ⊢ e1 : A    Γ, x : A  ⊢ e2 : B
      ------------------------------------(Ty_let)
              Γ ⊢ let x = e1 in e2 : B
>>


- Dynamic semantics:.
<<
                        value v1 
      --------------------------------------------(step_let_value)
            let x := v1 in e2 --> e2[x := v1]


                       e1 --> e1'
      --------------------------------------------(step_let)
        let x := e1 in e2 --> let x := e1' in e2

>>
*)


(** ** Syntax **)

(** We start the formalization by defining the abstract syntax of the extended STLC. *)

(** The abstract syntax of types. *)
Inductive type : Type :=
| Arrow : type -> type -> type
| Nat   : type
| Bool  : type
| Unit  : type
| Sum   : type -> type -> type
| Prod  : type -> type -> type.

(** Binary Operators. *)

(** To make definitions less verbose we group all binary operators
    under the same type [bop]. This allows us to handle them
    uniformly when possible. *)
Inductive bop :=
(* arithmetic operators *)
| Plus | Minus | Mult
(* boolean operators *)
| And | Or
(* comparison operators *)
| Lt | Eq.

(** Unary Operators. *)
Inductive uop :=
| Neg.

(** The abstract syntax of terms. *)
Inductive term : Type :=
(* Pure STLC fragment with functions, applications, and variables. *)
| T_App : term -> term -> term
| T_Lambda : string -> type -> term -> term
| T_Var : string -> term
(* Let *)
| T_Let : string -> term -> term -> term                      
(* Booleans *)
| T_Bool : bool -> term
(* If *)
| T_If : term -> term -> term -> term
(* Natural Numbers *)
| T_Nat : nat -> term
(* Binary Operators *)
| T_BOp : bop -> term -> term -> term
(* Unary Operatos *)
| T_UOp : uop -> term -> term
(* Pairs *)
| T_Pair : term -> term -> term
| T_Fst : term -> term
| T_Snd : term -> term
(* Sums *)
| T_Inl : type -> term -> term
| T_Inr : type -> term -> term
| T_Case : term -> string -> term -> string -> term -> term
.

(** As usual, we define familiar syntax for terms of the object
    language. Terms of the object language are written inside
    quotations [ <[ t ]> ]. Standalone types of the object language
    are written inside quotations [ <[[ t ]]> ]. In order to be able
    to write Coq terms inside object language quotations, introduce
    anti-quotations using curly braces [ { t } ]. Inside
    anti-quotations, we can escape the syntax of the object language
    and directly use the standard Coq syntax to write terms. *)

Declare Scope ML_scope.

Declare Custom Entry ML.
Declare Custom Entry ML_ty.

Notation "<[ e ]>" := e (e custom ML at level 99) : ML_scope.
Notation "( x )" := x (in custom ML, x at level 99).
Notation "x" := x (in custom ML at level 0, x constr at level 0).


Notation "<[[ e ]]>" := e (e custom ML_ty at level 99) : ML_scope.
Notation "( x )" := x (in custom ML_ty, x at level 99).
Notation "x" := x (in custom ML_ty at level 0, x constr at level 0).

(** Types *)

Notation "S + T" := (Sum S T) (in custom ML_ty at level 3, left associativity).
Notation "X * Y" :=
  (Prod X Y) (in custom ML_ty at level 2, X custom ML_ty, Y custom ML_ty at level 0).
Notation "S -> T" := (Arrow S T) (in custom ML_ty at level 50, right associativity).

(** Terms *)

Notation "x y" := (T_App x y) (in custom ML at level 1, left associativity).

Notation "'fun'  x ':' T  '->' y" := (T_Lambda x T y) (in custom ML at level 90,
                                           x at level 99,
                                           T custom ML at level 99,
                                           y custom ML at level 99,
                                           left associativity) : ML_scope.

Notation "'let' x ':=' y 'in' z" := (T_Let x y z) (in custom ML at level 90,
                                          x at level 99,
                                          y custom ML at level 100,
                                          z custom ML at level 100, left associativity) : ML_scope.

Notation "'if' x 'then' y 'else' z" :=
  (T_If x y z)
    (in custom ML at level 89, x at level 99,
        y at level 99, z at level 99) : ML_scope.

Notation "x <= y" := (T_BOp Or (T_BOp Lt x y) (T_BOp Eq x y))
                       (in custom ML at level 70, no associativity) : ML_scope.
Notation "x < y" := (T_BOp Lt x y)
                      (in custom ML at level 70, no associativity) : ML_scope.
Notation "x = y" := (T_BOp Eq x y)
                      (in custom ML at level 70, no associativity) : ML_scope.

Notation "x <> y" := (T_UOp Neg (T_BOp Eq x y))
                       (in custom ML at level 70, no associativity) : ML_scope.

Notation "x && y" := (T_BOp And x y) (in custom ML at level 80, left associativity) : ML_scope.
Notation "x || y" := (T_BOp Or x y) (in custom ML at level 80, left associativity) : ML_scope.

Notation "'~' b" := (T_UOp Neg b) (in custom ML at level 75, right associativity) : ML_scope.

Notation "x + y" := (T_BOp Plus x y) (in custom ML at level 50, left associativity) : ML_scope.
Notation "x - y" := (T_BOp Minus x y) (in custom ML at level 50, left associativity) : ML_scope.
Notation "x * y" := (T_BOp Mult x y) (in custom ML at level 40, left associativity) : ML_scope.

Notation "'inl' T t" := (T_Inl T t) (in custom ML at level 0,
                              T custom ML_ty at level 0,
                              t custom ML at level 0).
Notation "'inr' T t" := (T_Inr T t) (in custom ML at level 0,
                              T custom ML_ty at level 0,
                              t custom ML at level 0).
Notation "'case' t 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (T_Case t x1 t1 x2 t2) (in custom ML at level 89,
        t custom ML at level 99,
        x1 custom ML at level 99,
        t1 custom ML at level 99,
        x2 custom ML at level 99,
        t2 custom ML at level 99,
        left associativity).


Notation "( x ',' y )" := (T_Pair x y) (in custom ML at level 0,
                                x custom ML at level 99,
                                y custom ML at level 99).
Notation "t '.1'" := (T_Fst t) (in custom ML at level 1).
Notation "t '.2'" := (T_Snd t) (in custom ML at level 1).

(* antiquotation *)

Notation "{ x }" := x (in custom ML at level 1, x constr).

Coercion T_Var : string >-> term.
Coercion T_Nat : nat >-> term.
Coercion T_Bool : bool >-> term.

Open Scope ML_scope.

(** We define some commonly used variables. *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

(** ** Operational Semantics *)

(** *** Values *)

Inductive value : term -> Prop :=
(* Functions *)
| V_Fun :
  forall x T t,
    value <[ fun x : T -> t ]>
(* Natural Numbers *)
| V_Nat :
  forall (n : nat),
    value <[ n ]>
(* Booleans *)
| V_Bool :
  forall (b : bool),
    value <[ b ]>
(* Sums *)
| V_Inl : forall v T1,
    value v ->
    value <[ inl T1 v ]>
| V_Inr : forall v T1,
    value v ->
    value <[ inr T1 v ]>
(* Pairs *)
| V_Pair : forall v1 v2,
    value v1 ->
    value v2 ->
    value <[ (v1, v2) ]>.


(** *** Substitution. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom ML at level 20, x constr).

Fixpoint subst (x : string) (t' : term) (t : term) : term :=
  match t with
  (* pure stlc *)
  | T_Var y =>
      if String.eqb x y then t' else t
  | <[ fun y : T -> t1 ]> =>
      if String.eqb x y then t else <[ fun y : T -> [x:=t']t1 ]>
  | <[ t1 t2 ]> =>
      <[ ([x:=t'] t1) ([x:=t'] t2) ]>
  (* nats and bools *)
  | T_Nat _ => t
  | T_Bool _ => t
  | T_BOp bop t1 t2 => T_BOp bop <[ [x:=t'] t1 ]>  <[ [x:=t'] t2 ]>
  | T_UOp uop t1 => T_UOp uop <[ [x:=t'] t1 ]> 
  | <[ if t1 then t2 else t3 ]> =>
      <[ if [x := t'] t1 then [x := t'] t2 else [x := t'] t3 ]>
  (* pairs *)
  | <[ (t1, t2) ]> => <[ ([x:=t'] t1, [x:=t'] t2) ]>
  | <[ t.1 ]> => <[ ([x:=t'] t).1 ]>
  | <[ t.2 ]> => <[ ([x:=t'] t).2 ]>
  (* sums *)
  | <[ inl T2 t1 ]> =>
      <[ inl T2 ([x:=t'] t1) ]>
  | <[ inr T1 t2 ]> =>
      <[ inr T1 ( [x:=t'] t2) ]>
  | <[ case t of | inl y1 => t1 | inr y2 => t2 ]> =>
      let t1' := if String.eqb x y1 then t1 else <[ [x:=t'] t1 ]> in
      let t2' := if String.eqb x y2 then t2 else <[ [x:=t'] t2 ]> in
      <[ case ([x:=t'] t) of
         | inl y1 => t1'
         | inr y2 => t2' ]>        
  | <[ let y := t1 in t2 ]> =>
      let t2' := if String.eqb x y then t2 else <[ [x:=t'] t2 ]> in
      <[ let y := [x:=t'] t1 in t2' ]>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom ML).

Reserved Notation "t '-->' t'" (at level 40).

(** Helper functions to distinguish between operators of different
    types and define their interpretation. *)

Definition is_nat_op (op : bop) : bool :=
  match op with
  | Plus | Minus | Mult => true
  | _ => false
  end.

Definition nat_op (op : bop) : option (nat -> nat -> nat) :=
  match op with
  | Plus => Some add
  | Minus => Some sub
  | Mult => Some mul
  | _ => None
  end.

Definition is_bool_op (op : bop) : bool :=
  match op with
  | And | Or => true
  | _ => false
  end.

Definition bool_op (op : bop) : option (bool -> bool -> bool) :=
  match op with
  | And => Some andb
  | Or => Some orb
  | _ => None
  end.

Definition is_cmp_op (op : bop) : bool :=
  match op with
  | Eq | Lt => true
  | _ => false
  end.

Definition cmp_op (op : bop) : option (nat -> nat -> bool) :=
  match op with
  | Eq => Some eqb
  | Lt => Some ltb
  | _  => None
  end.

(** Call-by-value reduction relation *)
Inductive step : term -> term -> Prop :=
(* pure STLC *)
| Step_AppAbs : forall x T2 t1 v2,
    value v2 ->
    <[ (fun x:T2 -> t1) v2 ]> --> <[ [x:=v2]t1 ]>
| Step_App1 : forall t1 t1' t2,
    t1 --> t1' ->
    <[ t1 t2 ]> --> <[ t1' t2 ]>
| Step_App2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    <[ v1 t2 ]> --> <[ v1 t2' ]>
(* Let *)
| Step_LetVal : forall y v1 t2,
    value v1 ->
    <[ let y := v1 in t2 ]> --> <[ [y := v1] t2 ]>
| Step_Let : forall y t1 t1' t2,
    t1 --> t1'  ->
    <[ let y := t1 in t2 ]> --> <[ let y := t1' in t2 ]>
(* If then else *)
| Step_IfTrue : forall t1 t2,
    <[ if true then t1 else t2 ]> --> t1
| Step_IfFalse : forall t1 t2,
    <[ if false then t1 else t2 ]> --> t2
| Step_If: forall t t' t1 t2,
    t --> t' ->
    <[ if t then t1 else t2 ]> --> <[ if t' then t1 else t2 ]>
(* Binary Operators *)
| Step_BOpNat :
  forall bop (n1 n2 : nat) bop_f,
    nat_op bop = Some bop_f -> 
    (T_BOp bop n1 n2) --> T_Nat (bop_f n1 n2)
| Step_BOpBool :
  forall bop (b1 b2 : bool) bop_f,
    bool_op bop = Some bop_f -> 
    (T_BOp bop b1 b2) --> T_Bool (bop_f b1 b2)
| Step_BOpCmp :
  forall bop (n1 n2 : nat) bop_f,
    cmp_op bop = Some bop_f -> 
    (T_BOp bop n1 n2) --> T_Bool (bop_f n1 n2)
| Step_Bop1 : forall bop t1 t1' t2,
    t1 --> t1' ->
    (T_BOp bop t1 t2) --> (T_BOp bop t1' t2)  
| Step_Bop2 : forall bop v1 t2 t2',
    value v1 ->    
    t2 --> t2' ->
    (T_BOp bop v1 t2) --> (T_BOp bop v1 t2')
(* Unary Operators *)
| Step_UOpBool : forall (b : bool),
    (T_UOp Neg b) --> T_Bool (negb b)
| Step_UOp : forall t t',
    t --> t' ->
    (T_UOp Neg t) --> (T_UOp Neg t')
(* Pairs *)
| Step_Pair1 : forall t1 t1' t2,
    t1 --> t1' ->
    <[ (t1, t2) ]> --> <[ (t1', t2) ]>
| Step_Pair2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    <[ (v1, t2) ]> --> <[ (v1, t2') ]>
| Step_FstPair : forall v1 v2, 
    value v1 -> value v2 ->
    <[ (v1, v2).1 ]> --> <[ v1 ]>
| Step_Fst : forall t t', 
    t --> t' ->
    <[ t.1 ]> --> <[ t'.1 ]>
| Step_SndPair : forall v1 v2, 
    value v1 -> value v2 ->
    <[ (v1, v2).2 ]> --> <[ v2 ]>
| Step_Snd : forall t t', 
    t --> t' ->
    <[ t.2 ]> --> <[ t'.2 ]>
(* sums *)
| Step_Inl : forall t1 t1' T2,
    t1 --> t1' ->
    <[ inl T2 t1 ]> --> <[ inl T2 t1' ]>
| Step_Inr : forall t2 t2' T1,
    t2 --> t2' ->
    <[ inr T1 t2 ]> --> <[ inr T1 t2' ]>
| Step_Case : forall t t' x1 t1 x2 t2,
    t --> t' ->
    <[ case t of | inl x1 => t1 | inr x2 => t2 ]> -->
    <[ case t' of | inl x1 => t1 | inr x2 => t2 ]>
| Step_CaseInl : forall v x1 t1 x2 t2 T2,
    value v ->
    <[ case inl T2 v of | inl x1 => t1 | inr x2 => t2 ]> --> <[ [x1:=v]t1 ]>
| Step_CaseInr : forall v x1 t1 x2 t2 T1,
    value v ->
    <[ case inr T1 v of | inl x1 => t1 | inr x2 => t2 ]> --> <[ [x2:=v]t2 ]>
where "t '-->' t'" := (step t t').

(** ** Typing *)

(** To formalize typing we define a partial map data type to use
    for typing environments. We represent environments as functions
    from strings (identifiers) to optional values. We define
    operations and notations. *)

Definition partial_map A := string -> option A.

Definition empty {A : Type} : partial_map A :=
  fun _ => None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  fun x' => if String.eqb x x' then Some v else m x'.

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

(** The type of typing environments. *)
Definition context := string -> option type.

Reserved Notation "Gamma '⊢' t ':' T" (at level 40, t custom ML, T custom ML_ty at level 0).

(* The typing relation *)
Inductive has_type : context -> term -> type -> Prop :=
  (* Pure STLC *)
  | Ty_Var : forall Gamma x A,
      Gamma x = Some A ->
      Gamma ⊢ x : A
  | Ty_Abs : forall Gamma x t A B ,
      (x |-> A ; Gamma) ⊢ t : B ->
      Gamma ⊢ (fun x : A -> t) : (A -> B)
  | Ty_App : forall Gamma t1 t2 A B,
      Gamma ⊢ t1 : (A -> B) ->
      Gamma ⊢ t2 : A ->
      Gamma ⊢ t1 t2 : B
  (* Let *)
  | Ty_Let : forall Gamma x t1 t2 A B,
      Gamma ⊢ t1 : A ->
      (x |-> A ; Gamma) ⊢ t2 : B ->
      Gamma ⊢ (let x := t1 in t2) : B
  (* Bools *)
  | Ty_Bool : forall Gamma (b : bool),
      Gamma ⊢ b : Bool
  | Ty_If : forall Gamma t1 t2 t3 A,
      Gamma ⊢ t1 : Bool ->
      Gamma ⊢ t2 : A ->
      Gamma ⊢ t3 : A ->
      Gamma ⊢ if t1 then t2 else t3 : A
  | Ty_BopBool : forall Gamma bop t1 t2,
      Gamma ⊢ t1 : Bool ->
      Gamma ⊢ t2 : Bool ->
      is_bool_op bop = true ->
      Gamma ⊢ { T_BOp bop t1 t2 } : Bool
  | Ty_UOp : forall Gamma uop t1,
      Gamma ⊢ t1 : Bool ->
      Gamma ⊢ { T_UOp uop t1 } : Bool
  (* Numbers *)
  | Ty_Nat : forall Gamma (n : nat),
      Gamma ⊢ n : Nat
  | Ty_BopNat : forall Gamma bop t1 t2,
      Gamma ⊢ t1 : Nat ->
      Gamma ⊢ t2 : Nat ->
      is_nat_op bop = true ->
      Gamma ⊢ { T_BOp bop t1 t2 } : Nat
  | Ty_BopCmp : forall Gamma bop t1 t2,
      Gamma ⊢ t1 : Nat ->
      Gamma ⊢ t2 : Nat ->
      is_cmp_op bop = true ->
      Gamma ⊢ { T_BOp bop t1 t2 } : Bool
  (* Pairs *)
  | Ty_Pair : forall Gamma t1 t2 A B,
      Gamma ⊢ t1 : A ->
      Gamma ⊢ t2 : B ->
      Gamma ⊢ (t1, t2) : (A * B)
  | Ty_Fst : forall Gamma t1 A B,
      Gamma ⊢ t1 : (A * B) ->
      Gamma ⊢ t1.1 : A
  | Ty_Snd : forall Gamma t1 (A B : type),
      Gamma ⊢ t1 : (A * B) ->
      Gamma ⊢ t1.2 : B
  (* Sums *)
  | Ty_Inl : forall Gamma t1 A B,
      Gamma ⊢ t1 : A ->
      Gamma ⊢ (inl B t1) : (A + B)
  | Ty_Inr : forall Gamma t2 A B,
      Gamma ⊢ t2 : B ->
      Gamma ⊢ (inr A t2) : (A + B)
  | Ty_Case : forall Gamma t x1 A t1 x2 B t2 C,
      Gamma ⊢ t : (A + B) ->
      (x1 |-> A ; Gamma) ⊢ t1 : C ->
      (x2 |-> B ; Gamma) ⊢ t2 : C ->
      Gamma ⊢ (case t of | inl x1 => t1 | inr x2 => t2) : C
where "Gamma '⊢' t ':' T" := (has_type Gamma t T).


(** We extend the auto core database with the constructors of the
    [value], [step] and [has_type] relations. *)

Hint Constructors value : core.
Hint Constructors step : core.
Hint Constructors has_type : core.

(** ** Type Safety **)

Ltac inv H := inversion H; clear H; subst.

(** We can now move on to the proof of progress and preservation. *)

(** *** Canonical Forms *)

(** We first prove a series of _canonical forms_ lemmas.  They state
    that if a term that is a value has a certain type, then it must be
    a value of that type. They are proved by straightforward inversion
    of the value and typing relations. *)

Lemma canonical_forms_bool :
  forall t,
    empty ⊢ t : Bool ->
    value t ->
    (t = <[ true ]>) \/ (t = <[ false ]>).
Proof.
  intros t Htyp Hval.
  inv Hval; inv Htyp.
  destruct b; auto.
Qed.

Lemma canonical_forms_nat :
  forall t,
    empty ⊢ t : Nat ->
    value t ->
    exists (n : nat), t = <[ n ]>.
Proof.
  intros t Htyp Hval.
  inv Hval; inv Htyp. eauto.
Qed.

Lemma canonical_forms_fun :
  forall t T1 T2,
    empty ⊢ t : (T1 -> T2) ->
    value t ->
    exists x u, t = <[ fun x : T1  -> u ]>.
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp. eauto.
Qed.

Lemma canonical_forms_sum :
  forall t T1 T2,
    empty ⊢ t : (T1 + T2) ->
    value t ->
    (exists t1, t = <[ inl T2 t1 ]> /\ value t1) \/
    (exists t2, t = <[ inr T1 t2 ]> /\ value t2).
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp; eauto.
Qed.

Lemma canonical_forms_prod :
  forall t T1 T2,
    empty ⊢ t : (T1 * T2) ->
    value t ->
    exists t1 t2, t = <[ (t1, t2) ]> /\ value t1 /\ value t2.
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp; eauto.
Qed.

(** Helper lemmas for binary operators *)

Lemma is_nat_op_lemma :
  forall bop, is_nat_op bop = true -> exists f, nat_op bop = Some f. 
Proof. intros []; simpl; try discriminate; eauto. Qed.

Lemma is_bool_op_lemma :
  forall bop, is_bool_op bop = true -> exists f, bool_op bop = Some f. 
Proof. intros []; simpl; try discriminate; eauto. Qed.

Lemma is_cmp_op_lemma :
  forall bop, is_cmp_op bop = true -> exists f, cmp_op bop = Some f. 
Proof. intros []; simpl; try discriminate; eauto. Qed.

(** *** Progress *)

(** Note: Proof of certain cases and comments are taken from "Software
    Foundations"*)

(** Theorem: Suppose empty ⊢- t \in A.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)

Theorem progress : forall t T,
     empty ⊢ t : T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst.
  - (* Ty_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty ⊢ x : T] (since the context is empty). *)
    discriminate H.    
  - (* Ty_Abs *)
    (* If the [Ty_Abs] rule was the last used, then
       [t = fun x0 : T2 -> t1], which is a value. *)
    now left.
    
  - (* Ty_App *)
    
    (* If the last rule applied was Ty_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty ⊢ t1 : T1 -> T2]
         [empty ⊢ t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    
    destruct IHHt1.
    + reflexivity.
    + (* t1 is a value *)
      destruct IHHt2.
      * reflexivity.
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = fun x0 : T0 -> t11], since abstractions are the
           only values that can have an arrow type.  But
           [(fun x0 : T0 -> t11) t2 --> [x:=t2]t11] by [ST_AppAbs]. *)
        eapply canonical_forms_fun in Ht1; [| assumption ].

        destruct Ht1 as [x [u Heq]]; subst.
        eauto.        
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp].        
        exists <[t1 t2']>; auto.
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists <[t1' t2]>; auto.
  - (* Ty_let *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ]. 
  - (* Ty_Bool *)
    eauto.

  - (* TY_If *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ].

    edestruct (canonical_forms_bool t1); subst; eauto.

  - (* Ty_Bop bool *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct is_bool_op_lemma; eauto.

    edestruct (canonical_forms_bool t1); eauto; subst;
    edestruct (canonical_forms_bool t2); eauto; subst; eauto.

  - (* T_Uop bool *)
    destruct uop0.
    destruct IHHt as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto]. 
     
    edestruct (canonical_forms_bool t1); eauto; subst; eauto.

  - (* Ty_Nat *)
    left; auto.
  - destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct (canonical_forms_nat t1); eauto; subst.
    edestruct (canonical_forms_nat t2); eauto; subst.

    edestruct is_nat_op_lemma; eauto.

  - (* Ty_Bop cmp *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct (canonical_forms_nat t1); eauto; subst.
    edestruct (canonical_forms_nat t2); eauto; subst.

    edestruct is_cmp_op_lemma; eauto.

  - (* Ty_Pair *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    eauto.
    
  - (* Ty_fst *)
    destruct IHHt as [ | [t' Hstp]];
      subst; [ reflexivity | | now eauto ].
    edestruct (canonical_forms_prod t1) as [ v1 [v2 [Hstp1 [Hv1 Hv2]]]]; eauto.
    subst; eauto.

  - (* Ty_snd *)
    destruct IHHt as [ | [t' Hstp]];
      subst; [ reflexivity | | now eauto ].
    edestruct (canonical_forms_prod t1) as [ v1 [v2 [Hstp1 [Hv1 Hv2]]]]; eauto.
    subst; eauto.

      - (* Ty_Inl *)
    destruct IHHt as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ]. 

  - (* Ty_Inr *)
    destruct IHHt as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ].

  - (* Ty_case *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ].

    edestruct (canonical_forms_sum t) as [ [v1 [Hstp1 Hv1]] | [v2 [Hstp2 Hv2]]];
      eauto; subst; eauto.

Qed.


(** *** Weakening *)

(** In order to prove preservation, we first need to prove a weakening
    lemma. That is, if [Gamma ⊢ t : A], then [Gamma' ⊢ t : A], for any
    [Gamma'] that contains all the bindings of [Gamma], and possibly
    more. *)

(** We formalize a notion of submap. A map [m] is a submap of [m'], if
    any mapping [x |-> v] that is in [m] is also in [m'].  *)

Definition submap {A : Type} (m m' : partial_map A) : Prop :=
  forall x v, m x = Some v -> m' x = Some v.

(** We prove some useful lemmas for maps and the submap relation. *)

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite eqb_refl. reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update.
  apply eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma submap_update :
  forall (A : Type) (m m' : partial_map A) (x : string) (vx : A),
  submap m m' ->
  submap (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold submap.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.


(** Weakening follows easily by induction on the typing derivation. *)

Lemma weakening :
  forall Gamma Gamma' t A,
    submap Gamma Gamma' ->
    Gamma  ⊢ t : A  ->
    Gamma' ⊢ t : A.
Proof.
  intros Gamma Gamma' t  A Hsub Ht.
  revert Gamma' Hsub.
  induction Ht; eauto 7 using submap_update.
Qed.

Corollary weakening_empty :
  forall Gamma t A,
    empty ⊢ t : A  ->
    Gamma ⊢ t : A.
Proof.
  intros Gamma t A.
  eapply weakening.
  discriminate.
Qed.


(** *** Substitution Preserves Typing *)

(** Another crucial lemma that we will use is that substitution
    preserves typing. This lemma says that if

    [(x |-> B ; Gamma) ⊢ t : A]

    then we can substitute any closed term of type [B] for [x], and
    the resulting term will still have type [A]. That is, 
 
    if [empty ⊢ v : B] then [Gamma ⊢ [x:=v]t : A].
*)


(** Before proceeding, we need to establish some intuitive properties
    about partial maps. To do so, we will rely on the axiom of
    functional extensionality. This axiom states that two functions
    are equal if they produce the same output for all inputs:

    [forall f g, (forall x, f x = g x) -> f = g]

    This intuitive statement cannot be directly proven using the
    standard definition of equality in Coq, which requires syntactic
    equality. However, adding this axiom is logically sound and
    simplifies reasoning about functions.

   It is worth noting that we could have proved preservation without
   invoking functional extensionality, but the resulting proof would
   be more cumbersome and tedious. By using this axiom, we streamline
   the process while maintaining the rigor of our reasoning. *)

Require Import Coq.Logic.FunctionalExtensionality. 

Check functional_extensionality.

Lemma update_shadow :
  forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x y); subst; eauto.
Qed.

Lemma update_same :
  forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x y); subst; eauto.
Qed.

Lemma update_permute :
  forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2 Hneq. unfold update.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x1 y); subst; eauto.
  destruct (eqb_spec x2 y); subst; eauto.
  congruence. 
Qed.

(** Substitution preserves typing lemma. *)

Lemma substitution_preserves_typing :
  forall Gamma x v t A B,
    (x |-> B ; Gamma) ⊢ t : A ->
    empty ⊢ v : B   ->
    Gamma ⊢ [x:=v]t : A.
Proof.
  intros Gamma x v t A B Ht Hv.
  revert Gamma A Ht Hv. 
  induction t; intros Gamma A Ht1 Ht2; inv Ht1; simpl; eauto.
  - (* T_Abs *)
    destruct (eqb_spec x s); subst; apply Ty_Abs.
    + (* x = s *)
      rewrite update_shadow in H4. assumption.
    + (* x <> s *)
      apply IHt; auto.
      rewrite update_permute; auto.

  - (* T_Var *)
    destruct (eqb_spec x s); subst.
    + (* x = s *)
      rewrite update_eq in H1. inv H1. 
      apply weakening_empty. assumption.
    + (* x <> y *)
      apply Ty_Var. rewrite update_neq in H1; auto.

  - (* T_let *)
    eapply Ty_Let.
    + eapply IHt1; eauto.
    + destruct (eqb_spec x s); subst.
      * (* x = s *)        
        rewrite update_shadow in H5. assumption.
      * (* x <> s *)        
        eapply IHt2; auto.
        rewrite update_permute; eauto.
  - (* T_Case *)
    eapply Ty_Case.
    + now eauto.
    + destruct (eqb_spec x s); subst.
      * (* x = s *)
        rewrite update_shadow in H7. assumption.
      * (* x <> s *)
        apply IHt2.
        rewrite update_permute; auto.
        assumption.
    + destruct (eqb_spec x s0); subst.
      * (* x = s0 *)
        rewrite update_shadow in H8. assumption.
      * (* x <> s0 *)
        apply IHt3.
        rewrite update_permute; auto.
        assumption.
Qed.

(** *** Preservation *)

(** We can now prove the preservation theorem. *)

Theorem preservation :
  forall t t' A,
    empty ⊢ t : A  ->
    t --> t'  ->
    empty ⊢ t' : A.
Proof.
  intros t t' A Htyp. revert t'.
  remember empty as Gamma.
  induction Htyp; intros t' Hstep; subst.
  - (* Ty_Var *)
    inv Hstep.
  - (* Ty_Abs *)
    inv Hstep.
  - (* Ty_App *)
    inv Hstep.
    inv Htyp1.
    + eapply substitution_preserves_typing; eauto.
    + eauto.
    + eauto.

  - (* Ty_Let *)
    inv Hstep; eauto.
    eapply substitution_preserves_typing; eauto.

  - (* Ty_Bool *)
    inv Hstep.

  - (* Ty_If *)
    inv Hstep; eauto.

  - (* Ty_Bop *)
    inv Hstep; eauto.
    
    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_UOp *)
    inv Hstep; eauto.

  - (* Ty_Nat *)
    inv Hstep.

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_Pair *)
    inv Hstep; eauto.

  - (* Ty_Fst *)
    inv Hstep; eauto.
    
    inv Htyp; eauto. 

  - (* Ty_Snd *)
    inv Hstep; eauto.
    
    inv Htyp; eauto. 

  - (* Ty_inl *)
    inv Hstep; eauto.
    
  - (* Ty_inr *)
    inv Hstep; eauto.
    
  - (* Ty_case *)
    inv Hstep; eauto.
    + inv Htyp1.
      eapply substitution_preserves_typing; eauto.
    + inv Htyp1. 
      eapply substitution_preserves_typing; eauto.

Qed. 


(** ** Type Checking *)

(** Lastly, we define a typechecking program that we prove sound and
    complete with respect to our typing relation. *)


(** First, we define equality on types by recursion on their
    structure. *)
Fixpoint ty_eqb (A B: type) : bool :=
  match A, B with
  | Bool, Bool => true
  | Nat, Nat => true
  | Unit, Unit => true
  | <[[ A1 -> A2 ]]>, <[[ B1 -> B2 ]]> =>
      andb (ty_eqb A1 B1) (ty_eqb A2 B2)
  | <[[ A1 + A2 ]]>, <[[ B1 + B2 ]]> =>
      andb (ty_eqb A1 B1) (ty_eqb A2 B2)
  | <[[ A1 * A2 ]]>, <[[ B1 * B2 ]]> =>
      andb (ty_eqb A1 B1) (ty_eqb A2 B2)
  | _, _ => false
  end.


(** The typechecking function is defined by induction on the input term
    and returns either some type (the type of the term) or nothing ([None]),
    if the term is not well-typed. *)

(** To avoid boilerplate code when writing a function that manipulates
    a lot of [option] types, we introduce a so called _monadic_
    notation for sequencing operations.

    The sequencing operation [x <- e1 ;; e2] evaluates [e1] and if it
    returns some value, then it binds it to x, and evaluates
    [e2]. Otherwise, it propagates [None].

    The _action_ [return v] "returns" [Some v], and the _action_
    [fail] returns [None]. *)

Notation "x <- e1 ;; e2" := (match e1 with
                             | Some x => e2
                             | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e " := (Some e) (at level 60).

Notation " 'fail' " := None.

(* Note: We will explore monads in more depth later in the course *)

Fixpoint type_check (Gamma : context) (t : term) : option type :=
  match t with
  (*  Pure STLC *)
  | T_Var x => Gamma x
  | <[ fun x : A -> t1 ]> =>
      B <- type_check (x |-> A ; Gamma) t1 ;;
      return <[[ A -> B ]]>
  | <[ t1 t2 ]> =>
      A <- type_check Gamma t1 ;;
      B <- type_check Gamma t2 ;;
      match A with
      | <[[ A1 -> A2 ]]> =>
          if ty_eqb A1 B then return A2 else fail
      | _ => fail
      end
  (* Let *)
  | <[ let y := t1 in t2 ]> =>
      A <- type_check Gamma t1 ;;
      type_check (y |-> A ; Gamma) t2
  (* Booleans *)
  | T_Bool _ => return <[[ Bool ]]>
  | <[ if b then t1 else t2 ]> =>
      A <- type_check Gamma b ;;
      B <- type_check Gamma t1 ;;
      C <- type_check Gamma t2 ;;
      match A with
      | <[[ Bool ]]> => if ty_eqb B C then return B else fail
      | _ => fail
      end
  (* Numbers *)
  | T_Nat n => return <[[ Nat ]]>    
  (* Binary operators *)
  | T_BOp bop t1 t2 =>
      A <- type_check Gamma t1 ;;
      B <- type_check Gamma t2 ;;
      if ty_eqb A B then 
        if is_nat_op bop then
          if ty_eqb A Nat then return Nat else fail
        else if is_cmp_op bop then
          if ty_eqb A Nat then return Bool else fail
        else if is_bool_op bop then
          if ty_eqb A Bool then return Bool else fail
        else fail
      else fail
  (* Unary operators *)
  | T_UOp b t1 =>
      A <- type_check Gamma t1 ;;
      if ty_eqb A Bool then return Bool else fail
  (* Pairs *)
  | <[ (t1, t2)]> =>
      A <- type_check Gamma t1 ;;
      B <- type_check Gamma t2 ;;
      return <[[ A * B ]]>
  | <[ t1.1 ]> =>
      A <- type_check Gamma t1 ;;
      match A with
      | <[[ A1 * A2 ]]> => return A1
      | _ => fail
      end
  | <[ t1.2 ]> =>
      A <- type_check Gamma t1 ;;
      match A with
      | <[[ A1 * A2 ]]> => return A2
      | _ => fail
      end
  (* Sums *)
  | <[ inl B t1 ]> =>
      A <- type_check Gamma t1 ;;
      return <[[ A + B ]]>
  | <[ inr A t1 ]> =>
      B <- type_check Gamma t1 ;;
      return <[[ A + B ]]>
  | <[ case t of | inl y1 => t1 | inr y2 => t2 ]> =>
      A <- type_check Gamma t ;;
      match A with
      | <[[ A1 + A2 ]]> =>
          B <- type_check (y1 |-> A1 ; Gamma) t1 ;; 
          C <- type_check (y2 |-> A2 ; Gamma) t2 ;;
          if ty_eqb B C then return B else fail
      | _ => fail
      end
  end.

(** *** Correctness of Type Checking *)

(** We first prove some simple lemmas about type equality. *)

Lemma ty_eqb_eq :
  forall t1 t2, ty_eqb t1 t2 = true -> t1 = t2.
Proof.
  induction t1; intros []; simpl; intros H; try congruence.
  - apply andb_prop in H. destruct H.
    erewrite IHt1_1; eauto.
    erewrite IHt1_2; eauto.
  - apply andb_prop in H. destruct H.
    erewrite IHt1_1; eauto.
    erewrite IHt1_2; eauto.
  - apply andb_prop in H. destruct H.
    erewrite IHt1_1; eauto.
    erewrite IHt1_2; eauto.
Qed.    

Lemma ty_eqb_refl :
  forall t, ty_eqb t t = true.
Proof.
  induction t; simpl; auto.
  - rewrite IHt1; eauto.
  - rewrite IHt1; eauto.
  - rewrite IHt1; eauto.
Qed.    


Ltac simpl_tc :=
  match reverse goal with
  | [H: ty_eqb ?t1 ?t2 = true |- _] => apply ty_eqb_eq in H; subst
  | [H: Some _ = Some _ |- _] => inv H
  | [_ : match ?t with _ => _ end = _ |- _] =>
      destruct t eqn:?; try congruence
  | [_: context[ty_eqb ?t1 ?t2] |- _] =>
      destruct (ty_eqb t1 t2) eqn:?; subst; try congruence
  end.

(** Soundness. *)
Theorem type_checking_sound :
  forall Gamma t A,
    type_check Gamma t = Some A ->
    Gamma ⊢ t : A.
Proof.
  intros Gamma t. revert Gamma.
  induction t; intros Gamma A Htc; simpl in *;
    try now (repeat simpl_tc; eauto).
Qed.

(** Completeness. *)
Theorem type_checking_complete :
  forall Gamma t A,
    Gamma ⊢ t : A ->
    type_check Gamma t = Some A.
Proof.
  intros Gamma t A Htyp; induction Htyp; simpl; eauto;
  try rewrite IHHtyp; try rewrite IHHtyp1; try rewrite IHHtyp2;
    try rewrite IHHtyp3;
    try rewrite ty_eqb_refl; try reflexivity.
  
  - destruct bop0; simpl in *; try congruence.
  - destruct bop0; simpl in *; try congruence.
  - destruct bop0; simpl in *; try congruence.    
Qed.
