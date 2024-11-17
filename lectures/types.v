Require Import Coq.Strings.String Coq.Init.Nat Lia.


(** * Introduction to Type Systems **)


(** ** Syntax **)

(** The abstract syntax tree of lambda calculus. *)

Inductive type : Type :=
| Arrow : type -> type -> type
| Nat   : type
| Bool  : type
| Unit  : type
| Sum   : type -> type -> type
| Prod  : type -> type -> type.

(** Binary Operators *)
Inductive bop :=
| Plus | Minus | Mult
| And | Or | Lt | Eq.

(** Unary Operators *)
Inductive uop :=
| Neg.

Inductive term : Type :=
(* Functions *)
| T_App : term -> term -> term
| T_Lambda : string -> type -> term -> term
(* Variables *)
| T_Var : string -> term
(* Natural Numbers *)
| T_Nat : nat -> term
(* Booleans *)
| T_Bool : bool -> term
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
(* Let *)
| T_Let : string -> term -> term -> term
(* If *)
| T_If : term -> term -> term -> term
.

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


Definition nat_op (op : bop) : option (nat -> nat -> nat) :=
  match op with
  | Plus => Some add
  | Minus => Some sub
  | Mult => Some mul
  | _ => None
  end.

Definition bool_op (op : bop) : option (bool -> bool -> bool) :=
  match op with
  | And => Some andb
  | Or => Some orb
  | _ => None
  end.

Definition cmp_op (op : bop) : option (nat -> nat -> bool) :=
  match op with
  | Eq => Some eqb
  | Lt => Some ltb
  | _  => None
  end.

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
(* if then else *)
| Step_IfTrue : forall t1 t2,
    <[ if true then t1 else t2 ]> --> t1
| Step_IfFalse : forall t1 t2,
    <[ if false then t1 else t2 ]> --> t2
| Step_If: forall t t' t1 t2,
    t --> t' ->
    <[ if t then t1 else t2 ]> --> <[ if t' then t1 else t2 ]>
(* let *)
| Step_LetVal : forall y v1 t2,
    value v1 ->
    <[ let y := v1 in t2 ]> --> <[ [y := v1] t2 ]>
| Step_Let : forall y t1 t1' t2,
    t1 --> t1'  ->
    <[ let y := t1 in t2 ]> --> <[ let y := t1' in t2 ]>
where "t '-->' t'" := (step t t').


(** *** Typing *)


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


Definition context := string -> option type.

Reserved Notation "Gamma '|-' t ':' T" (at level 40, t custom ML, T custom ML_ty at level 0).

Notation "{ x }" := x (in custom ML at level 1, x constr).

Inductive has_type : context -> term -> type -> Prop :=
  (* pure STLC *)
  | Ty_Var : forall Gamma x A,
      Gamma x = Some A ->
      Gamma |- x : A
  | Ty_Abs : forall Gamma x t A B ,
      (x |-> A ; Gamma) |- t : B ->
      Gamma |- (fun x : A -> t) : (A -> B)
  | Ty_App : forall Gamma t1 t2 A B,
      Gamma |- t1 : (A -> B) ->
      Gamma |- t2 : A ->
      Gamma |- t1 t2 : B
  (* numbers *)
  | Ty_Nat : forall Gamma (n : nat),
      Gamma |- n : Nat
  | Ty_BopNat : forall Gamma bop t1 t2 f,
      Gamma |- t1 : Nat ->
      Gamma |- t2 : Nat ->
      nat_op bop = Some f ->  (* TODO nicer*)
      Gamma |- { T_BOp bop t1 t2 } : Nat
  | Ty_BopCmp : forall Gamma bop t1 t2 f,
      Gamma |- t1 : Nat ->
      Gamma |- t2 : Nat ->
      cmp_op bop = Some f ->  (* TODO nicer*)
      Gamma |- { T_BOp bop t1 t2 } : Bool
  (* bools *)
  | Ty_Bool : forall Gamma (b : bool),
      Gamma |- b : Bool
  | Ty_BopBool : forall Gamma bop t1 t2 f,
      Gamma |- t1 : Bool ->
      Gamma |- t2 : Bool ->
      bool_op bop = Some f ->  (* TODO nicer*)
      Gamma |- { T_BOp bop t1 t2 } : Bool
  | Ty_If : forall Gamma t1 t2 t3 A,
      Gamma |- t1 : Bool ->
      Gamma |- t2 : A ->
      Gamma |- t3 : A ->
      Gamma |- if t1 then t2 else t3 : A
  (* sums *)
  | Ty_Inl : forall Gamma t1 A B,
      Gamma |- t1 : A ->
      Gamma |- (inl B t1) : (A + B)
  | Ty_Inr : forall Gamma t2 A B,
      Gamma |- t2 : B ->
      Gamma |- (inr A t2) : (A + B)
  | Ty_Case : forall Gamma t x1 A t1 x2 B t2 C,
      Gamma |- t : (A + B) ->
      (x1 |-> A ; Gamma) |- t1 : C ->
      (x2 |-> B ; Gamma) |- t2 : C ->
      Gamma |- (case t of | inl x1 => t1 | inr x2 => t2) : C
  (* pairs *)
  | Ty_Pair : forall Gamma t1 t2 A B,
      Gamma |- t1 : A ->
      Gamma |- t2 : B ->
      Gamma |- (t1, t2) : (A * B)
  | Ty_Fst : forall Gamma t1 A B,
      Gamma |- t1 : (A * B) ->
      Gamma |- t1.1 : A
  | Ty_Snd : forall Gamma t1 (A B : type),
      Gamma |- t1 : (A * B) ->
      Gamma |- t1.2 : B
  (* let *)
  | Ty_Let : forall Gamma x t1 t2 A B,
      Gamma |- t1 : A ->
      (x |-> A ; Gamma) |- t2 : B ->
      Gamma |- (let x := t1 in t2) : B
where "Gamma '|-' t ':' T" := (has_type Gamma t T).

Hint Constructors value : core.
Hint Constructors step : core.
Hint Constructors has_type : core.

(** ** Type Safety **)


Ltac inv H := inversion H; clear H; subst.

(** *** Canonical Forms *)

Lemma canonical_forms_bool :
  forall t,
    empty |- t : Bool ->
    value t ->
    (t = <[ true ]>) \/ (t = <[ false ]>).
Proof.
  intros t Htyp Hval.
  inv Hval; inv Htyp.
  destruct b; auto.
Qed.

Lemma canonical_forms_nat :
  forall t,
    empty |- t : Nat ->
    value t ->
    exists (n : nat), t = <[ n ]>.
Proof.
  intros t Htyp Hval.
  inv Hval; inv Htyp. eauto.
Qed.

Lemma canonical_forms_fun :
  forall t T1 T2,
    empty |- t : (T1 -> T2) ->
    value t ->
    exists x u, t = <[ fun x : T1  -> u ]>.
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp. eauto.
Qed.

Lemma canonical_forms_sum :
  forall t T1 T2,
    empty |- t : (T1 + T2) ->
    value t ->
    (exists t1, t = <[ inl T2 t1 ]> /\ value t1) \/
    (exists t2, t = <[ inr T1 t2 ]> /\ value t2).
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp; eauto.
Qed.

Lemma canonical_forms_prod :
  forall t T1 T2,
    empty |- t : (T1 * T2) ->
    value t ->
    exists t1 t2, t = <[ (t1, t2) ]> /\ value t1 /\ value t2.
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp; eauto.
Qed.

(** Theorem: Suppose empty |-- t \in T.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)

Theorem progress : forall t T,
     empty |- t : T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst.
  - (* Ty_Var *)
    (* The final rule in the given typing derivation cannot be
       [T_Var], since it can never be the case that
       [empty |-- x \in T] (since the context is empty). *)
    discriminate H.
  - (* T_Abs *)
    (* If the [T_Abs] rule was the last used, then
       [t = \ x0 : T2, t1], which is a value. *)
    now left. 
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty |-- t1 \in T1 -> T2]
         [empty |-- t2 \in T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    destruct IHHt1; subst.
    + reflexivity.
    + (* t1 is a value *)
      destruct IHHt2; subst.
      * reflexivity.
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = \x0 : T0, t11], since abstractions are the
           only values that can have an arrow type.  But
           [(\x0 : T0, t11) t2 --> [x:=t2]t11] by [ST_AppAbs]. *)
        destruct H; try now eauto.
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [ST_App2]. *)
        destruct H0 as [t2' Hstp]. exists <[t1 t2']>; auto.
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [ST_App1]. *)
      destruct H as [t1' Hstp]. exists <[t1' t2]>; auto.
  - (* T_Nat *)
    left; auto.
  - destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct (canonical_forms_nat t1); eauto; subst.
    edestruct (canonical_forms_nat t2); eauto; subst.

    eauto. 

  - (* T_Bop cmp *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct (canonical_forms_nat t1); eauto; subst.
    edestruct (canonical_forms_nat t2); eauto; subst.

    eauto.

  - (* Ty_Bool *)
    eauto.
    
  - (* T_Bop bool *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    
    edestruct (canonical_forms_bool t1); eauto; subst;
    edestruct (canonical_forms_bool t2); eauto; subst; eauto.

  - (* TY_If *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ].

    edestruct (canonical_forms_bool t1); subst; eauto.

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

  - (* Ty_let *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ].
Qed.

Definition submap {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.


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



Lemma weakening :
  forall Gamma Gamma' t A,
    submap Gamma Gamma' ->
    Gamma  |- t : A  ->
    Gamma' |- t : A.
Proof.
  intros Gamma Gamma' t  A Hsub Ht.
  revert Gamma' Hsub.
  induction Ht; eauto 7 using submap_update.
Qed.

Lemma weakening_empty :
  forall Gamma t A,
    empty |- t : A  ->
    Gamma |- t : A.
Proof.
  intros Gamma t A.
  eapply weakening.
  discriminate.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update.
Admitted.

Lemma update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  (* intros A m x v H. unfold update. rewrite <- H. *)
  (* apply t_update_same. *)
Admitted.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  (* intros A m x1 x2 v1 v2. unfold update. *)
  (* apply t_update_permute. *)
Admitted.

Lemma substitution_preserves_typing :
  forall Gamma x v t A B,
    (x |-> B ; Gamma) |- t : A ->
    empty |- v : B   ->
    Gamma |- [x:=v]t : A.
Proof.
  intros Gamma x v t A B Ht Hv.
  revert Gamma A Ht Hv. 
  (* Proof: By induction on the term [t].  Most cases follow
     directly from the IH, with the exception of [var]
     and [abs]. These aren't automatic because we must
     reason about how the variables interact. The proofs
     of these cases are similar to the ones in STLC.
     We refer the reader to StlcProp.v for explanations. *)
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
  - (* T_let *)
    eapply Ty_Let.
    + eapply IHt1; eauto.
    + destruct (eqb_spec x s); subst.
      * (* x = s *)        
        rewrite update_shadow in H5. assumption.
      * (* x <> s *)        
        eapply IHt2; auto.
        rewrite update_permute; eauto.
Qed.


Theorem preservation :
  forall t t' A,
    empty |- t : A  ->
    t --> t'  ->
    empty |- t' : A.
Proof.
  intros t t' A Htyp. revert t'.
  remember empty as Gamma.
  (* Proof: By induction on the given typing derivation.  Many
     cases are contradictory ([T_Var], [T_Abs]).  We show just
     the interesting ones. Again, we refer the reader to
     StlcProp.v for explanations. *)
  induction Htyp; intros t' Hstep; subst.
  - (* Ty_Var *)
    inv Hstep.
  - (* Ty_Abs *)
    inv Hstep.
  - (* Ty_App *)     
    inv Hstep; eauto.

    inv Htyp1. eapply substitution_preserves_typing; eauto.

  - (* Ty_Nat *)
    inv Hstep.

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_Bool *)
    inv Hstep.

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_If *)
    inv Hstep; eauto.

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

  - (* Ty_Pair *)
    inv Hstep; eauto.

  - (* Ty_Fst *)
    inv Hstep; eauto.
    
    inv Htyp; eauto. 

  - (* Ty_Snd *)
    inv Hstep; eauto.
    
    inv Htyp; eauto. 

  - (* Ty_Let *)
    inv Hstep; eauto.
    eapply substitution_preserves_typing; eauto.
Qed. 
