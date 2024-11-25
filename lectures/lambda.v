Require Import Coq.Strings.String Coq.Init.Nat Lia.


(** * Pure Lambda Calculus **)


(** The lambda calculus (λ-calculus) is an abstract model of
    computation introduced by Alonzo Church in the 1930s. As a
    theoretical framework for computation, lambda calculus is
    Turing-complete, meaning it can model any computation that a
    Turing machine can perform (Turing, 1937).

    Modern functional programming languages have their roots in lambda
    calculus. Essentially, lambda calculus can be thought of as a
    minimalistic functional programming language, providing a
    foundation for studying the semantics and formal properties of
    functional programming languages.


    Lambda calculus is a formal language consisting of three main
    components:

    - Functions (or _lambda abstractions_): Functions are written as
      "λx. e", where "x" is a variable that is bound within the
      function body "e". A more familiar syntax for functions is ML's
      "fun x -> e"

    - Function Applications: Function application is written as "e1
      e2", where "e1" is applied to "e2".

    - Variables: Variables are typically denoted using elements of a
      countably infinite set. Here we will be using strings.

    For example, consider the identity function applied to itself,
    written as: "(λx. x) (λx. x)".

   The syntax of lambda calculus can be defined by the following BNF
   grammar:

  term := λvar. term | term term | var

  with var ∈ {x, y, z, ... }

  Here we formalize the call-by-value and call-by-name semantics of
  lambda calculus, and we provide a proved-correct interpreter.
  Lastly, we build the AST of an untyped (for now) MiniML and we build
  an interpreter for it. *)

(** ** Pure Lambda Calculus: Syntax **)

(** The abstract syntax tree of lambda calculus. *)

Inductive term : Type :=
| App : term -> term -> term
| Lambda : string -> term -> term
| Var : string -> term.


(** Examples *)

Definition id : term := Lambda "x" (Var "x").

Definition app_id_id : term := App id id.

(** As usual, to make our lives slightly easier, we define some
    concrete syntax for lambda terms, using Coq's notations. *)

Declare Custom Entry LC.

Notation "<{ e }>" := e (e custom LC at level 99).
Notation "( x )" := x (in custom LC, x at level 99).
Notation "x" := x (in custom LC at level 0, x constr at level 0).
Notation "x y" := (App x y) (in custom LC at level 1, left associativity).
Notation "\ x , y" := (Lambda x y) (in custom LC at level 90,
                            x at level 99,
                            y custom LC at level 99,
                            left associativity).

(** Let's also define an implicit coercion to avoid writing the "Var"
    constructor in terms. *)

Coercion Var : string >-> term.

(** We define some commonly used variables. *)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

(** Examples, using notations *)

Definition id' : term := <{ \ x, x }>.

Definition app_id' : term := <{ id id }>.


(** ** Pure Lambda Calculus: CBV and CBN Semantics **)

(** To define the semantics we first formally define the substitution
    operation. We do not need to worry about making it explicitly
    capture avoiding: We only apply it to closed terms. Since CBV and
    CBN semantics do not evaluate under lambdas, and we only care
    about evaluating closed terms, substitution will never substitute
    open terms.

    Put more formally: CBV reduction preserves "closedness" of
    terms. *)

Fixpoint subst (x : string) (t' : term) (t : term) : term :=
  match t with
  | App t1 t2 => App (subst x t' t1) (subst x t' t2)
  | Lambda y t1 => if (x =? y)%string then Lambda y t1 else Lambda y (subst x t' t1)
  | Var y => if (x =? y)%string then t' else Var y
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom LC at level 20, x constr).

(** The reflexive transitive closure of a binary relation. Same with
    the definition we have used in Imp.v. *)

Inductive multi {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | multi_refl : forall a, multi R a a
  | multi_step : forall a b c,
    R a b ->
    multi R b c ->
    multi R a c.

(** *** Values **)

(** To define the evaluation strategy we need some notions of _value_.
    Value is a term that cannot be reduced any further. *)

Definition value (t : term) : bool :=
  match t with
  | Lambda _ _ => true
  | _ => false
  end.

(** We can now proceed to defining small step semantics that encode
    call-by-value and call-by-name evaluation strategies. *)

(** *** Call by Value *)

Module CBV.

  Reserved Notation "t '-->' t'" (at level 40).

  Inductive step : term -> term -> Prop :=
  | step_abs : forall x t1 v2,
      value v2 = true ->
      <{ (\x, t1) v2 }> --> <{ [x:=v2]t1 }>
  | step_app1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ t1 t2 }> --> <{ t1' t2 }>
  | step_app2 : forall v1 t2 t2',
      value v1 = true ->
      t2 --> t2' ->
      <{ v1 t2 }> --> <{ v1 t2' }>

  where "t '-->' t'" := (step t t').

  Notation multistep := (multi step).

  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

End CBV.


(** *** Call by Name *)

Module CBN.

  Reserved Notation "t '-->' t'" (at level 40).

  Inductive step : term -> term -> Prop :=
  | step_abs : forall x t1 t2,
      <{ (\x, t1) t2 }> --> <{ [x:=t2]t1 }>
  | step_app : forall t1 t1' t2,
      t1 --> t1' ->
      <{ t1 t2 }> --> <{ t1' t2 }>

  where "t '-->' t'" := (step t t').

  Notation multistep := (multi step).

  Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

End CBN.

Import CBV.

(** ** Big-step Call-by-value Semantics **)

Reserved Notation "t '==>' t'" (at level 40).


Inductive bigstep : term -> term -> Prop :=
| bigstep_abs : forall x t1,
      <{ \x, t1 }> ==> <{ \x, t1 }>
| bigstep_app : forall t1 x t1' t2 v2 v,
    t1 ==> <{ \x, t1' }> ->
    t2 ==> v2 ->
    <{ [x:=v2]t1' }> ==> v ->
    <{ t1 t2 }> ==> v

where "t '==>' t'" := (bigstep t t').

(** We prove some properties about the big-step semantics:

    - If [e ==> v], then v is a value.
    - If v is a value, then [v ==> v]. *)

Lemma bigstep_value :
  forall t1 t2, t1 ==> t2 -> value t2 = true.
Proof.
  intros t1 t2 Hyp. induction Hyp.
  - simpl. reflexivity.
  - assumption.
Qed.

Lemma value_bigstep :
  forall v,
    value v = true ->
    v ==> v.
Proof.
  intros v Hv. destruct v; simpl in *.
  - congruence.
  - apply bigstep_abs.
  - congruence.
Qed.

(** *** Case study: Equivalence Between Big-step and Small-step Semantics *)

Lemma multi_step_compose1 :
  forall t1 t2 t1',
    t1 -->* t1' ->
    <{ t1 t2 }> -->* <{ t1' t2 }>.
Proof.
  intros t1 t2 t1' H1.
  induction H1.
  - apply multi_refl.
  - eapply multi_step.
    + eapply step_app1. eassumption.
    + assumption.
Qed.

Lemma multi_step_compose2 :
  forall t1 t2 t2',
    t2 -->* t2' ->
    value t1 = true ->
    <{ t1 t2 }> -->* <{ t1 t2' }>.
Proof.
  intros t1 t2 t2' H1 Hval.
  induction H1.
  - apply multi_refl.
  - eapply multi_step.
    + eapply step_app2. assumption. eassumption.
    + assumption.
Qed.

Lemma multi_trans {A} (R : A -> A -> Prop) :
  forall a b c,
    multi R a b ->
    multi R b c ->
    multi R a c.
Proof.
  intros a b c H1 H2.
  induction H1.
  - assumption.
  - eapply multi_step. eassumption.
    eapply IHmulti. assumption.
Qed.

Lemma bigstep_step :
  forall t1 t2,
    t1 ==> t2 -> t1 -->* t2.
Proof.
  intros t1 t2 Hyp. induction Hyp.
  - apply multi_refl.
  - eapply multi_trans.
    + eapply multi_step_compose1. eassumption.
    + eapply multi_trans.
      * eapply multi_step_compose2. eassumption.
        reflexivity.
      * eapply multi_step.
        -- eapply step_abs.
           eapply bigstep_value. eassumption.
        -- assumption.
Qed.

Lemma step_bigstep_compose :
  forall t1 t2 t3,
    t1 --> t2 -> t2 ==> t3 -> t1 ==> t3.
Proof.
    intros t1 t2 t3 Hstep. revert t3. induction Hstep; intros t3 Hbstep.
    - eapply bigstep_app.
      + eapply bigstep_abs.
      + eapply value_bigstep. assumption.
      + assumption.
    - inversion Hbstep; subst.
      eapply IHHstep in H1.
      eapply bigstep_app; eassumption.
    - inversion Hbstep; subst.
      eapply IHHstep in H3.
      eapply bigstep_app; eassumption.
Qed.

Lemma step_bigstep :
  forall t1 t2,
    t1 -->* t2 -> value t2 = true -> t1 ==> t2.
Proof.
    intros t1 t2 Hyp Hval. induction Hyp.
    - destruct a; simpl in *.
      + congruence.
      + apply bigstep_abs.
      + congruence.
    - eapply step_bigstep_compose. eassumption.
      eauto.
Qed.


(** *** A Call-by-value Interpreter for Lambda Calculus *)

(** The interpreter closely follows the structure of the big-step
    semantics. *)
Fixpoint eval (fuel : nat) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      | <{ t1 t2 }> =>
          match eval fuel' t1 with
          | Some <{ \ x, t }> =>
              match eval fuel' t2 with
              | Some v => eval fuel' (<{ [x := v] t }>)
              | None => None
              end
          | _ => None
          end
      | <{ \x, t }> => Some <{ \x, t }>
      | Var x => None
      end
  end.

Ltac inv H := inversion H; subst; clear H.

(** To prove that the interpreter is correct with respect to the
    big-step semantics we need a lemma saying that the interpreter is
    monotonic in the fuel value.  That is, if evaluating a term with
    some fuel value returns a value, then evaluating the term with a
    larger fuel value returns the same value. *)

Lemma eval_motonic :
  forall n1 n2 t t',
    eval n1 t = Some t' ->
    n1 <= n2 ->
    eval n2 t = Some t'.
Proof.
  intros n1; induction n1; simpl; intros n2 t t' Heval Hleq.
  - congruence.
  - destruct t.
    + destruct (eval n1 t1) eqn:Heval1.
      * destruct t; try congruence.
        destruct (eval n1 t2) eqn:Heval2; try congruence.
        destruct n2; [ lia | ].
        simpl.
        erewrite IHn1; [ | eassumption | lia ].
        erewrite IHn1; [ | eassumption | lia ].
        apply IHn1; [ eassumption | lia ].
      * congruence.
    + inv Heval.
      destruct n2; [ lia | ]. reflexivity.
    + congruence.
Qed.

(** We can now formally prove that the interpreter correctly
    implements the big-step semantics. *)

Theorem eval_correct :
  forall t t',
    (exists n, eval n t = Some t') <-> t ==> t'.
Proof.
  intros t t'; split.
  - intros [n Heval].
    revert t t' Heval.
    induction n; simpl; intros t t' Heval.
    + congruence.
    + destruct t.
      * destruct (eval n t1) eqn:Heval1.
        -- destruct t; try congruence.
            destruct (eval n t2) eqn:Heval2; try congruence.
            econstructor; eauto.
        -- congruence.
      * inversion Heval; subst; eauto.
        constructor.
      * inversion Heval; subst; eauto.
  - intros Hbigstep. induction Hbigstep.
    + exists 1. eauto.
    + edestruct IHHbigstep1 as [n1 Hbs1].
      edestruct IHHbigstep2 as [n2 Hbs2].
      edestruct IHHbigstep3 as [n3 Hbs3].

      eexists (1 + (n1 + n2 + n3)). simpl.
      do 3 (erewrite eval_motonic; [ | eassumption | lia ]).

      reflexivity.
Qed.

(** ** From Lambda Calculus to an (Untyped) Mini ML *)

Module MiniML.

  (** Binary Operators *)
  Inductive bop :=
  | Plus | Minus | Mult
  | And | Or | Lt | Eq.

  (** Unary Operators *)
  Inductive uop :=
  | Neg.

  (** The abstract syntax tree of miniML. *)
  Inductive term : Type :=
  (* Functions *)
  | T_App : term -> term -> term
  | T_Lambda : string -> term -> term
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
  (* Let *)
  | T_Let : string -> term -> term -> term
  (* If *)
  | T_If : term -> term -> term -> term
  .

  Declare Custom Entry ML.
  Declare Scope ML_scope.


  Notation "<[ e ]>" := e (e custom ML at level 99) : ML_scope.
  Notation "( x )" := x (in custom ML, x at level 99).
  Notation "x" := x (in custom ML at level 0, x constr at level 0).
  Notation "x y" := (T_App x y) (in custom ML at level 1, left associativity).

  Notation "'fun' x '->' y" := (T_Lambda x y) (in custom ML at level 90,
                                     x at level 99,
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

  Notation "'true'" := true (at level 1).
  Notation "'true'" := (T_Bool true) (in custom ML at level 0).
  Notation "'false'" := false (at level 1).
  Notation "'false'" :=  (T_Bool false) (in custom ML at level 0).

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


  Coercion T_Var : string >-> term.
  Coercion T_Nat : nat >-> term.

  Open Scope ML_scope.

  (** Some variables *)

  Definition f : string := "f".
  Definition foo : string := "for".
  Definition bar : string := "bar".
  Definition fact : string := "fact".
  Definition n : string := "n".

  (** Recursion with the Y combinator diverges in CBV *)

  Definition Y := <[ fun f -> (fun x -> f (x x)) (fun x -> f (x x)) ]>.

  (** The Z combinator is the strict version of the Y combinator. *)

  Definition Z := <[ fun f -> (fun x -> f (fun y -> x x y)) (fun x -> f (fun y -> x x y)) ]>.

  (** Notation for recursion using the Z combinator. *)

  Notation "'letrec' f ':=' y 'in' z" :=
    (T_Let f (T_App Z (T_Lambda f y)) z)
      (in custom ML at level 90,
          f at level 99,
          y custom ML at level 99,
          z custom ML at level 99) : ML_scope.


  (** *** Substitution for MiniML. *)

  Fixpoint subst (x : string) (t' : term) (t : term) : term :=
    match t with
    | T_App t1 t2 => T_App (subst x t' t1) (subst x t' t2)
    | T_Lambda y t1 => if (x =? y)%string then T_Lambda y t1 else T_Lambda y (subst x t' t1)
    | T_Var y => if (x =? y)%string then t' else T_Var y
    | T_BOp op t1 t2 => T_BOp op (subst x t' t1) (subst x t' t2)
    | T_UOp op t => T_UOp op (subst x t' t)
    | T_Pair t1 t2 => T_Pair (subst x t' t1) (subst x t' t2)
    | T_Fst t => T_Fst (subst x t' t)
    | T_Snd t => T_Snd (subst x t' t)
    | T_Let y t1 t2 =>
        T_Let y  (subst x t' t1) (if (x =? y)%string then t1 else subst x t' t2)
    | T_If t1 t2 t3 =>
        T_If (subst x t' t1) (subst x t' t2) (subst x t' t3)
    | t => t
    end.


  Notation "'[' x ':=' s ']' t" := (subst x s t) (in custom ML at level 20, x constr).


  (** *** Interpreter for MiniML. *)

  Fixpoint eval (fuel : nat) (t : term) : option term :=
    match fuel with
    | 0 => None
    | S fuel' =>
        match t with
        (* Application *)
        | <[ t1 t2 ]> =>
            match eval fuel' t1 with
            | Some <[ fun x -> t ]> =>
                match eval fuel' t2 with
                | Some v => eval fuel' (subst x v t)
                | None => None
                end
            | _ => None
            end
        (* Let *)
        | <[ let x := t1 in t2]> => (* eval fuel' <[ (fun x -> t2) t1 ]> *)
            match eval fuel' t1 with
            | Some v => eval fuel' (subst x v t2)
            | None => None
            end
        (* If *)
        | <[ if t1 then t2 else t3 ]> =>
            match eval fuel' t1 with
            | Some (T_Bool true) => eval fuel' t2
            | Some (T_Bool false) => eval fuel' t3
            | _ => None
            end
        (* Bop *)
        | T_BOp bop t1 t2 =>
            match eval fuel' t1, eval fuel' t2 with
            | Some (T_Bool b1), Some (T_Bool b2) =>
                match bop with
                | And => Some (T_Bool (b1 && b2))
                | Or => Some (T_Bool (b1 || b2))
                | _ => None
                end
            | Some (T_Nat n1), Some (T_Nat n2) =>
               match bop with
               | Plus => Some (T_Nat (n1 + n2))
               | Minus => Some (T_Nat (n1 - n2))
               | Mult => Some (T_Nat (n1 * n2))
               | Lt => Some (T_Bool (n1 <? n2))
               | Eq => Some (T_Bool (n1 =? n2))
               | _ => None
               end
            | _, _ => None
            end
        (* Uop *)
        | T_UOp op t =>
            match eval fuel' t with
            | Some (T_Bool b) =>
                match op with
                | Neg => Some (T_Bool (negb b))
                end
            | _ => None
            end
        (* Fst *)
        | T_Fst t =>
            match eval fuel' t with
            | Some (T_Pair t1 _) => Some t1
            | _ => None
            end
        (* Snd *)
        | T_Snd t =>
            match eval fuel' t with
            | Some (T_Pair _ t2) => Some t2
            | _ => None
            end
        (* Pair *)
        | T_Pair t1 t2 =>
            match eval fuel' t1, eval fuel' t2 with
            | Some v1, Some v2 => Some (T_Pair v1 v2)
            | _, _ => None
            end
        (* Values*)
        | <[ fun x -> t ]> => Some <[ fun x -> t ]>
        | T_Nat n => Some (T_Nat n)
        | T_Bool b => Some (T_Bool b)
        | T_Var x => None
        end
    end.

  (** *** Interpreter Tests. *)

  (* TODO notations not working inside of [Some] constructor. *)

  Example example1 : eval 1000 <[ let f := (fun x -> x + 4) in f 4 ]> = Some (T_Nat 8).
  Proof. reflexivity. Qed.

  Definition test1 := <[ let foo := (fun x -> x + 7) in
                        let bar := (fun x -> x*2) in
                        (foo (bar 4)) ]>.

  Example example2 : eval 1000 test1 = Some (T_Nat 15).
  Proof. reflexivity. Qed.

  Definition test2 : term :=
    <[ let foo := fun n -> if n = 0 then 0 else n * n in foo 4]>.

  Example example3 : eval 1000 test2 = Some (T_Nat 16).
  Proof. reflexivity. Qed.

  Definition myfact : term :=
    <[ letrec fact := fun n -> if n = 0 then 1 else n * fact (n - 1) in fact 5 ]>.

  Example example4 : eval 1000 myfact = Some (T_Nat 120).
  Proof. reflexivity. Qed.

End MiniML.
