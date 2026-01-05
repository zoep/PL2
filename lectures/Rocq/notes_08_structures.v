From Stdlib Require Import Lists.List Init.Nat FunctionalExtensionality Lia.

Import ListNotations.

(** Basic Utilities *)

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
    fun x => g (f x).

Notation "g '∘' f" := (compose g f) (at level 40, left associativity).


(** * Functors *)

(**
  ============================================================
  * Functors
  ============================================================

  A functor is a type constructor F : Type -> Type that supports mapping a
  function over value contained in the functor, such that function composition
  and identity are preserved.

*)

Class Functor (F : Type -> Type) := {
    (** fmap applies a function inside the context F *)
    fmap : forall {A B : Type}, (A -> B) -> F A -> F B;

    (** Identity law: mapping id does nothing *)
    fmap_id : forall {A : Type} (x : F A), fmap id x = x;

    (** Composition law: mapping composed functions is the same as mapping one
        after the other *)
    fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : F A),
        fmap (g ∘ f) x = fmap g (fmap f x)

}.

(**
  ------------------------------------------------------------
  List functor
  ------------------------------------------------------------
*)

Program Instance List_Functor : Functor list :=
  { fmap := map; }.
(** Proof of identity law *)
Next Obligation.
- induction x as [| x xs' IH].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Defined.
(** Proof of identity law *)
Next Obligation.
- induction x as [| x xs' IH].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Defined.

(**
  ------------------------------------------------------------
  Option functor
  ------------------------------------------------------------
*)

(** fmap applies the function only if a value exists *)
Program Instance Option_Functor : Functor option := {
    fmap := fun {A B} (f : A -> B) (xo : option A) =>
              match xo with
              | None => None
              | Some x => Some (f x)
              end
  }.
(** Proof of identity law *)
Next Obligation.
- destruct x as [ x |].
  + reflexivity.
  + simpl. reflexivity.
Defined.
(** Proof of identity law *)
Next Obligation.
  destruct x as [ x |]; reflexivity.
Defined.


(** Notes about Rocq syntax:

The [Program] command before the instance declaration allows us to defines
without having to provide all the fields upfront. For the fields that are
missing Rocq then will generate proof obligations that need to be discharged
after the declaration of the instance.

This is particularly useful for type classes fields that are propositions (such
as the laws of functors, applicatives, monads, etc). In the above, each
obligation corresponds to a property that must be proven for the instance to be
valid. The [Next Obligation] command is used to provide proofs for these
obligations one by one.

*)

(**
  ============================================================
  * Applicative Functors
  ============================================================

  We saw that a functor allows the application of a *pure* function to a value
  wrapped inside the context of the functor.

  An applicative functor (or, for short, just applicative) extends a functor by
  allowing the function itself be wrapped inside the context of the functor as
  well.

  This enables us to compose computations that are inside the context of the
  applicative functor, which was not possible by a functor alone.

  Even though applicatives allow function application inside the context, they
  do not provide a way to sequence computations in the context of the functor
  when later computations depend on the results of earlier ones. (This is the
  role of monads, which we will see later.)

  An applicative functor is defined by the following operations:

    - [pure] lifts a pure value into the context of the applicative functor.
    - [ap] applies a wrapped function to a wrapped value.

  These operations must satisfy the following laws:

    - Identity law: applying the identity function inside the applicative is a
      no-op.
    - Composition law: applying composed functions is the same as applying one
      after the other.
    - Homomorphism law: applying a pure function to a pure value is the same as
      applying the function to the value and then lifting the result.
    - Interchange law: applying a wrapped function to a pure value is the same
      as applying a pure function that applies its argument to the pure value.

  The laws guarantee that pure computations introduce no effects, that grouping
  and reordering of applicative expressions does not change meaning, and that
  effects are combined in a predictable, structure-preserving way.
*)

Class Applicative (F : Type -> Type) := {
    (** Lift a pure computation into the context F *)
    pure : forall {A : Type}, A -> F A;
    (** Apply a wrapped function to a wrapped value *)
    ap : forall {A B : Type}, F (A -> B) -> F A -> F B;

    (** Identity law *)
    ap_identity : forall {A : Type} (x : F A), ap (pure id) x = x;

    (** Composition law *)
    ap_compose : forall {A B C : Type} (ff : F (B -> C)) (fg : F (A -> B)) (x : F A),
        ap ff (ap fg x) = ap (ap (ap (pure compose) ff) fg) x;

    (** Homomorphism law *)
    ap_homomorphism : forall {A B : Type} (f : A -> B) (x : A),
        ap (pure f) (pure x) = pure (f x);

    (** Interchange law *)
    ap_interchange : forall {A B : Type} (ff : F (A -> B)) (x : A),
        ap ff (pure x) = ap (pure (fun f => f x)) ff;
}.



Program Instance Applicative_Functor (F : Type -> Type) `{Applicative F} : Functor F := {
    fmap := fun {A B : Type} (f : A -> B) (x : F A) => ap (pure f) x
}.

Definition liftA2 {F A B C} `{Applicative F}
  (f : A -> B -> C)
  (fa : F A)
  (fb : F B) : F C :=
  ap (ap (pure f) fa) fb. 
    

(* Every applicative is also a functor, with fmap defined in terms of pure and
  ap. *)
Next Obligation.
- rewrite ap_identity. reflexivity.
Defined.
Next Obligation.
- rewrite ap_compose. rewrite !ap_homomorphism. reflexivity.
Defined.

(**
  ------------------------------------------------------------
  List applicative
  ------------------------------------------------------------

  The list applicative functor represents nondeterminism in the sense that [list
  A] represents a nondeterministic computation that can yield any value in the
  list.

  Applicative list works as follows:

  - [pure] lifts a deterministic value into a nondeterministic computation by
    wrapping it in a singleton list.

  - [ap] applies every function in the list of functions to every value in the
    list of values, yielding a list of all possible results.

  Note that the non-deterministic computation represented by lists does not have
  any notion of sequencing: the order in which functions are applied to values
  does not matter, and there is no way for a non-deterministic computation to
  depend on the result of another computation.

*)


Fixpoint list_app {A B : Type} (fs : list (A -> B)) (xs : list A) : list B :=
    match fs with
    | [] => []
    | f :: fs' => fmap f xs ++ list_app fs' xs
    end.

Lemma list_app_nil_r : forall {A B : Type} (fs : list (A -> B)),
    list_app fs [] = [].
Proof.
  induction fs as [| f fs' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma list_app_app : forall {A B : Type} (fs1 fs2 : list (A -> B)) (xs : list A),
    list_app (fs1 ++ fs2) xs = list_app fs1 xs ++ list_app fs2 xs.
Proof.
  induction fs1 as [| f fs1' IH]; intros fs2 xs.
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Program Instance List_Applicative : Applicative list := {
    pure := fun {A} (x : A) => [x];
    ap := fun {A B} => @list_app A B
}.
Next Obligation.
- induction x as [| x xs IH ].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Defined.
Next Obligation.
- rewrite app_nil_r.
   induction ff as [| f fs IHf].
    + simpl. reflexivity.
    + simpl. rewrite list_app_app.
      apply f_equal2; [ | assumption ].
      clear IHf.
      induction fg as [| g gs IHg].
        * simpl. reflexivity.
        * simpl.
          replace (map (f ∘ g) x) with (fmap (f ∘ g) x) by reflexivity.
          rewrite fmap_compose. rewrite map_app. rewrite IHg.
          reflexivity.
Defined.
Next Obligation.
- simpl. rewrite app_nil_r. induction ff as [| f fs' IH].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Defined.

(**
  ------------------------------------------------------------
  Option applicative
  ------------------------------------------------------------
*)

Program Instance Option_Applicative : Applicative option := {
    pure := fun {A} (x : A) => Some x;
    ap := fun {A B} (fo : option (A -> B)) (xo : option A) =>
        match fo with
        | Some f => fmap f xo
        | None => None
        end
}.
Next Obligation.
- destruct x as [ x | ]; reflexivity.
Defined.
Next Obligation.
- destruct ff as [ f |];
  destruct fg as [ g |]; destruct x as [ a |]; simpl; reflexivity.
Defined.


(**
  ============================================================
  * Monads
  ============================================================

  A monad is a type constructor [M : Type -> Type] that supports sequencing of
  computations inside the context of the monad. It extends the capabilities of
  applicative functors by allowing later computations to depend on the results
  of earlier ones.

  A monad is defined by the following operations:

  - [ret] lifts a pure value into the context of the monad.
  - [bind] sequences two computations in the context of the monad, where the
    second computation can depend on the result of the first.


  These operations must satisfy the following laws:
  - Left identity: lifting a value and then binding it to a function is the same
    as applying the function to the value.
  - Right identity: binding a computation to [ret] is a no-op.
  - Associativity: the order of nested binds does not matter.

*)

Class Monad (M : Type -> Type) := {
    ret : forall {A : Type}, A -> M A;

    bind : forall {A B : Type}, M A -> (A -> M B) -> M B;

    bind_ret : forall {A : Type} (x : M A),
        bind x ret = x;

    ret_bind : forall {A B : Type} (a : A) (f : A -> M B),
        bind (ret a) f = f a;

    bind_assoc : forall {A B C : Type} (x : M A) (f : A -> M B) (g : B -> M C),
        bind (bind x f) g = bind x (fun a => bind (f a) g)
    }.

(** We introduce some common notations for monadic operations.
    These notations make monadic code look like imperative code.
*)

Notation "e1 ;; e2" := (@bind _ _ _ _ e1 (fun _ => e2))
    (at level 61, right associativity).

Notation "x <- c1 ;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity).

Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
        (at level 61, pat pattern, c1 at next level, right associativity).

Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity).


(** Generic opperations over a monad *)
Definition liftM {M : Type -> Type} `{Monad M} {A B : Type} (f : A -> B) (ma : M A) : M B :=
    ma >>= (fun a => ret (f a)).

Definition liftM2 {M : Type -> Type} `{Monad M} {A B C : Type} (f : A -> B -> C) (ma : M A) (mb : M B) : M C :=
    ma >>= (fun a => mb >>= (fun b => ret (f a b))).

Fixpoint traverse {M : Type -> Type} `{Monad M} {A B : Type} (f : A -> M B) (xs : list A) : M (list B) :=
    match xs with
    | [] => ret []
    | x :: xs' =>
        b <- f x ;;
        bs <- traverse f xs' ;;
        ret (b :: bs)
    end.

Fixpoint sequence {M : Type -> Type} `{Monad M} {A : Type} (xs : list (M A)) : M (list A) :=
    match xs with
    | [] => ret []
    | x :: xs' =>
        a <- x ;;
        as' <- sequence xs' ;;
        ret (a :: as')
    end.

Require Import Program.

Program Fixpoint forM {M : Type -> Type} `{Monad M} (l h : nat) (f : nat -> M unit) {measure (h - l)} : M unit :=
  match h - l with
    | 0 => f l
    | _ =>
      f l ;;
      forM (l + 1) h f
    end.
Next Obligation. lia. Defined.

(** Monads are also applicative functors: *)

Program Instance Applicative_Monad (M : Type -> Type) `{Monad M} : Applicative M := {
    pure := fun {A} x => ret x;
    ap := fun {A B} (mf : M (A -> B)) (mx : M A) =>
        bind mf (fun f => bind mx (fun x => ret (f x)))
}.
Next Obligation.
- rewrite ret_bind. rewrite bind_ret. reflexivity.
Defined.
Next Obligation.
- rewrite ret_bind. rewrite !bind_assoc. f_equal.
  extensionality a. rewrite ret_bind. rewrite !bind_assoc. f_equal.
  extensionality b. rewrite ret_bind. rewrite !bind_assoc. f_equal.
  extensionality y. rewrite ret_bind. reflexivity.
Defined.
Next Obligation.
- rewrite !ret_bind. reflexivity.
Defined.
Next Obligation.
  rewrite !ret_bind. f_equal.
  extensionality f. rewrite ret_bind. reflexivity.
Defined.


(**
  ------------------------------------------------------------
  List Monad
  ------------------------------------------------------------
*)

Fixpoint list_bind {A B : Type} (xs : list A) (f : A -> list B) : list B :=
    match xs with
    | [] => []
    | x :: xs' => f x ++ list_bind xs' f
    end.

Lemma list_bind_app : forall {A B : Type} (xs1 xs2 : list A) (f : A -> list B),
    list_bind (xs1 ++ xs2) f = list_bind xs1 f ++ list_bind xs2 f.
Proof.
  induction xs1 as [| x xs1' IH]; intros xs2 f.
  - reflexivity.
  - simpl. rewrite IH, app_assoc. reflexivity.
Qed.

Program Instance List_Monad : Monad list := {
    bind := fun {A B} => @list_bind A B;
    ret := fun {A} (x : A) => [x];
}.
Next Obligation.
- induction x as [| x xs' IH].
  + reflexivity.
  + simpl. rewrite IH. reflexivity.
Defined.
Next Obligation.
- rewrite app_nil_r. reflexivity.
Defined.
Next Obligation.
- induction x as [| x xs' IH]; simpl.
  + reflexivity.
  + rewrite !list_bind_app, IH. reflexivity.
Defined.

Program Instance Option_Monad : Monad option := {
    ret := fun {A : Type} (x : A) => Some x;
    bind := fun {A B} (xo : option A) (f : A -> option B) =>
        match xo with
        | None => None
        | Some x => f x
        end
}.
Next Obligation.
- destruct x as [ x | ]; reflexivity.
Defined.
Next Obligation.
- destruct x as [ x | ]; reflexivity.
Defined.

(**
  ------------------------------------------------------------
  State Monad
  ------------------------------------------------------------
*)

Definition State (S A : Type) : Type := S -> (A * S).


Program Instance state_Monad (S : Type) : Monad (fun A => S -> (A * S)) := {
    ret := fun {A : Type} (a : A) s => (a, s);

    
    bind := fun {A B} (sa : S -> (A * S)) (f : A -> S -> (B * S)) =>
        fun s0 =>
            let (a, s1) := sa s0 in
            f a s1
}.
Next Obligation.
- extensionality s0. destruct (x s0). reflexivity.
Defined.
Next Obligation.
- extensionality s0. simpl. destruct (x s0). reflexivity.
Defined.


Definition get {S : Type} : State S S :=
    fun s => (s, s).

Definition put {S : Type} (s : S) : State S unit :=
    fun _ => (tt, s).


(**
  ------------------------------------------------------------
  Reader Monad
  ------------------------------------------------------------
*)

(** A reader monad represents computations that read from a shared
    environment of type R. It allows functions to access the environment without
    explicitly passing it around. *)

Definition Reader (R A : Type) : Type := R -> A.

Program Instance reader_Monad (R : Type) : Monad (fun A => R -> A) := {
    ret := fun {A : Type} (a : A) _ => a;
    bind := fun {A B} (ra : R -> A) (f : A -> R -> B) =>
        fun r => f (ra r) r
}.

Definition local {R A : Type} (f : R -> R) (ra : R -> A) : R -> A :=
    fun r => ra (f r).

Definition Writer (W A : Type) : Type := A * W.

(**
  ------------------------------------------------------------
  A Monoidal Structure
  ------------------------------------------------------------
*)

(* Before introducing the writer monad, we define a Monoid class that represents
   types with an associative binary operation and an identity element with
   respect to this operation. *)

Class Monoid (M : Type) := {
    empty : M;
    op : M -> M -> M;

    left_id : forall (x : M), op empty x = x;
    right_id : forall (x : M), op x empty = x;
    assoc : forall (x y z : M), op x (op y z) = op (op x y) z
}.


(** Monoid Instances *)

Program Instance list_app_Monoid (A : Type) : Monoid (list A) := {
    empty := [];
    op := @app A
}.
Next Obligation.
- apply app_nil_r.
Defined.
Next Obligation.
- apply app_assoc.
Defined.

Program Instance Nat_Add_Monoid : Monoid nat := {
    empty := 0;
    op := Nat.add
}.
Next Obligation.
- lia.
Defined.

Program Instance Nat_Mul_Monoid : Monoid nat := {
    empty := 1;
    op := Nat.mul
}.
Next Obligation.
- lia.
Defined.
Next Obligation.
- lia.
Defined.


(**
  ------------------------------------------------------------
  Writer Monad
  ------------------------------------------------------------
*)

(* A writer monad allows computations to produce a value along with a
   supplementary output (or "log") of type W. The log values are combined using
   a monoidal operation.

   Such monads are useful for computations that need to accumulate auxiliary
   information, such as logging, without explicitly passing the log around. *)

Program Instance writer_Monad (W : Type) `{Monoid W} : Monad (Writer W) := {
    ret := fun {A : Type} (a : A) => (a, empty);
    bind := fun {A B} (wa : A * W) (f : A -> B * W) =>
        let (a, w1) := wa in
        let (b, w2) := f a in
        (b, op w1 w2)
}.
Next Obligation.
- destruct x as [ a w ]. rewrite right_id. reflexivity.
Defined.
Next Obligation.
- destruct (f a) as [ b w1 ]. simpl.
  rewrite left_id. reflexivity.
Defined.
Next Obligation.
- destruct x as [ a w1 ]. destruct (f a) as [ b w2 ].
  destruct (g b) as [ c w3 ]. simpl.
  rewrite assoc. reflexivity.
Defined.

(**
  ------------------------------------------------------------
  Monad Examples
  ------------------------------------------------------------
*)

(** Eval Example
    ------------

    An expression language with addition, multiplication, division, and
    subtraction, where division by zero is handled gracefully using the option
    monad.

*)

Inductive expr :=
| Const : nat -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr
| Div : expr -> expr -> expr
| Sub: expr -> expr -> expr.


Fixpoint eval (e : expr) : option nat :=
  match e with
    | Const n => Some n
    | Add e1 e2 =>
        v1 <- eval e1;;
        v2 <- eval e2;;
        ret (v1 + v2)
    | Mul e1 e2 =>
        v1 <- eval e1;;
        v2 <- eval e2;;
        ret (v1 * v2)
    | Div e1 e2 =>
        v1 <- eval e1;;
        v2 <- eval e2;;
        match v2 with
        | 0 => None
        | _ => ret (v1 / v2)
        end
    | Sub e1 e2 =>
        v1 <- eval e1;;
        v2 <- eval e2;;
        ret (v1 - v2)
    end.

(* State Example
   -------------

    A simple state monad that maintains a counter.

*)

Definition tick : State nat unit :=
  (* bind get (fun n =>  put (n + 1))  *)
   n <- get;;
   put (n + 1).

Definition tick_twice : State nat unit :=
    tick;;
    tick.

Definition get_and_tick : State nat nat :=
    n <- get;;
    tick;;
    ret n.

Eval compute in (tick_twice 0).
Eval compute in (get_and_tick 5).

(* Stack Calculator
   -----------------

    A stack-based calculator implemented using the state monad.

*)

(* A stack-based calculator that maintains a stack of numbers *)
Definition Stack := list nat.

Definition StackCalc := State Stack.


Definition push (n : nat) : State Stack unit :=
  stack <- get ;;
  put (n::stack).
 

Definition evalOp (f : nat -> nat -> nat) : State Stack unit :=
  stack <- get ;;
  match stack with
    | x1 :: x2 :: stack' =>
        put (f x2 x1 :: stack')
    | _ => pure tt
  end.
            

Fixpoint evalStack (e : expr) : State Stack () :=
  match e with
  | Const n => push n      
  | Add e1 e2 =>
      evalStack e1 ;;
      evalStack e2 ;;
      evalOp (fun x1 x2 => x1 + x2)      
  | Mul e1 e2 =>
      evalStack e1 ;;
      evalStack e2 ;;
      evalOp (fun x1 x2 => x1 * x2)      
  | Div e1 e2 =>
      evalStack e1 ;;
      evalStack e2 ;;
      evalOp (fun x1 x2 => div x1 x2)      
  | Sub e1 e2 =>
      evalStack e1 ;;
      evalStack e2 ;;
      evalOp (fun x1 x2 => x1 - x2)      
  end.
    

Definition e1 :=
  Mul (Const 6) (Add (Const 3) (Const 4)).


Compute (snd (evalStack e1 [])).




















(* Push a value onto the stack *)
Definition push (n : nat) : StackCalc unit :=
      fun s => (tt, n :: s).

(* Pop a value from the stack *)
Definition pop : StackCalc (option nat) :=
  fun s => match s with
           | [] => (None, [])
           | x :: xs => (Some x, xs)
           end.

(* Peek at the top of the stack without removing it *)
Definition peek : StackCalc (option nat) :=
  fun s => match s with
           | [] => (None, [])
           | x :: xs => (Some x, s)
           end.

(* Binary operations on the stack *)
Definition binop (op : nat -> nat -> nat) : StackCalc unit :=
  x <- pop;;
  y <- pop;;
  match x, y with
  | Some x', Some y' => push (op y' x')
  | _, _ => ret tt
  end.

Definition stack_add : StackCalc unit := binop Nat.add.

Definition stack_mul : StackCalc unit := binop Nat.mul.

Definition stack_sub : StackCalc unit := binop Nat.sub.


(* Example: Evaluate (3 + 5) * 2 using stack operations *)
Definition example_calc : StackCalc (option nat) :=
  push 3;;
  push 5;;
  stack_add;;
  push 2;;
  stack_mul;;
  pop.

Eval compute in (example_calc []).

(* We can evaluate an expression using the stack calculator *)

Fixpoint eval_stack_calc (e : expr): StackCalc unit :=
    match e with
    | Const n => push n
    | Add e1 e2 =>
        eval_stack_calc e1;;
        eval_stack_calc e2;;
        stack_add
    | Mul e1 e2 =>
        eval_stack_calc e1;;
        eval_stack_calc e2;;
        stack_mul
    | Sub e1 e2 =>
        eval_stack_calc e1;;
        eval_stack_calc e2;;
        stack_sub
    | Div e1 e2 =>
        eval_stack_calc e1;;
        eval_stack_calc e2;;
        d2 <- peek;;
        match d2 with
        | None => ret tt
        | Some d2 =>
          if d2 =? 0 then ret tt
          else binop Nat.div
        end
    end.


(* Stateful Fibonacci
   -----------------

    A stateful computation that calculates Fibonacci numbers.

*)

Definition fib_state (n : nat) : State (nat*nat) unit :=
  forM 0 (n - 1) (fun _ =>
    '(a, b) <- get;;
    put (b, a + b)).


Definition compute_fib (n : nat) := fst (snd (fib_state n (0, 1))).

Eval compute in (compute_fib 8).
