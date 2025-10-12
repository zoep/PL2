From Stdlib Require Import Strings.String Init.Nat Arith.PeanoNat Lia.

(** * Introduction to Operational Semantics: The Language Imp. *)

(** In this section we will use Rocq to study the semantics of simple
    languages, prove properties about them and use them to reason
    about the behavior of programs. We will start with a simple
    language of arithmetic expressions and we will build up to a small
    imperative language, that can be seen as a small core subset of
    imperative languages like C or Java.

    In this section, we will also take a deeper dive into Rocq's
    tactics, and how we can use Rocq's tactic language, Ltac to
    automate our proofs, handle multiple similar goals at once, and
    make our proof scripts smaller. *)


(** ** Arithmetic Expressions *)

(** The abstract syntax tree (AST) of arithmetic expressions is given
    by the following definition. *)
Inductive exp : Type :=
| Num : nat -> exp
| Plus : exp -> exp -> exp
| Minus : exp -> exp -> exp
| Mult : exp -> exp -> exp.

(** We can use this abstract syntax to construct arithmetic expressions. *)
Definition answer : exp := Mult (Num 6) (Plus (Num 4) (Num 3)).

(** So far, we haven't attached any meaning to arithmetic expressions.
   There are a few ways to do so.
    We will write:
    - an interpreter for arithmetic expressions
    - a big-step semantics
    - a small-step semantics
 *)

(** *** Arithmetic Expressions: Interpreter *)

(** Perhaps, the most natural thing to do in order to give meaning to arithmetic
    expressions is to write an interpreter. The interpreter is a recursive
    function that evaluates an arithmetic expression to the number it computes
    in a bottom-up fashion. *)
Fixpoint interp (e : exp) : nat :=
  match e with
  | Num n => n
  | Plus e1 e2 => (interp e1) + (interp e2)
  | Minus e1 e2 => (interp e1) - (interp e2)
  | Mult e1 e2 => (interp e1) * (interp e2)
  end.

(** We can now use the interpreter to evaluate an arithmetic expression. *)
Compute (interp answer).

(** *** Arithmetic Expressions: Big-step Semantics *)

(** Another thing we can do is to define a big-step semantics for
    [exp]. A big-step semantics is a relation that defines what is the
    result of evaluating an expression. [eval_exp e n] means "e
    evaluates to n") *)

Inductive eval_exp : exp -> nat -> Prop :=
| eval_Num :
  forall n, eval_exp (Num n) n
| eval_Plus :
  forall e1 e2 n1 n2,
    eval_exp e1 n1 ->
    eval_exp e2 n2  ->
    eval_exp (Plus e1 e2) (n1 + n2)
| eval_Minus :
  forall e1 n1 e2 n2,
    eval_exp e1 n1 ->
    eval_exp e2 n2 ->
    eval_exp (Minus e1 e2) (n1 - n2)
| eval_Mult :
  forall e1 n1 e2 n2,
    eval_exp e1 n1 ->
    eval_exp e2 n2 ->
    eval_exp (Mult e1 e2) (n1 * n2).

(** It closely resembles the structure of an interpreter. The difference is that
    the interpreter can be used to evaluate an expression, whereas [eval_exp] is
    a logical proposition, we can only construct proofs that an expression
    evaluates to a number, but we cannot compute with it.

    In this case, choosing the relational vs. the computational definition is
    mostly a matter of convenience. However, in general, relations give us more
    freedom: they can be partial or non-deterministic. On the other hand,
    functions can be used for computation.  *)

(** Let's use some notation for [eval_exp] to make our definitions
    prettier. *)
Notation "e '==>' n" := (eval_exp e n) (at level 40).

(** We can construct a proof that [answer] evaluates to [42], by
    applying the suitable constructor for each step. *)
Example eval_example:
  answer ==> 42.
Proof.
  (* The following to tactics fails, as Rocq cannot unify 42 with [n1 * n2].
     It cannot find the factors by itself. *)
  unfold answer.

  Fail econstructor.
  Fail apply eval_Mult.

  (* But once we provide the factors the application succeeds. *)
  apply eval_Mult with (n1 := 6) (n2 := 7).

  - apply eval_Num.

  - apply eval_Plus with (n1 := 4) (n2 := 3); apply eval_Num.
    (* Recall that we can sequence tactics with [;]. In the tactic
       [tactic1; tactic2], [tactic1] will be applied to the goal and
       [tactic2] will be applied to _all_ of the generated
       subgoals. *)
Qed.

(** We can also prove that the interpreter is equivalent to the
    big-step semantics. *)

Theorem interp_eval_exp :
  forall e n,
    interp e = n ->
    eval_exp e n.
Proof.
  (* In this proof we sequence tactics to handle four cases at once,
     since their proofs are very similar *)
  intros e; induction e; intros n' Hi;
    simpl in *; subst; constructor; auto.
Qed.

(** *** Defining Our Own Tactics *)

(** Often it is useful to define shorthand for tactics that we use
    often by combining several tactics into one. We can do this with
    the [Ltac] command. [Ltac] provides powerful facilities to inspect
    the proof context and goal and automate proofs. We wil see only a 
    few of its capabilities.

    We will define a tactic that inverts a hypothesis (that should be
    a proof of an inductive proposition), substitutes the generated
    equations, and clears the initial hypothesis. These are steps that
    are used very often together and will come in handy when writing
    proofs.

    Recall that inverting a proof of an inductive proposition
    considers all cases by which a proof of the proposition can be
    derived. For each of these cases, Rocq will generate equalities 
    for the arguments of the relation that enforce that they unify 
    with the arguments of the relation in the conclusion of the 
    case we are considering. *)


Ltac inv H :=
  inversion H; subst; clear H.

(** We will prove that the interpreter is complete w.r.t. the evaluation
    relation, meaning that whenever [e] evaluates to [n] according to the
    relation, the same result is computed by the interpreter. *)
Theorem eval_exp_interp_long_proof :
  forall e n,
    eval_exp e n ->
    interp e = n.
Proof.
  intros e;
      (* we proceed by induction on the expression [e] *)
      induction e as [ | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 ];
    intros n' Heval.
  - (* e = Num n *) 
    simpl. inv Heval. 
    reflexivity.
  - (* e = Plus n1 n2 *)
    inv Heval; simpl.

    (* Here, we want to rewrite with the conclusion of IHe1.  We can
       use the [rewrite] tactic with all logical statements whose
       conclusion is an equality. If the statement has premises, Rocq
       will generate new goals asking us to prove them. If the
       statement has quantified variables, then Rocq will try to unify
       them when matching the left hand side of the equality with a
       subterm of the goal. If it cannot unify them all, it will fail.
       If we can use [erewrite] then Rocq will generate evars for the
       unknown variable that must be unified in the next steps. *)
    erewrite IHe1. (* generated an extra goal: [e1 ==> ?n] *)

    erewrite IHe2.  (* generated an extra goal: [e2 ==> ?n0] *)

    reflexivity. (* unifies ?n with  n1 and ?n0 with n2 *)

    assumption.

    assumption.

  - (* e = Minus n1 n2 *)
    inv Heval; simpl.
    erewrite IHe1. erewrite IHe2.
    reflexivity.
    assumption.
    assumption.

  - (* e = Mult n1 n2 *)
    inv Heval; simpl.
    erewrite IHe1. erewrite IHe2.
    reflexivity.
    assumption.
    assumption.
Qed.


(** The above proof is very repetitive. The three cases are similar to each
    other. We can use [tacticals] which are tactics that operate on other
    tactics to make the proof script smaller *)

(** *** Tacticals *)

(** Tacticals are "tactic operators" that take other tactics as arguments. They
    are a powerful facility to automate our proofs. *)

(** **** Tactic Sequencing *)
(** We have already seen the tactic sequencing operator [;].  In its
    simplest form [tactic1; tactic2] will apply [tactic1] and then it
    will apply [tactic2] to all generated goals. *)

(** The sequence operator has the general form:

    [tactic ; [tactic_1 | tactic_2 | ... | tactic_n ].]

    In this case, [tactic_1] will be applied to the first subgoal,
    [tactic_2] will be applied to the second subgoal and so on.  Note,
    that the number of tactics in the list following [;] must be equal
    to the number of generated subgoals otherwise the tactic will fail. *)

(** **** The [try] Tactical  *)

(** The tactic [try tactic] will apply the tactic [tactic] but if [tactic]
    fails then [try tactic] will successfully terminate doing nothing at all. *)

(** **** The [repeat] Tactical  *)
(** The tactic [repeat tactic] will repeatedly apply the tactic
    [tactic] until it fails (or it doesn't make any progress). *)

Lemma repeat_example (x : nat) :
  x = x + 0 /\ x = x + 0 /\ x = x + 0 /\ x = x + 0 /\ x = x + 0 /\ x = x + 0.
Proof.
  repeat split; rewrite <- plus_n_O; reflexivity.
Qed.


Lemma repeat_try_example (x : nat) :
  x = x + 0 /\ x = x * 1 /\ x = x + 0 /\ x = x * 1 /\ x = x + 0 /\ x = x + 0.
Proof.
  repeat split;
    try rewrite <- plus_n_O;
    try rewrite PeanoNat.Nat.mul_1_r;
    reflexivity.
Qed.

(** **** The [now] Tactical  *)

(** The tactic [now tactic] will apply tactic [tactic] but it will
    succeed only if it solves the goal, otherwise it will fail.

    This can be useful in combination with try.

    If we want to apply a tactic to a number of generated subgoals but
    only if this tactic succeeds then we can use [try now tactic]. *)

(** **** The [||] Tactical  *)

(** The tactic [tactic1 || tactic2] will try to apply the tactic on
    the left. If this fails it will apply the tactic on the right.  It
    will fail if all tactics fail. *)


Lemma or_example (x : nat) :
  x = x + 0 /\ x = x * 1 /\ x = x + 0 /\ x = x * 1 /\ x = x + 0 /\ x = x * 1.
Proof.
  repeat split; 
    (rewrite <- plus_n_O || rewrite Nat.mul_1_r); reflexivity.
Qed.

(** **** The [first] Tactical  *)

(** The tactic [first [tactic1 | ... | tacticn]] will apply the first
    tactic from the list that doesn't fail. *)


(** With the use of tacticals we can make the proof
    [eval_exp_interp_long_proof] much shorter. *)
Theorem eval_exp_interp :
  forall e n,
    eval_exp e n ->
    interp e = n.
Proof.
  intros e;
    induction e as [ | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 ];
    intros n' Heval; inv Heval; simpl;
    try erewrite IHe1; try erewrite IHe1; eauto.
Qed.

(** *** Arithmetic Expressions: Small-step semantics *)

(** We can also define the evaluation of arithmetic expressions as a
    sequence of transitions, where each transition performs a single
    computation step. The relation [step_exp e e'] represents the
    concept of a single _reduction_ step in the computation. It
    defines how an expression [e] reduces to another expression [e']
    by performing one step of computation.

    The expression that is reduced, which is called a _redex_, is
    always of the form [n1 + n1], [n1 * n2], [n1 - n2] where [n1],
    [n2] are numbers (rules [step_Plus], [step_Minus],
    [step_Mult]). The redex can be at an arbitrary depth inside the
    expression (rules [step_Plus_l], [step_Plus_r], [step_Minus_l],
    [step_Minus_r], [step_Mult_l], [step_Mult_r].  *)

Inductive step_exp : exp -> exp -> Prop :=
| step_Plus :
  forall n1 n2,
    step_exp (Plus (Num n1) (Num n2)) (Num (n1 + n2))
| step_Plus_l :
  forall e1 e1' e2,
    step_exp e1 e1' ->
    step_exp (Plus e1 e2) (Plus e1' e2)
| step_Plus_r :
  forall n1 e2 e2',
    step_exp e2 e2' ->
    step_exp (Plus (Num n1) e2) (Plus (Num n1) e2')
| step_Minus :
  forall n1 n2,
    step_exp (Minus (Num n1) (Num n2)) (Num (n1 - n2))
| step_Minus_l :
  forall e1 e1' e2,
    step_exp e1 e1' ->
    step_exp (Minus e1 e2) (Minus e1' e2)
| step_Minus_r :
  forall n1 e2 e2',
    step_exp e2 e2' ->
    step_exp (Minus (Num n1) e2) (Minus (Num n1) e2')
| step_Mult :
  forall n1 n2,
    step_exp (Mult (Num n1) (Num n2)) (Num (n1 * n2))
| step_Mult_l :
  forall e1 e1' e2,
    step_exp e1 e1' ->
    step_exp (Mult e1 e2) (Mult e1' e2)
| step_Mult_r :
  forall n1 e2 e2',
    step_exp e2 e2' ->
    step_exp (Mult (Num n1) e2) (Mult (Num n1) e2').

(** Again, we define a pretty notation. *)
Notation "e '-->' e'" := (step_exp e e') (at level 39).

(** We want a way to compose multiple of these steps together.  That
    is, a relation [e -->* e'] that says that [e] takes multiple steps
    of computation to [e']. We will do this by defining the reflexive
    transitive closure of the relation [-->]. We will first do this
    generically for any binary relation over a type [A]. *)

(** **** Reflexive Transitive Closure of a Relation *)

Definition relation (A : Type) : Type := A -> A -> Prop.

(** The reflexive transitive closure of relation [R] is the smallest relation that
    - contains [R]
    - is reflexive
    - is transitive

   We can define this inductively for any relation [R] *)

Inductive multi {A : Type} (R : relation A) : relation A :=
| multi_refl :  (* a reflexive step *)
  forall (x : A), multi R x x
| multi_step :
  forall (x y z : A),
    R x y -> (* an [R] step followed by any number of steps *)
    multi R y z ->
    multi R x z.

(** We can prove that [multi R] is indeed transitive. To do this we do
    induction on the derivation of [R]. Informally:

    If [multi R x y] (H1) and [multi R y z] (H2) then [multi R x z].
    We do induction on the derivation of (H1).

    - Base case: If (H1) is derived by a [multi_refl] step then x = y
      and we derive [multi R x z] from (H2).

    - Inductive case: If (H1) is derived by a [multi_step] step then
      we know there exists some x' such that [R x x'] (H3) and [multi R x'
      z].

      We have [multi R x' z] and [multi R y z] which by the inductive
      hypothesis gives us [multi R x' z] (H5).

      By (H3) and (H5) and rule [multi_step] we get [multi R x z]. *)

Lemma multi_transitive :
  forall A R (x y z : A),
    multi R x y ->
    multi R y z ->
    multi R x z.
Proof.
  intros A R x y z H1. revert z.
  induction H1; intros z' H2.
  - assumption.
  - eapply multi_step.
    + eassumption.
    + apply IHmulti. assumption.
Qed.


(** We now define the reflexive transitive closure of [-->] and we
    give it some nice notation. *)
Definition multi_step_exp := multi step_exp.


Notation "e '-->*' e'" := (multi step_exp e e') (at level 39).

(** We can now prove that [answer] evaluates to [42] after some steps. *)
Lemma small_step_example:
  answer -->* (Num 42).
Proof.
  unfold answer.
  eapply multi_step.
  - (* Mult (Num 6) (Plus (Num 4) (Num 3)) --> Mult (Num 6) (Num 7) *)
    apply step_Mult_r.
    apply step_Plus.
  - (* Mult (Num 6) (Num 7) -->* Num 42 *)
    eapply multi_step; [ | now apply multi_refl ].
    apply step_Mult.
Qed.


Lemma small_step_stop (e : exp) :
  ~ (exists e', e --> e') ->
  (exists n, e = Num n).
Proof.
  induction e; intros Hnot.
  - eauto. (* or, more explicitly: [exists n. reflexivity. eauto.] *)

  - (* We have the hypothesis [~ (exists e' : exp, Plus e1 e2 --> e')]
       which is a contradiction. In this simple language, any plus/minus/mult
       expression can always be reduced.

       We will show exactly this fact to conclude the goal. *)

    (* From the hypothesis [Hnot] we can derive the following fact *)
    assert (Hnot1:  ~ (exists e1' : exp, e1 --> e1')). {
      intros Hnot1. apply Hnot.
      destruct Hnot1 as [e1' Heval1].
      eexists. eapply step_Plus_l; eauto.
     }

     apply IHe1 in Hnot1. destruct Hnot1 as [n1 Heq]. subst.
     (* We now derived from the [IHe1] that [e1] must be a [Num]
        expression *)

    (* From the hypothesis [Hnot] and the fact that [e1] is [Num]
       we can derive the following *)
     assert (Hnot2:  ~ (exists e2' : exp, e2 --> e2')). {
      intros Hnot2. apply Hnot.
      destruct Hnot2 as [e2' Heval2].
      eexists. eapply step_Plus_r; eauto.
     }

     apply IHe2 in Hnot2. destruct Hnot2 as [n2 Heq]. subst.
     (* We now derived from the [IHe2] that [e2] must be a [Num]
        expression *)

     (* Now we can prove that [Hnot] is a contradiction. *)

     exfalso. apply Hnot.
     eexists. eapply step_Plus.

  - (* The rest of the cases are largely similar. We will use them to
       practice with [destruct]. *)

    (* If the result of any logical truth is an existential, we can
       directly use destruct on it. If it has premises, Rocq will ask
       us to prove them. If it has universal quantifiers we must do it
       with [edestruct]. *)

    destruct IHe1 as [n1 Heq1].

    { (* We have to show the premise here. The optional use of curly
         braces helps us to separate this proof from the rest. It is
         similar to bullets. *)
      intros Hnot1. apply Hnot.
      destruct Hnot1 as [e1' Heval1].
      eexists. eapply step_Minus_l; eauto. }

    subst. destruct IHe2 as [b2 Heq2].

    { intros Hnot2. apply Hnot.
      destruct Hnot2 as [e2' Heval2].
      eexists. eapply step_Minus_r; eauto. }

    subst. exfalso. apply Hnot.
    eexists; apply step_Minus.

  - (* This case is similar *)
    destruct IHe1 as [n1 Heq1].
    { intros Hnot1. apply Hnot.
      destruct Hnot1 as [e1' Heval1].
      eexists. eapply step_Mult_l; eauto. }

    subst. destruct IHe2 as [b2 Heq2].

    { intros Hnot2. apply Hnot.
      destruct Hnot2 as [e2' Heval2].
      eexists. eapply step_Mult_r; eauto. }

    subst. exfalso. apply Hnot.
    eexists; apply step_Mult.
Qed.

(** The above lemma tells us that if [e] cannot be evaluated further
    then it must be a [Num] expression. This is called a _value_ which
    is the final result of the evaluation.

    In this simple language every expression evaluates to a value. The
    following are equivalent:

    - The interpreter is total
    - [forall e, exists n, e ==> n]
    - [forall e, exists n, e -->* (Num n)]

    Can you think of cases where this is not true for some language?
    What are these? *)

(** *** Case Study: Equivalence of the Small-step and Big-step Semantics *)

(** In this section, we will establish the equivalence between
    small-step semantics and big-step semantics. While the proof is
    somewhat technical, it serves as an exercise in understanding how
    to rigorously state and prove properties about programming
    languages.  *)

(** ****  Big-step -> Small-step *)

(** We start by proving a series of useful lemmas. The following
    lemmas state that the reductions in the left or right operands,
    then these reductions can also be performed under the operand.

    In other words, if [e1] can transition to [e1'] through multiple
    small steps, then the entire [Plus e1 e2] expression can also
    transition to [Plus e1' e2]. (lemma [multi_Plus_compose_l])

    For the right operand we can say the same, but only if the left
    operand is already a value. Recall that according to our
    small-step semantics we can perform reductions on the right
    operand only if the left is evaluated. (lemma
    [multi_Plus_compose_r])

    To show these two lemmas, we proceed by induction on the derivation
    of the multi-step relation.

    Lastly, we can combine the above lemmas together and prove an easy
    corollary: if [e1] can transition to [Num n1] through multiple
    small steps, and [e2] can transition to [e2'] then the entire
    [Plus e1 e2] expression can also transition to [Plus (Num n1)
    e2']. (lemma [multi_Plus_compose])

    We state similar lemmas for all of the arithmetic operators. *)


Lemma multi_Plus_compose_l :
  forall e1 e2 e1',
    e1 -->* e1' ->
    Plus e1 e2 -->* Plus e1' e2.
Proof.
  intros e1 e2 e1' Hs1. induction Hs1.
  - eapply multi_refl.
  - eapply multi_step.
    + eapply step_Plus_l; eauto.
    + assumption.
Qed.

Lemma multi_Plus_compose_r :
  forall n1 e2 e2',
    e2 -->* e2' ->
    Plus (Num n1) e2 -->* Plus (Num n1) e2'.
Proof.
  intros e1 e2 e1' Hs1. induction Hs1.
  - eapply multi_refl.
  - eapply multi_step.
    + eapply step_Plus_r; eauto.
    + assumption.
Qed.

Corollary multi_Plus_compose :
  forall e1 e2 n1 e2',
    e1 -->* (Num n1) ->
    e2 -->* e2' ->
    Plus e1 e2 -->* Plus (Num n1) e2'.
Proof.
  intros e1 e2 n1 e2' Hs1 Hs2.
  eapply multi_transitive.
  - apply multi_Plus_compose_l; eauto.
  - apply multi_Plus_compose_r; eauto.
Qed.

Lemma multi_Mult_compose_l :
  forall e1 e2 e1',
    e1 -->* e1' ->
    Mult e1 e2 -->* Mult e1' e2.
Proof.
  intros e1 e2 e1' Hs1. induction Hs1.
  - eapply multi_refl.
  - eapply multi_step.
    + eapply step_Mult_l; eauto.
    + assumption.
Qed.

Lemma multi_Mult_compose_r :
  forall n1 e2 e2',
    e2 -->* e2' ->
    Mult (Num n1) e2 -->* Mult (Num n1) e2'.
Proof.
  intros e1 e2 e1' Hs1. induction Hs1.
  - eapply multi_refl.
  - eapply multi_step.
    + eapply step_Mult_r; eauto.
    + assumption.
Qed.

Corollary multi_Minus_compose_l :
  forall e1 e2 e1',
    e1 -->* e1' ->
    Minus e1 e2 -->* Minus e1' e2.
Proof.
  intros e1 e2 e1' Hs1. induction Hs1.
  - eapply multi_refl.
  - eapply multi_step.
    + eapply step_Minus_l; eauto.
    + assumption.
Qed.

Lemma multi_Mult_compose :
  forall e1 e2 n1 e2',
    e1 -->* (Num n1) ->
    e2 -->* e2' ->
    Mult e1 e2 -->* Mult (Num n1) e2'.
Proof.
  intros e1 e2 n1 e2' Hs1 Hs2.
  eapply multi_transitive.
  - apply multi_Mult_compose_l; eauto.
  - apply multi_Mult_compose_r; eauto.
Qed.

Lemma multi_Minus_compose_r :
  forall n1 e2 e2',
    e2 -->* e2' ->
    Minus (Num n1) e2 -->* Minus (Num n1) e2'.
Proof.
  intros e1 e2 e1' Hs1. induction Hs1.
  - eapply multi_refl.
  - eapply multi_step.
    + eapply step_Minus_r; eauto.
    + assumption.
Qed.

Corollary multi_Minus_compose :
  forall e1 e2 n1 e2',
    e1 -->* (Num n1) ->
    e2 -->* e2' ->
    Minus e1 e2 -->* Minus (Num n1) e2'.
Proof.
  intros e1 e2 n1 e2' Hs1 Hs2.
  eapply multi_transitive.
  - apply multi_Minus_compose_l; eauto.
  - apply multi_Minus_compose_r; eauto.
Qed.

(** By using the above lemmas, we can now prove the main theorem. We
    proceed by induction on the evaluation relation. Here we could
    have also used induction on the term [e]. *)

Theorem eval_exp_step_exp :
  forall (e : exp) (n : nat),
    e ==> n -> e -->* (Num n).
Proof.
  intros e n Heval. induction Heval.
  - constructor.
  - (* Plus *)
    eapply multi_transitive.
    + apply multi_Plus_compose; eauto.
    + eapply multi_step; [ apply step_Plus | apply multi_refl ].

  - (* Minus *)
    eapply multi_transitive.
    + apply multi_Minus_compose; eauto.
    + eapply multi_step; [ apply step_Minus | apply multi_refl ].

  - (* Mult *)
    eapply multi_transitive.
    + apply multi_Mult_compose; eauto.
    + eapply multi_step; [ apply step_Mult | apply multi_refl ].
Qed.


(** The above proof is verbose and repetitive. We can write a shorter
    proof using the tacticals we learn. Warning: shorter proofs may
    not always be good for readability. *)
Theorem eval_exp_step_exp' :
  forall (e : exp) (n : nat),
    e ==> n -> e -->* (Num n).
Proof.
  intros e n Heval.
  induction Heval ; (try now constructor); (* solves the first
                                              goal. The use [now] is
                                              crucial since it
                                              prevents the tactic from
                                              being applied if it
                                              doesn't solve the
                                              goal. *)
    (eapply multi_transitive;
     [ (apply multi_Plus_compose || apply multi_Minus_compose || apply multi_Mult_compose); eauto
     |  eapply multi_step; [ (apply step_Plus || apply step_Minus || apply step_Mult)
                           | apply multi_refl ]
     ]).
Qed.

(** **** Small-step -> Big-step *)

(** We now proceed to the other direction. We first show a useful
    lemma stating that a single small-step can be "composed" with a
    big-step evaluation to produce the same overall result in the
    big-step semantics. *)

Lemma small_step_eval_compose :
  forall e1 e2 e3,
    e1 --> e2 -> e2 ==> e3 -> e1 ==> e3.
Proof.
  intros e1 e2 e3 Hstep. revert e3. induction Hstep; intros e3 Heval; inv Heval.
  - apply eval_Plus; apply eval_Num.
  - apply eval_Plus; auto.
  - apply eval_Plus; auto.
  - apply eval_Minus; apply eval_Num.
  - apply eval_Minus; auto.
  - apply eval_Minus; auto.
  - apply eval_Mult; apply eval_Num.
  - apply eval_Mult; auto. (** the number here specifies the search depth *)
  - apply eval_Mult; auto.
Qed.

(** Again, we can make this repetitive proof much shorter using
    tacticals.  *)
Lemma step_eval_compose' :
  forall e1 e2 e3,
    e1 --> e2 -> e2 ==> e3 -> e1 ==> e3.
Proof.
  intros e1 e2 e3 Hstep. revert e3. induction Hstep; intros e3 Heval; inv Heval;
    (apply eval_Plus || apply eval_Minus || apply eval_Mult);
    (try now constructor); now auto.
Qed.

Theorem multi_step_eval  :
  forall e n,
    e -->* (Num n) -> e ==> n.
Proof.
  intros e n Hmulti.

  (* We would like to do induction on the multi-step relation, but
     right now we can't *)

  (* First, let's generalize the statement *)
  remember (Num n) as m eqn:Heq.
  revert n Heq.

  induction Hmulti; intros n Heq; subst.

  - constructor.
  - eapply small_step_eval_compose; eauto.
Qed.


(** ** The [Imp] language *)

(** The [Imp] language is a small imperative language. Its AST
    describes by the following grammar:


<<
     <com>  := skip
            | <var> := <aexp>
            | <com> ; <com>
            | if <bexp> then <com> else <com> end
            | while <bexp> do <com> end
>>
*)

(** where <var> are variables, <aexp> arithmetic expressions, similar to
those we saw above, and <bexp> is a boolean expression which we will examine
next.

The difference is that now <aexp>s and <bexp>s can contain variables.
To write an interpreter or give semantics to such a program, we will
need an environment mapping variables to their value during execution.
We pass this mapping as an extra parameter. This environment will be
created and maintained during the execution of the <com> command.

In this simple language, variables can only have values that are
natural numbers. In this language, variables don't need to be
explicitly declared and have a default value of [0]. Therefore, we
will model this environment as a total function from variable names to
natural numbers. *)

(** A map from variable names to their values *)

(** *** State *)

(** The definition of the state type. It is useful to make these
    definitions parametric on the type [A], as we may use them later
    when we extend the language. *)
Definition state (A : Type) := string -> A.

(** We write a function to generate an empty state *)
Definition empty_st {A : Type} (def : A) : state A := fun _ => def.

(** and a function to update the state when the value of a variable is changed *)
Definition update_st {A : Type} (st : state A)
  (x : string) (v : A) : state A :=
  fun z => if (x =? z)%string then v else st z.

(** We write some fancy notation for these operations. *)

Notation "'_' '!->' 0" := (empty_st 0)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" :=
  (update_st m x v)
    (at level 100, v at next level, right associativity).


(** Next we define arithmetic expressions again, but now with the
    ability to refer to variables. We also write the AST for boolean
    expressions. *)

(** *** Adding Variables: Arithmetic and Boolean Expressions *)

(** Arithmetic expressions: *)

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : string -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.


(** Boolean expressions: *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BLt : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr :  bexp -> bexp -> bexp.



(** **** Notations *)

(** Now, we define some more complicated notations, so that we can
    write concrete syntax to generate AST terms. *)

(** a string [x] can be converted to an aexp [AId x] when used in an [aexp] position. *)
Coercion AId : string >-> aexp.
(** a nat [n] can be converted to an aexp [ANum n] when used in an [aexp] position. *)
Coercion ANum : nat >-> aexp.

Declare Custom Entry com. (* declare the scope of the new syntax. *)
Declare Scope com_scope.
Declare Custom Entry com_aux.

(* we enter the scope and use its notation we must write inside [<{] [}>] . *)
Notation "<{ e }>" := e (e custom com_aux) : com_scope.

Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x < y" := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNot (BEq x y)) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "x || y" := (BOr x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).

Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.
Open Scope string_scope.
Open Scope nat_scope.

(** We can write terms with this new syntax. *)
Definition exp1 := <{ 3 + 4 * 6 }>.
Definition exp2 := <{ (2 + 1 = "x") && (true || false) }>.


Set Printing All.
(** The above syntax constructed the following terms: *)
Print exp1.
Print exp2.

Unset Printing All.


(** We define a new interpreter for [aexp] that now takes the state as a parameter. *)

Definition imp_state := state nat.

Fixpoint ainterp (st : imp_state) (e: aexp) : nat :=
  match e with
  | ANum n => n
  | AId x => st x
  | APlus e1 e2 => (ainterp st e1) + (ainterp st e2)
  | AMinus e1 e2 => (ainterp st e1) - (ainterp st e2)
  | AMult e1 e2 => (ainterp st e1) * (ainterp st e2)
  end.

(** We do the same for [bexpr]. *)
Fixpoint binterp (st : imp_state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq e1 e2 => (ainterp st e1) =?  (ainterp st e2)
  | BLe e1 e2 => (ainterp st e1) <=? (ainterp st e2)
  | BLt e1 e2 => (ainterp st e1) <? (ainterp st e2)
  | BNot b => negb (binterp st b)
  | BAnd b1 b2 => (binterp st b1) && (binterp st b2)
  | BOr b1 b2 =>  (binterp st b1) || (binterp st b2)
  end.

(** We could also define the big-step semantics, we will use these
    interpreters instead.*)

(** *** [Imp] Commands: AST *)

(** We are ready to define the AST for commands. It closely follows
   the structure of the informal grammar. *)
Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(** We extend the [com_scope] with notations for commands. *)

Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "{ x }" := x (in custom com, x at level 50) : com_scope.
Notation "'if' x 'then' y 'else' z" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y" :=
         (CWhile x y)
           (in custom com at level 88, x at level 89,
            y at level 89) : com_scope.

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition RES : string := "RES".

(** Some example [Imp] programs are below. *)

(** Addition of two numbers. *)
Definition add (a b : nat) : com :=
  (* Calculate a + b *)
  <{ X := a;
     Y := b;
     RES := X + Y
    }>.

Unset Printing Notations.
Set Printing Coercions.
(** The above syntax constructed the following terms: *)
Print add.

Set Printing Notations.
Unset Printing Coercions.


Definition pow (base exp : nat) : com :=
  (* Calculate base ** exp *)
  <{ RES := 1;
     Z := exp;
     X := base;
     while Z <> 0 do
     { RES := X * RES;
       Z := Z - 1 }
   }>.


Unset Printing Notations.
Set Printing Coercions.
(* Again, [pow] is just a [com] term constructed with [com] constructors.  *)
Print pow.

Set Printing Notations.
Unset Printing Coercions.

(** *** [Imp] Commands: Big-step Semantics *)

(** Let's now move on to defining the semantics of [com] programs.
    We will start with big-step semantics.

    We chose the notation [st =[ c ]=> st'] to write that program [c]
    when starting from an initial state [st] evaluates to a final
    state [st']. In contrast to [aexp] and [bexp] that evaluated to a
    value, a [com] program's behaviour is defined as the effect it has
    on state. *)

(** Here are the big-step semantics presented as inference rules:


                           -----------------                            (E_Skip)
                           st =[ skip ]=> st


                           ainterp st a = n
                   -------------------------------                     (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)


                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                          (E_Seq)
                         st =[ c1;c2 ]=> st''


                          binterp st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'


                         binterp st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'


                         binterp st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st


                          binterp st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)


(** We will now formalize the above as an inductive relation in Rocq. *)

(** We can reserve notations in advance so we can use them when
    defining new inductive relations. This is just syntactic
    convenience. *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).


Inductive ceval : imp_state -> com -> imp_state -> Prop :=
  | E_Skip : forall st,
      ceval st CSkip st
  | E_Asgn : forall st a n x,
      ainterp st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      binterp st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      binterp st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 ]=> st'
  | E_WhileFalse : forall b st c,
      binterp st b = false ->
      st =[ while b do c ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      binterp st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c ]=> st'' ->
      st =[ while b do c ]=> st''

  where "st =[ c ]=> st'" := (ceval st c st').

Theorem skip_does_nothing :
  (_ !-> 0) =[ skip ]=> (_ !-> 0).
Proof.
  constructor.
Qed.


Theorem add_result :
  forall (a b : nat),
    (_ !-> 0) =[ add a b ]=> (RES !-> a + b; Y !-> b; X !-> a; _ !-> 0).
Proof.
  intros a b. unfold add.

  econstructor. (* eapply E_Seq. *)

  - constructor. (* apply E_Asgn *) simpl. reflexivity.

  - econstructor. (* eapply E_Seq. *)

    constructor. (* apply E_Asgn *) simpl. reflexivity.

    econstructor. (* apply E_Asgn *) simpl. reflexivity.

Qed.


(** We can also make the above theorem a bit more general by saying
    what happens when this program is executed in any initial state. *)

Theorem add_result' :
  forall (a b : nat) (st : imp_state),
    exists st', st =[ add a b ]=> st' /\ st' RES = a + b.
Proof.
  intros a b st.

  (* This is the final state resulting from the execution of [add a b] in state [st]. *)
  exists (RES !-> a + b; Y !-> b; X !-> a; st).

  split.
  - (* proof that [add a b] evaluates to the above state. *)
    eapply E_Seq.
    + apply E_Asgn. reflexivity.
    + eapply E_Seq.
      * apply E_Asgn. reflexivity.
      * eapply E_Asgn. reflexivity.

  - (* proof that in the final state the variable [RES] has the expected value . *)
    unfold update_st. simpl. reflexivity.

Qed.

(** *** Induction on the Derivation *)

(** We can also prove a theorem about the evaluation of [com]
    programs. Here we prove that [ceval] is deterministic. That is,
    any two executions of the same program in the same state yield the
    same result. *)

Lemma ceval_deterministic :
  forall st c st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros st c st1 st2 Heval1. revert st2.
  induction Heval1; intros st2 Heval2.
  - (* E_Skip *)
    inv Heval2. reflexivity.
  - (* E_Asgn *)
    inv Heval2. reflexivity.
  - (* E_Seq *)

    inv Heval2.
    apply IHHeval1_1 in H2.
    subst.
    apply IHHeval1_2. assumption.

  - (* E_IfTrue *)
    inv Heval2. (* can be either [E_IfTrue] or [E_IfFalse] *)
    + apply IHHeval1. assumption.
    + congruence. (* contradiction *)

  - (* E_IfFalse *)
    inv Heval2. (* can be either [E_IfTrue] or [E_IfFalse] *)
    + congruence. (* contradiction *)
    + apply IHHeval1. assumption.

  - (* E_WhileFalse *)
    inv Heval2. (* can be either [E_WhileFalse] or [E_WhileTrue] *)
    + reflexivity.
    + rewrite H in H2.
      discriminate. (* contradiction *)

  - (* E_WhileTrue *)
    inv Heval2. (* can be either [E_WhileFalse] or [E_WhileTrue] *)
    + congruence. (* contradiction *)
    + apply IHHeval1_1 in H4.
      subst.

      apply IHHeval1_2. assumption.

Qed.

(** Note that induction over the program here wouldn't work. When
    reasoning about the execution we want an inductive hypothesis that
    tells us what happens about smaller parts of the execution. When
    the language has loops this is not possible by simply doing
    induction over the terms. *)

(** *** Writing an Interpreter *)

(** This language has unbounded loops, which means that execution can
    diverge (i.e., a program doesn't terminate). Therefore we cannot
    define a Rocq function to interpret this language as this could
    never terminate.

    A "standard" trick to define computational definitions of the
    semantics for such languages is to write a function that takes a
    so-called fuel variable that provides an upper bound to the number
    of steps. *)


Fixpoint cinterp (fuel : nat) (st : imp_state) (c : com) : option imp_state :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match c with
      | CSkip => Some st
      | CAsgn x n => Some (x !-> ainterp st n; st)
      | CSeq c1 c2 =>
          match cinterp fuel' st c1 with
          | Some st' => cinterp fuel' st' c2
          | None => None
          end
      | CIf b c1 c2 => if binterp st b then cinterp fuel' st c1 else cinterp fuel' st c2
      | CWhile b c =>
          if negb (binterp st b) then Some st (* If the condition is false, stop *) else
            match cinterp fuel' st c (* Run the body of the while once *) with
            | Some st' => cinterp fuel' st' (CWhile b c) (* Run the rest of the loop *)
            | None => None
            end
      end
  end.

(** In order to run the interpreter we must provide it with enough
    fuel to run the program. Otherwise, it will not return a result. *)

Compute (match cinterp 2 (_ !-> 0) (add 21 21) with
         | Some st => Some (st RES) (* Get the value if variable [RES] in the state *)
         | None => None
         end).

Compute (match cinterp 3 (_ !-> 0) (add 21 21) with
         | Some st => Some (st RES) (* Get the value if variable [RES] in the state *)
         | None => None
         end).

(** *** Case study: Correctness of [pow] *)

Theorem pow_result :
  forall (base exp : nat) st,
  exists st',
      st =[ pow base exp ]=> st' /\ st' RES = base ^ exp.
Proof.

  (* First we will prove a more general statement for the while loop
     by induction on the value of Z in the state. *)
  assert (Hloop :
           forall n st,
             st Z = n -> (* This generalizes the value of Z in the state, so we can do induction on it *)
             exists st',
               st =[ while Z <> 0 do { RES := X * RES; Z := Z - 1 } ]=> st' /\
               st' RES = Nat.pow (st X) n * st RES /\ st' Z = 0 ).
  { intros n; induction n as [ | n' IHn' ]; (* We do induction on [n]. This is exactly the number of
                                               times that the loop is executed *)
      intros st Heq.
    - (* Case n = 0 *)
      eexists. split; [| split ].
      + eapply E_WhileFalse.
        simpl. rewrite Heq. simpl. reflexivity.

      + simpl; lia.

      + lia.

    - (* Case n = S n' *)
      specialize IHn' with
        (* This will be the state after one iteration *)
        (st := (Z !-> (RES !-> st X * st RES; st) Z - 1; RES !-> st X * st RES; st)).

      destruct IHn' as [st' [Heval [Hst1 Hst2]]].

      + unfold update_st; simpl. lia.

      + eexists.  split; [| split ].
        * eapply E_WhileTrue.
          -- (* Prove that the condition is true *)
             simpl. rewrite Heq. reflexivity.
          -- (* Evaluate the first iteration *)
             econstructor. econstructor. reflexivity.
             econstructor. reflexivity.
          -- (* Evaluate subsequent iterations. Here we use the IH *)
             eassumption.

        * rewrite Hst1. unfold update_st. simpl. lia.

        * assumption. }

  - intros base expn st.

    (* This is the state after executing the initialization commands *)
    specialize Hloop with (n := expn) (st := X !-> base; Z !-> expn; RES !-> 1; st).

    destruct Hloop as [st' [Heval [Hst1 Hst2]]].

    + reflexivity.

    + eexists. split.
      * unfold pow.
        (* apply the constructors to evaluate the initialization commands *)
        eapply E_Seq; [ apply E_Asgn; reflexivity | ].
        eapply E_Seq; [ apply E_Asgn; reflexivity | ].
        eapply E_Seq; [ apply E_Asgn; reflexivity | ].

        simpl. eassumption. (* Use the [Heval] fact for the loop *)

     * rewrite Hst1. unfold update_st. simpl. lia.
Qed.
