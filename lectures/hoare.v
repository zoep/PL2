Require Import Coq.Strings.String Coq.Init.Nat Lia.

Require Import imp.

(** * Introduction to Axiomatic Semantics *)


(** Axiomatic semantics is an approach that defines the semantics of a
    language as set of inference rules that capture the intended
    behaviour of each command. These rules can be glued together to
    construct a formal derivation (i.e., a proof) of a program's
    specification.

    In this sense, axiomatic semantics is similar to proof systems
    like natural deduction. Just as natural deduction provides a
    syntactic way of constructing formal proofs in first-order logic,
    axiomatic semantics allows as to construct formal proofs of
    program specifications by purely syntactic means.

    In this section we study Hoare logic (or Floyd-Hoare logic) which
    is a formal system for reasoning about program correctness.
    We will define a Hoare logic for reasoning about Imp programs. *)

(** ** Hoare Logic *)

(** A judgment in Hoare logic is a program specification that has the form:

<<
    {{ P }} c {{ Q }}
>>
*)

(** where c is a program, [P] is a _precondition_ and [Q] is a
   _postcondition_. Such a statement is commonly called a _Hoare
   triple_.

   Preconditions and postconditions are _assertions_ about the program
   states.  That is, logical predicates over a program state that
   express logical properties about the state of a program.

   A Hoare triple informally means that
   - if a program [c] starts executing in a program state that satisfies  [P]
   - and if the execution terminates
   - then the postcondition must satisfy [Q]

   Note that this is a "weak" definition of correctness meaning that it
   only specifies what happens if the program terminates, but such a
   specification does not guarantee termination. There are strong
   variants of Hoare logic that also specify that the execution of a
   program terminates, but we will not examine them here. *)

(**  Let's formally define the type of assertions in Coq. *)

Definition assertion := imp_state -> Prop.

(** For example, we can write an assertion that makes a claim about
    the value of a variable in a program state. *)

Example assertion1 : assertion := fun st => st RES = 42.

(** Or we can make a claim about the value of a boolean expression in
    the state. *)

Example assertion2 : assertion := fun st => binterp st <{ 0 < RES + Z }> = true.

(** Because we will very often make claims about the value of boolean
    expressions in certain states, we will define a shorthands for it *)

Definition TRUE (b : bexp) : assertion := fun st => binterp st b = true.
Definition FALSE (b : bexp) : assertion := fun st => binterp st b = false.

(** It is also convenient to define the conjunction and the
    disjunction of two assertions *)

Definition assert_and (P Q : assertion) := fun st => P st /\ Q st.
(** Such assertion holds for states that satisfy both P and Q. *)

Definition assert_or (P Q : assertion) := fun st => P st \/ Q st.
(** Such assertion holds for states that satisfy P or Q. *)

Declare Scope hoare_spec_scope.

Notation "P 'AND' Q" := (assert_and P Q) (at level 68, left associativity) : hoare_spec_scope.

Open Scope hoare_spec_scope.

(** *** Inference Rules  *)

(** In order to derive a Hoare triple, Hoare logic provides a number
    of inference rules that provide a way of establishing a triple for
    a particular command of the program. There is an inference rule
    for each type.  *)


(** **** Skip *)

(** The proof rule for the command [skip] says that any precondition
    that holds on the state before the command executes, it also holds
    on the state after the command executes. This makes sense, as [skip]
    has not effect on the program's state.

<<
        ---------------------- (H_Skip)
         {{ P }} skip {{ P }}
>>
*)

(** **** Assignment *)

(** The rule for assignment is less trivial. Let's say that we want to
    prove that the assertion [fun st => st RES = 42] holds after running
    command [ RES := X * Y ].  What is the precondition that must be
    true on the initial state in order for this to be provable?

    For the triple to be derivable, we must now that the initial state
    satisfies the assertion [fun st => st X * st Y = 42]. How did we
    obtain such triple? We replaced the left-hand side of the
    assignment in the postcondition with the value of the right-hand
    side of the assignment.

    That is, the postcondition holds for the variable [X] after the
    assignment, if before the assignment is was true for the value we
    are assigning to it.

    Let's use the notation [Q[X |-> a]] for this substitution
    operation. It means that in the assertion Q we replace the value
    of variable [X] with the value of the term [a]. *)

(** To clarify things let's define this formally.

    The function [assertion_sub P X a] defines a new assertion that holds
    on a state [st] if and only if [P] holds on a state where the variable
    [X] has the value [ainterp a st]. *)

Definition assertion_sub (P : assertion) (X : string) (a : aexp) : assertion :=
  fun (st : imp_state) => P (X !-> ainterp st a ; st).

(** As usual, let's also define some notations. *)

Notation "P [ X |-> a ]" := (assertion_sub P X a)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

(** Let's see how it this functions works in practice when applied to
    the assertion [fun st => st X * st Y = 42]:

    [(fun st => st RES = 42) [ RES |-> X * Y ]] =
    [fun st => (fun st => st RES = 42) [ RES !-> ainterp st (X * Y); st]] =
    [fun st => ([ RES !-> ainterp st (X * Y)]; st) RES = 42] =
    [fun st => ainterp st (X * Y) = 42]
    [fun st => st X * st Y = 42]

    Which is exactly what we stated above.

    Now let's use this to state the proof rule for the assignment.


<<
       --------------------------------- (H_Asgn)
         {{ P[X |-> a }} X := a {{ P }}
>>
*)


(** **** Sequencing *)

(** The proof rule for sequencing says that a given a precondition [P],
    a postcondition [Q] holds on the sequencing of two commands if
    there is an assertion [R] such that:

    - command [c1] when run on a state that satisfies [P] it
      produces a state that satisfies [R]
    - command [c1] when run on a state that satisfies [R] it
      produces a state that satisfies [Q]

    Put formally:

<<
        {{ P }} c1 {{ R }}  {{ R }} c2 {{ Q }}
       ----------------------------------------- (H_Seq)
               {{ P }} c1 ; c2 {{ Q }}
>>
*)


(** **** Conditionals *)

(** The proof rule for conditional expressions says that given a
    precondition [P] on the initial state, the postcondition [Q] holds
    after the execution of [if b then c1 else c2] if

    - Starting from a state that satisfies [P st] and also [binterp st
      b = true], [c1] results in a state that satisfies [Q].

    - Starting from a state [st] that satisfies [P st] and also
      [binterp st b = false], [c2] results in a state that satisfies
      [Q].

    Put formally:

<<
                      {{ P AND (TRUE b) }} c1 {{ Q }}

                      {{ P AND (FALSE b) }} c2 {{ Q }}
        ------------------------------------------------------------- (H_Seq)
                     {{ P }} if b the c1 else c2 {{ Q }}
>>

Note that, according to our definitions above [P AND (TRUE b)]
is just notation for the assertion [fun st => P st /\ binterp st b = true]. *)


(** **** Loops *)

(** The last command we have to examine is while loops. Loops
    repeatedly execute the command in their body. Therefore the
    postcondition at the end of each iteration will be the
    precondition at the beginning of the next one.

    This is captured by the idea of an _invariant_: an assertion that
    is true _before_ and _after_ the execution of a command.

    The proof rule of [while b then c] says that if [P] is an
    invariant of the body of the loop [c], then it is also an
    invariant of the while loop. In a way, it is like applying the
    repeatedly the rule for sequencing for the command [c; c;...; c].

<<

           {{ P }} c {{ P }}
----------------------------------------(H_Seq_first_try)
    {{ P }} while b then c {{ P }} >>
>>


    Even though this rule is sound, it doesn't use all the available
    information about the value of the loop condition at the beginning
    of each iteration and at the end of the loop.

    We can strengthen the precondition of the body to asserts that the
    condition of the while is [true]. This makes sense, since the body
    will only be executed if the condition evaluates to true. This
    precondition gives us more information about the state where [c]
    executes.

    Similarly, the postcondition of the while can be strengthened to
    also assert that the while condition is be false.

    In summary, we have the rule

<<
                  {{ P AND (TRUE b) }} c {{ P }}
---------------------------------------------------------------------------(H_Seq)
            {{ P }} while b then c {{ P AND (FALSE b) }}
>>
*)


(** **** Consequence Rules *)

(** ***** Precondition Strengthening *)

(** The rules we've written cover all Imp commands. However, they are
    too restrictive to allow us to prove all specifications. Consider
    this triple:
<<
    {{ fun st => st Y = 42 }} X := Y + 1 {{ fun st => 42 < st X }}
>>

     While we would expect such specification to be provable, we cannot directly
     prove it.

     Keeping the postcondition the same, this specification that we can derive
     using our rules.
<<
    {{ fun st => 42 < st Y + 1 }} X := Y + 1 {{ fun st => 42 < st X }}
>>

    This precondition is _weaker_ that the previous one, meaning that
    if a states satisfies [{{ fun st => st Y = 42 }}] then it must also
    satisfy [{{ fun st => 42 < st Y + 1 }}]. *)


(** Let us first formally define what it means for an assertion to
    imply an other assertion and define some notation for it.

    Assertion implication [P ->> Q] holds when for any state on which
    [P] holds, so does [Q]. *)

Definition assert_implies (P Q : assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80, right associativity) : hoare_spec_scope.

(** Now we can formally write a rule that captures the precondition
    strengthening.

<<
          {{ P' }} c {{ Q }}
                P ->> P'
----------------------------------------(H_PreStrenghtening)
           {{ P }} c {{ Q }}
>>
*)



(** ***** Postcondition Weakening *)

(** Conversely, we can reason that if we can prove a a triple [{{ P }}
    c {{ Q }}] then we can prove a triple [{{ P }} c {{ Q' }}], where
    [Q'] is any postcondition that follows from [Q]. This rule is called
    strengthening of the postcondition.


<<
          {{ P' }} c {{ Q }}
                P ->> P'
----------------------------------------(H_PostWeakening)
           {{ P }} c {{ Q }}
>>
*)



(** *** Hoare Triples: Formal Definition *)

(** We can now put all of the above together and write the
    inference rules for a triple as an inductive relation. *)

Reserved Notation "{{ P }} c {{ Q }}"
  (at level 90, c custom com at level 99).

Inductive triple : assertion -> com -> assertion -> Type :=
  | H_Skip :
    forall (P : assertion),
      {{ P }} <{ skip }> {{ P }}
  | H_Asgn :
    forall (Q : assertion) (X : string) (a : aexp),
      {{ Q [X |-> a] }} <{ X := a }> {{ Q }}
  | H_Seq :
    forall (P Q R : assertion) (c1 c2 : com),
     (* Note: it is useful to have the second command first here, as
        it captures the common strategy of working our way up from the
        postcondition to build a proof.  During the proof, the triple
        for the second command will be the first goal to tackle.  *)
     {{ Q }} c2 {{ R }} ->
     {{ P }} c1 {{ Q }} ->
     {{ P }} <{ c1 ; c2 }> {{ R }}
  | H_If :
    forall (P Q : assertion) (b : bexp) (c1 c2 : com),
     {{ P AND (TRUE b) }} c1 {{ Q }} ->
     {{ P AND (FALSE b) }} c2 {{ Q }} ->
     {{ P }} <{if b then c1 else c2 }> {{ Q }}
  | H_While :
    forall (P : assertion) (b : bexp) (c : com),
      {{ P AND (TRUE b) }} c {{ P }} ->
      {{ P }} <{ while b do c }> {{ P AND (FALSE b) }}
  | H_PostWeakening :
    forall (P Q Q' : assertion) (c : com),
      {{ P }} c {{ Q' }} ->
      (Q' ->> Q) -> (* weakening of the postcondintion *)
      {{ P }} c {{ Q }}
  | H_PreStrenghtening :
    forall (P Q P' : assertion) (c : com),
      {{ P' }} c {{ Q }} ->
      (P ->> P') -> (* strengthening of the precondintion *)
      {{ P }} c {{ Q }}

where "{{ P }} c {{ Q }}" := (triple P c Q) : hoare_spec_scope.

(** *** Hoare Triples: Examples *)

(** We are now ready to use the Hoare logic to build proofs of specifications. *)

Example hoare_asgn_example :
  {{ fun _ => True }}
    X := 11;
    Y := 42
  {{ fun st => st X = 11 /\ st Y = 42 }}.
Proof.
  eapply H_Seq.
  - eapply H_Asgn.
  - Fail eapply H_Asgn.
    (* We cannot apply this rule directly. We have to strengthen
       the precondition first *)
    eapply H_PreStrenghtening.
    + apply H_Asgn.

    + unfold assert_implies, assertion_sub, update_st. simpl.
      auto.
Qed.

Example if_minus_plus :
  {{ fun _ => True }}
    <{ if (X <= Y)
       then Z := Y - X
       else Y := X + Z }>
  {{fun st => st Y = st X + st Z }}.
Proof.
  apply H_If.
  - eapply H_PreStrenghtening.
    + apply H_Asgn.

    + unfold assert_and, TRUE, assert_implies, assertion_sub, update_st. simpl.

      intros st [_ Heqb]. apply Compare_dec.leb_complete in Heqb.
      lia.

  - eapply H_PreStrenghtening.
    + apply H_Asgn.

    + unfold assert_and, TRUE, assert_implies, assertion_sub, update_st. simpl.

      intros st [_ Heqb]. apply Compare_dec.leb_complete_conv in Heqb.
      lia.
Qed.

Lemma swap (a b : nat) :
  {{ fun st => st X = a /\ st Y = b }}
    <{ X := X + Y;
       Y := X - Y;
       X := X - Y }>
  {{ fun st => st Y = a /\ st X = b }}.
Proof.
  eapply H_Seq.
  - eapply H_Seq.
    + apply H_Asgn.
    + apply H_Asgn.
  - eapply H_PreStrenghtening.
    + apply H_Asgn.
    + unfold assert_and, TRUE, assert_implies, assertion_sub, update_st. simpl.
      intros st [Heq1 Heq2]. lia.
Qed.

(** *** Automation *)

(** Derivation of Hoare triples can get tedious and repetitive for
    even a small program, so let's examine how can we automate this
    process. *)

(** We first create a new _hint database_. Using such a database we
    can extend [auto] so that it applies all the lemmas available in
    the database. By default [auto] uses the database [core], but we
    can create a new database [my_db] and use it with the tactic [auto
    with my_db]. Coq's standard library provides a few hint
    databases.*)

Create HintDb hoareDB.

(** We add all the constructors of [triple] to the database, so [auto]
    can apply them automatically. *)

Hint Constructors triple : hoareDB.

(** Let's define a tactic to perform all the unfold that we usually do
    in a Hoare triple proof. *)

Ltac unfold_all :=
  unfold assert_implies, assertion_sub,
    binterp, update_st, TRUE, FALSE, assert_and in *.

(** And a tactic to simplify the environment during a proof. *)
Ltac simplify_env :=
  match goal with
  | [ H : _ /\ _ |- _] => destruct H
  (* Patterns for binterp: the following can be obtained by some
     hypothesis of the form [binterp st b = true] or [binterp st b =
     false]. We apply the necessary lemma to make it a logical
     proposition rather than a boolean connective *)
  | [ H : false = true |- _ ] => discriminate
  | [ H : true = false |- _ ] => discriminate
  | [ H : _ =? _ = true |- _ ] => apply PeanoNat.Nat.eqb_eq in H
  | [ H : _ =? _ = false |- _ ] => apply PeanoNat.Nat.eqb_neq in H
  | [ H : _ <=? _ = true |- _ ] => apply Compare_dec.leb_complete in H
  | [ H : _ <=? _ = false |- _ ] => apply Compare_dec.leb_complete_conv in H
  | [ H : _ <? _ = true |- _ ] => apply PeanoNat.Nat.ltb_lt in H
  | [ H : _ <? _ = false |- _ ] => apply PeanoNat.Nat.ltb_ge in H
  | [ H : negb _  = true |- _ ] => apply Bool.negb_true_iff in H
  | [ H : negb _ = false |- _ ] => apply Bool.negb_false_iff in H
  | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
  | [ H : (_ || _)%bool = false |- _ ] => apply Bool.orb_false_elim in H
  (* Rewrites with an hypothesis of the form [st some_var = some_term] or
      [some_term = st some_var]. *)
  | [ st : imp_state |- _] =>
      match goal with
      | [H : st _ = _ |- _] =>
          rewrite -> H in *; clear H
      | [H : _ = st _ |- _] =>
          rewrite <- H in *; clear H
      end
  end.

(** We can use a command of the form [Hint Extern number pattern =>
    ltac_expr : hintdb] to extend auto with tactics other than apply.
    [number] is a cost that we can assign to each operation, [pattern]
    is the pattern that should be matched in order of the tactic
    [ltac_expr] to be applied, and [hintdb] the hind database we want
    to add this hint to. [auto] will try to apply such hints at each
    step of the search. We add a few of these hints. *)

Hint Extern 2 (_ = _) => lia : hoareDB.
Hint Extern 2 (_ <= _) => lia : hoareDB.
Hint Extern 2 (_ >= _) => lia : hoareDB.
Hint Extern 2 => simpl in *: hoareDB.
Hint Extern 2 => unfold_all : hoareDB.
Hint Extern 2 => repeat simplify_env : hoareDB.

Example hoare_asgn_example_auto :
  {{ fun  _ => True }}
    X := 1;
    Y := 2
  {{ fun st => st X = 1 /\ st Y = 2 }}.
Proof.
  debug eauto with hoareDB.
  (* the [debug] tactical tells us exactly what [eauto] did. *)
Qed.


Lemma swap_auto (a b : nat) :
  {{ fun st => st X = a /\ st Y = b }}
    <{ X := X + Y;
       Y := X - Y;
       X := X - Y }>
  {{ fun st => st Y = a /\ st X = b }}.
Proof.
  time eauto 7 with hoareDB.
  (* Tactic call ran for 3.435 secs (3.377u,0.055s) (success) *)
Qed.


Lemma if_minus_plus_auto :
  {{ fun _ => True }}
    <{ if (X <= Y)
       then Z := Y - X
       else Y := X + Z }>
  {{ fun st => st Y = st X + st Z }}.
Proof.
  time (now eauto 10 with hoareDB).
  (* Tactic call ran for 36.803 secs (36.14u,0.637s) (success) *)
Qed.

(** *** Case study: Proof of Fibonacci *)

(** Let's now prove the correctness of a program that uses loops.
    In particular, we will show that an iterative computation of Fibonacci
    number computes the n-th Fibonacci number correctly according a
    functional specification of Fibonacci numbers. *)

(** We first define a recursive function that naively computes the nth
    Fibonacci number. *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition CURR := "curr".
Definition PREV := "prev".

(** And an Imp program that computes the nth Fibonacci using two auxiliary variables
    [CURR] and [PREV]. *)

Definition FIB_FAST (n : nat) : com :=
  <{ PREV := 0;
     CURR := 1;
     X := 0;
     while (X <> n) do
     { Y := CURR + PREV;
       PREV := CURR;
       CURR := Y;
       X := X + 1 };
     RES := PREV
   }>.


(** Convenient tactic shorthand. *)
Ltac hoare_auto := eauto with hoareDB.


(** The specification of [FIB_FAST n] says that after the program finishes execution,
    variable [RES] will hold the value [fib n]. *)

Lemma fib_fast_correct :
  forall n,
    {{ fun _ => True }} FIB_FAST n {{ fun st => st RES = fib n }}.
Proof.
  intros n. unfold FIB_FAST.
  apply H_Seq with (Q := fun st => st PREV = 0).
  - apply H_Seq with (Q := fun st => st PREV = 0 /\ st CURR = 1).
    + apply H_Seq with (Q := fun st => st PREV = 0 /\ st CURR = 1 /\ st X = 0).
      * eapply H_Seq.
        -- (* final assignment *)
           apply H_Asgn.
        -- (* Loop invariant. Find an assertion that
              1. If it holds before the execution of the loop body,
                 it holds after the execution of the  loop body
              2. Together with the negation of the while condition,
                 it implies the final postcondition.
             Here the invariant we pick is that [PREV] will contain
             the value [fib X] and that [CURR] will contain the value
             [fib (X + 1)]. When the loop end [X] will be equal to [n]
             and [PREV] will hold the desired result. *)
          pose (INV := fun st => st CURR = fib (st X + 1) /\ st PREV = fib (st X)).

          apply H_PreStrenghtening with (P' := INV); [ | now unfold INV; hoare_auto ].
          eapply H_PostWeakening with (Q' := INV AND (FALSE <{ X <> n }>));
            [ | now unfold INV; hoare_auto ].
          (* While loop *)
          eapply H_While.
          eapply H_Seq; [ eapply H_Seq; [ eapply H_Seq | ] |]; try apply H_Asgn.
          eapply H_PreStrenghtening; [ apply H_Asgn |  ].
          unfold INV. simpl. unfold_all. simpl.
          intros st [[H1 H2] H3]. rewrite H1, H2.
          repeat rewrite PeanoNat.Nat.add_1_r. simpl. lia.
      * eapply H_PreStrenghtening; [ apply H_Asgn | hoare_auto ].
    + eapply H_PreStrenghtening; [ apply H_Asgn | hoare_auto ].
  - eapply H_PreStrenghtening; [ apply H_Asgn | hoare_auto ].
Qed.

(** ** Hoare Logic: Soundness and Completeness *)

(** For the program logic we defined to be meaningful, it needs to be
    sound with respect to the operational semantics of the language We
    say that a triple [{{ P }} c {{ Q }}] is _valid_ if that any
    terminating execution of the program [c] that starts from a state
    that satisfies [P], ends in a states that satisfies [Q].
    We write a predicate on a triple [P], [c], [Q] that expresses this
    formally. *)

Definition valid (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st st',
    st =[ c ]=> st' -> (* if the program starting from [st] terminates in [st'] *)
    P st ->            (* and [st] satisfies [P] *)
    Q st'.             (* then [st'] also satisfies [Q]. *)


(** We now prove formally that if we can derive [{{P}} c {{Q}}], then
    the triple [P], [c], [Q] is valid. We proceed by induction on the
    derivation of the triple. To show the [CWhile] case we do nested
    induction on the derivation of the evaluation relation. *)

Theorem hoare_triple_sound :
  forall (P Q : assertion) (c : com ),
    {{ P }} c {{ Q }} ->
    valid P c Q.
Proof.
  unfold valid.
  intros P Q c Htriple.
  induction Htriple; intros st1 st2 Heval HP.
  - inv Heval; auto.
  - inv Heval. assumption.
  - inv Heval. eauto.
  - inv Heval.
    + (* binterp st1 b = true *)
      eapply IHHtriple1; hoare_auto.
    + (* binterp st1 b = false *)
      eapply IHHtriple2; hoare_auto.
  - remember <{ while b do c }> as loop eqn:Heq.
    induction Heval; try congruence; inv Heq.
    + (* E_WhileFalse *)
      split; eauto.
    + (* E_WhileTrue *)
      apply IHHeval2. reflexivity.
      eapply IHHtriple; hoare_auto.
  - hoare_auto.
  - hoare_auto.
Qed.

(** An other useful property is completeness: if we can show that a
    triple [P], [c], [Q] is valid with respect to the operational
    semantics of [c], then we can build a derivation [{{ P }} c {{ Q
    }}].
    This means that Hoare logic is not only sound with respect to the
    operational semantics, but also expressive enough to allow us to
    prove all triples that are valid for the operational semantics of
    Imp.
    This proof due to Cook (1974), is more challenging. It uses a
    technical device called _weakest precondition_.
    A weakest precondition for a program [c] and an postcondition [Q],
    written [wp c Q] is an assertion such that [{{ P }} c {{ Q }}] is
    derivable and furthermore for any [P'], such that [{{ P' }} c {{ Q }}],
    we have [P' ->> P]. *)


(** We can express such assertion in the following way: [wp c Q] holds
    for any state [st] for which the execution of [c] on [st] produces
    a state [st'] that satisfies [Q]. *)
Definition wp (c:com) (Q:assertion) : assertion :=
  fun s => forall s', s =[ c ]=> s' -> Q s'.

(** We can prove that [{{ wp c Q }} c {{ Q }}] is always derivable.
    We proceed by induction on [c] *)

Lemma hoare_wp:
  forall (c : com) (Q : assertion), {{ wp c Q }} c {{ Q }}.
Proof.
  intros c; induction c; intros Q.
  - (* CSkip *)
    eapply H_PreStrenghtening. now constructor.
    intros c Hwp. apply Hwp. constructor.
  - (* CAsgn *)
    eapply H_PreStrenghtening. now constructor.
    intros c Hwp. apply Hwp. constructor; eauto.
  - (* CSeq *)
    eapply H_Seq with (Q := wp c2 Q); eauto.
    apply H_PreStrenghtening with (P' := wp c1 (wp c2 Q)).
    apply H_PostWeakening with (Q' := wp c2 Q); eauto.
    hoare_auto.
    intros ? H ? ? ? ?. eapply H.
    econstructor; eauto.
  - (* CIf *)
    apply H_If.
    + apply H_PreStrenghtening with (P' := wp c1 Q). now auto.
      intros ? [H ?] ? ?; eapply H; eauto.
      constructor; eauto.
    + apply H_PreStrenghtening with (P' := wp c2 Q). now auto.
      intros ? [H ?] ? ?; eapply H; eauto.
      apply E_IfFalse; eauto.
  - (* CWhile *)
    apply H_PostWeakening with (Q' := wp (CWhile b c) Q AND FALSE b); eauto.
    (* We use [wp (CWhile b c) Q] as the loop invariant *)
    + apply H_While.
      apply H_PreStrenghtening with (P' := wp c (wp (CWhile b c) Q)).
      eapply H_PostWeakening; eauto.
      hoare_auto.
      intros ? [H ?] ? ? ? ?. eapply H.
      eapply E_WhileTrue; eauto.
    + intros ? [H ?]. eapply H.
      eapply E_WhileFalse; eauto.
Qed.


(** It is also easy to prove that [wp c Q] is indeed the weakest
    precondition for any valid triple. *)

Lemma wp_is_wp :
  forall (c : com) (P Q : assertion),
    valid P c Q -> P ->> wp c Q.
Proof.
  intros c P Q Htriple st Hp st' Hst.
  eapply Htriple. eassumption. eassumption.
Qed.


(** Using these two lemmas we can prove completeness for Hoare logic. *)
Theorem hoare_complete (c : com) (P Q : assertion) :
  valid P c Q  ->
  {{ P }} c {{ Q }}.
Proof.
  intros H.
  apply H_PreStrenghtening with (P' := wp c Q).
  apply hoare_wp.
  apply wp_is_wp. assumption.
Qed.


(** ** Deductive Program Verification *)

(** *** Incompleteness and Undecidability *)

(** Is Hoare logic complete in the sense that either [{{ P }} c {{ Q
    }}] or [{{ P }} c {{ NOT Q }}] is derivable?
    It is easy to reason that, if the programming language we are
    reasoning about is Turing complete then Hoare logic is incomplete.
    If we can derive [{{ P }} c {{ FALSE }}], it means that the
    program [c] does not terminate starting from a state that
    satisfies [P].
    Therefore, if we could prove either [{{ TRUE }} c {{ TRUE }}] or
    [{{ TRUE }} c {{ FALSE }}] for any program [c], we could also
    prove (constructively) that [c] terminates or doesn't terminate.
    This is equivalent to having a algorithm that decides whether or
    not [c] terminates. *)


(** *** Weakest Preconditions and Verification Conditions *)

(** Even though Hoare logic is not decidable, Hoare-style reasoning
    about programs can be automated to a large extent.
    For example, say that we wanted to prove that [{{ P }} c {{ Q }}].
    If we could automatically compute the weakest precondition [wp c
    Q], then proving the desired triple would amount to proving that
    [P ->> wp c Q]. That could be done manually or (semi)automatically
    (e.g., using tactics or SMT solvers)
    It turns out that computation of weakest preconditions is not
    generally possible. The culprit is, unsurprisingly, the while
    loop.  However, if the programmer provides the invariant of every
    while loop in the program, then the rest can be automated.
    We consider a variant of Imp, where while loops are annotated with
    loop invariants. We call these _annotated_ Imp programs. *)


(** *** Annotated Programs *)

Inductive acom : Type :=
  DCSkip : acom
| DCAsgn : string -> aexp -> acom
| DCSeq : acom -> acom -> acom
| DCIf : bexp -> acom -> acom -> acom
| DCWhile : bexp -> assertion (* loop invariant *) -> acom -> acom.

(** We can write a function that erases the annotations and returns
    an Imp program without annotations. *)

Fixpoint erase (d : acom) : com :=
  match d with
  | DCSkip => <{ skip }>
  | DCAsgn X a => <{ X := a }>
  | DCSeq c1 c2 => <{ erase c1 ; erase c2 }>
  | DCIf b c1 c2 => <{ if b then erase c1 else erase c2 }>
  | DCWhile b INV c => <{ while b do erase c }>
  end.


(** We define notations similar to those of [Imp] programs, but now
    require that programs are written inside [<[ c ]>] quotes to avoid
    ambiguity. *)

Declare Custom Entry acom.
Declare Scope acom_scope.
Notation "<[ e ]>" := e (e custom acom) : acom_scope.
Notation "'skip'" :=
         DCSkip (in custom acom at level 0) : acom_scope.
Notation "x := y" :=
         (DCAsgn x y)
            (in custom acom at level 0, x constr at level 0,
             y custom com at level 85, no associativity) : acom_scope.
Notation "x ; y" :=
         (DCSeq x y)
           (in custom acom at level 90,
            right associativity) : acom_scope.
Notation "{ x }" := x (in custom acom, x at level 50) : acom_scope.
Notation "'if' x 'then' y 'else' z" :=
         (DCIf x y z)
           (in custom acom at level 89, x custom com at level 99,
            y at level 99, z at level 99) : acom_scope.
Notation "'while' x '{{' inv '}}' 'do' y" :=
         (DCWhile x inv y)
           (in custom acom at level 88, x custom com at level 89,
               inv constr, y at level 89) : acom_scope.

Open Scope acom_scope.



(** Given an annotated program, where each loop is annotated with an
    invariant, and a postcondition, we can write a function that
    computes the _weakest liberal precondition_ for this program and
    postcondition.

    All cases other than while loops, follow directly from the rules
    of Hoare logic.

    For a while loop [DCWhile b INV c], the weakest precondition is
    the invariant itself.  However, for it to a precondition that is
    indeed an invariant and also it implies the desired postcondition,
    it must additionally satisfy that

    1. [TRUE b AND INV ->> wlp INV c]

    2. [FALSE b AND INV ->> Q]

    The first condition ensures that [INV] is indeed an invariant for
    the body of the while: the assertion [INV] together with the
    assertion that the loop condition is true, imply the weakest
    precondition such that [INV] holds after the execution of [c].
    This way the preservation of [INV] by the body of the loop is
    ensured.

    The second condition ensures that the assertion [INV] together
    with the assertion that the loop condition is false, imply the
    desired post condition.

    We write two functions:

    1. [wlp ac Q] that computes the weakest precondition for [c] to
       satisfy [Q]

    2. [vc ac Q] that computes the _verification conditions_ that must
       be true for the annotations of [c] to be adequate invariants in
       order to prove [Q]. *)

Fixpoint wlp (ac : acom) (Q : assertion) : assertion :=
  match ac with
  | DCSkip => Q
  | DCAsgn X a => Q [X |-> a]
  | DCSeq c1 c2 => wlp c1 (wlp c2 Q)
  | DCIf b c1 c2 =>
      (fun st => (binterp st b = true -> wlp c1 Q st) /\
                 (binterp st b = false -> wlp c2 Q st))
  | DCWhile b INV c => INV
  end.

Fixpoint vc (ac : acom) (Q : assertion) : Prop :=
  match ac with
  | DCSkip => True
  | DCAsgn X a => True
  | DCSeq c1 c2 => vc c1 (wlp c2 Q) /\ vc c2 Q
  | DCIf b c1 c2 => vc c1 Q /\ vc c2 Q
  | DCWhile b INV c =>
      vc c INV /\ (* verification conditions for the body *)
      ((INV AND TRUE b) ->> wlp c INV) /\ (* INV is invariant *)
      ((INV AND FALSE b) ->> Q) (* Inv implies postcondition *)
  end.

(** We can now prove that if the verification conditions hold for a
    given program [ac] and precondition [Q], then the triple
    [{{ wlp ac Q }} erase ac {{ Q }}] is derivable. *)
Theorem wlp_sound:
  forall (ac : acom) (Q : assertion),
    vc ac Q ->
    {{ wlp ac Q }} erase ac {{ Q }}.
Proof.
  intros dc;
    induction dc as [ | x a | c1 IHda1 c2 IHac2
                    | b c1 IHac1 c2 IHac2 | b INV c IHac ];
    intros Q Hvc; simpl in *.
  - (* CSkip *)
    hoare_auto.
  - (* CAssign *)
    hoare_auto.
  - (* CSeq *)
    hoare_auto.
  - (* CIf *)
    eapply H_If.
    + eapply H_PreStrenghtening.
      eapply IHac1.
      hoare_auto.
      hoare_auto.
    + eapply H_PreStrenghtening.
      eapply IHac2.
      hoare_auto.
      hoare_auto.
  - (* CWhile *)
    eapply H_PostWeakening. apply (H_While INV).
    eapply H_PreStrenghtening. eapply IHac. now auto.
    now auto. now auto.
Qed.


(** As a corollary, we can prove that in order to prove any triple [{{
    P }} ac {{ Q }}] for an annotated program, it suffices to prove
    that the precondition [P] imply the weakest precondition and that
    the verification conditions hold. *)

Corollary verify_triple :
  forall (ac : acom) (P Q : assertion),
    vc ac Q -> (P ->> wlp ac Q) ->
    {{ P }} erase ac {{ Q }}.
Proof.
  intros ac P Q H1 H2.
  eapply H_PreStrenghtening.
  now apply wlp_sound; auto.
  assumption.
Qed.


(** *** Fibonacci, Again *)

(** That gives as a verification strategy for any triple we want to
    prove.  Let's apply it to the verification of the Fibonacci
    program we wrote earlier. *)

(** First, we annotate [FIB_FAST] with the invariant. *)

Definition FIB_FAST_ANNOT (n : nat) : acom :=
  <[ PREV := 0;
     CURR := 1;
     X := 0;
     while (X <> n) {{ fun st => st CURR = fib (st X + 1) /\ st PREV = fib (st X) }} do
     { Y := CURR + PREV;
       PREV := CURR;
       CURR := Y;
       X := 1 + X };
     RES := PREV
   ]>.

Ltac norm_plus :=
  repeat (match goal with
          | H : context [?e + 1] |- _ => rewrite (PeanoNat.Nat.add_1_r e) in H
          | |- context [?e + 1] => rewrite (PeanoNat.Nat.add_1_r e)
          end).



Hint Extern 3 => norm_plus : hoareDB.
Hint Extern 1 (_ /\ _)=> split : hoareDB.

(** The specification of [FIB_FAST n] says that after the program
    finishes execution, variable [RES] will hold the value [fib n]. *)
Lemma fib_fast_correct' :
  forall n,
    {{ fun _ => True }} erase (FIB_FAST_ANNOT n) {{ fun st => st RES = fib n }}.
Proof.
  intros n. apply verify_triple.
  - repeat split; hoare_auto.
  - hoare_auto.
Qed.


(** ** References *)

(** - https://github.com/xavierleroy/cdf-program-logics/blob/main/Hoare.v
    - https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
    - https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html
    - https://softwarefoundations.cis.upenn.edu/plf-current/HoareAsLogic.html
*)
