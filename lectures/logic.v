Require Import Coq.Init.Nat Coq.Arith.Arith Lia Coq.Lists.List.
Import ListNotations.

(** * A Small Introduction to The Coq Proof Assistant (II): Logic **)


(** In part 1, we worked with stating and proving logical
    propositions. Logical propositions are themselves part of the same
    functional programming language. Since Coq is typed, logical
    propositions must also have a type. Their type is called [Prop].
    Everything that we have put inside a [Lemma] declaration is in
    fact an expression of type [Prop].

    Here are some examples: *)

Check (2 = 2).

Check (1 =? 1 = true).

Check (forall A (x y z: A), x = y -> y = z -> x = z).


(** Of course, not all propositions are provable. We can express
    nonsensical claims that are not provable. *)

Check (3 = 2).

Check (forall (n m : nat), n = m).

(** As with any other type, we can construct propositions and assign
    them to names using a [Definition]. *)

Definition eq_transitive : Prop :=
  forall A (x y z: A), x = y -> y = z -> x = z.

Lemma eq_transitive_proof : eq_transitive.
Proof.
  unfold eq_transitive. intros A x y z Heq1 Heq2.
  rewrite Heq1. assumption.
Qed.


(** We can also write predicates and relations. That is,
    [Prop]-returning functions that define properties on their
    arguments. Such properties, of course, may or may not be provable
    for every element of the domain of the function.

    [is_even] is a predicates that holds when a number is even. *)

Fixpoint is_even (n : nat) : Prop :=
  match n with
  | 0 => True
  | 1 => False
  | S (S n') => is_even n'
  end.

Check is_even.

(** Prints:

[is_even : nat -> Prop]

*)

(** [is_even] a predicate over natural numbers, and can be used to
    assert that the proposition [is_even n] holds for a natual number
    [n]. We can use it to state lemmas.  *)


Lemma is_even_6 : is_even 6.
Proof.
  simpl.
  (* Evaluates to [True]. Note that this is not the boolean value
     true. (What do you think is the type of [True]?

     We don't know how to prove this yet. In fact, we don't even know
     what [True] is (hint: as you might expect it is not a built-in).
     We will learn more about this soon. For now we will use the tactic
     [auto] that can automatically discharge some kinds of goals (more
     on this soon!).  *)
  auto.
Qed.


Lemma is_even_7 : is_even 7.
Proof.
  simpl.
  (* Evaluates to [False]. Of course, we can't prove false *)
Abort.


(** As functions, logical predicates or relations can be
    higher-order. Here's a higher-order predicate over _relations_
    that assets that a relation [R] is transitive. *)


Definition R_transitive {A : Type} (R : A -> A -> Prop) : Prop :=
  forall (x y z: A), R x y -> R y z -> R x z.

(** We can use the above predicate to state that equality is transitive. *)

(** Locate is useful to find notations that are defined in the scope. *)
Locate "=".

(** Prints:

[Notation "x = y" := (eq x y) : type_scope (default interpretation)]

*)


Lemma eq_transitive' : forall A, R_transitive (@eq A).
Proof.
  intros A x y z H1 H2. subst. reflexivity.
Qed.


(** ** Logical Connectives *)

(** Coq's language can express logical connectives and quantifiers.
    Most of these definitions are not primitives. They are all
    defined in terms of the core functional language in the Coq's
    standard library.

    We have already used some of them extensively: [->] (implication)
    and [forall _, _] (universal quantification).

    - [/\] : conjunction

    - [\/] : disjunction

    - [~] : negation

    - [->] : implication

    - [<->] : equivalence

    - [forall _, _] : universal quantification forall exists

    - [exists _, _] : existential quantification

    Universal quantification is one of the few primitives of the core
    language. It is itself a term of the language. Implication is
    defined in terms of forall quantification. We will examine this
    more in depth later in the course. All other connectives are
    defined in terms of the core language.

    There are also two constants: [True] and [False]. They represent
    truth and falsity respectively. *)

(** *** Implication *)

(** We have already worked with logical implication when stating
    theorems. An implication [P -> Q] means that [Q] is a logical
    consequence of [P] (in other words, "if [P] then [Q]").

    A proof a proposition [P -> Q] is quite similar to a function with
    this type: given a proof of proposition [P] it returns a proof of
    the proposition [Q].

    Therefore, if we have a proof of [P] and a proof of [P -> Q] we
    can derive a proof of [Q]. This logical rule is known as "modus
    ponens" (or implication elimination). It can be expressed as an
    inference rule:

<<
      P  -> Q      P
   --------------------
            Q
>>

  This kind of reasoning can be performed in Coq with the [apply]
  tactic. *)


Lemma modus_ponens:
  forall (P Q : Prop),
    (P -> Q) ->
    P ->
    Q.
Proof.
  intros P Q HPQ HP.

  apply HPQ. (* this will transform the goal to [Q] *)

  apply HP. (* apply can also be used when the goal exactly matches an assumption *)
Qed.


Lemma modus_ponens_2:
  forall (P Q : Prop),
    (P -> Q) ->
    P ->
    Q.
Proof.
  intros P Q HPQ HP.

  (* We can also apply an implication to an other hypothesis.
     The hypothesis should match the premise of the implication,
     and the [apply] tactic will transform it to the conclusion
     of the implication. *)
  apply HPQ in HP.

  apply HP. (* apply can also be used when the goal exactly matches an assumption *)
Qed.


Lemma modus_ponens_3:
  forall (P Q R: Prop),
    (P -> Q -> R) ->
    P ->
    Q ->
    R.
Proof.

  intros P Q R HPQR HP HQ.
  apply HPQR.
  - apply HP.
  - apply HQ.
Qed.


(** **** Propositions vs Proofs *)

(** In the above proofs notice the difference between [P : Prop] and
    [H : P].

    The expression asserts that [P] has type [Prop], i.e., [P] is a
    logical proposition. But it says nothing about the validity of the
    proposition.

    The second expression asserts that [H] has type [P]. This means that
    [H] is a _proof_ of the proposition [P]. Therefore, [P] holds. *)


(** **** The [auto] Tactic *)

(** Let's prove that implication is a transitive relation. We cannot
    use the infix implication notation as an unapplied function. We
    need to wrap it in a function. *)

Check (fun (x y : Prop) => x -> y).

Definition impl := fun (x y : Prop) => x -> y.

(** We can prove the claim using the [apply] tactic we just learned. *)
Lemma impl_transitive : R_transitive impl.
Proof.
  unfold R_transitive, impl. intros x y z H1 H2 Hx.

  apply H2. apply H1. assumption.
Qed.

(** We can also prove the claim using [auto] tactic that automates the
   process. *)
Lemma impl_transitive_2 : R_transitive impl.
Proof.
  unfold R_transitive, impl. intros x y z H1 H2.

  auto. (* magic! *)
Qed.


(** [auto] is a tactic that performs what is called proof automation.
     Proof automation synthesizes automatically the proof of a goal
     and allows us to prove theorems using smaller proof scripts.

     Coq has powerful automation facilities that allow the user to
     build custom tactics to solve goals (but, most likely, we will
     not get to see much of it in this course). It also has some
     built-in automation tactics (e.g., decision procedures for
     arithmetic).

     [auto] performs proof search, by searching for a proof that
     consists of a sequence of some particular tactics, including
     [intros], [apply], [assumption] and [reflexivity] tactics. In
     this case [auto] applied [H2], then [H1] and then proved the goal
     by [assumption].

     Tip: We can specify the search depth of the using [auto n] where
     [n] is a natural number (the default depth is 5).

     From the "Software Foundations" textbook: The behavior of [auto
     n] can be summarized as follows. It first tries to solve the goal
     using [reflexivity] and [assumption]. If this fails, it tries to
     apply a hypothesis (or a lemma that has been registered in the
     hint database), and this application produces a number of
     sugoals. The tactic [auto (n-1)] is then called on each of those
     subgoals. If all the subgoals are solved, the job is completed,
     otherwise [auto n] tries to apply a different hypothesis
     (backtracking). *)

(** *** Universal Quantification *)

(** A universal quantifier, [forall (x : A), P x] states that a
    predicate [P] of type [A -> Prop] holds for every element of type
    [A].

    If we have a proof of [forall (x : A), P x] then we can derive [P
    a] for any [a]. There are multiple ways we can do this in
    Coq. Here we review [apply] and [specialize]. *)

(** Different kinds of logical systems allow for quantification over
    different objects. This affects the expressively of the logic.
    For example:

    (0th order) predicate logic: no quantification

    first-order logic: quantification over ground types (not
    predicates or functions).

    second-order logic: quantification over predicates and relations
    parametric over ground terms (i.e., sets)

    third-order logic: quantification over predicates and relations
    that can be parametric on other predicates or relations (predicates
    on predicates) (i.e., sets of sets).

    ...

    higher-order logic: quantification over arbitrary predicates and
    relations (or arbitrary sets)

    Notice the direct correspondence with order of a function. Coq
    encodes a higher-order logic, making it a very expressive logical
    system. *)

Lemma forall_example_1 :
  (* Question: What is the order of this statement? *)
  forall (P : nat -> Prop),
    (forall x, P x) ->
    P 42.
Proof.
  intros P HP.
  (* we can use [specialize] to explicitly instantiate a universally
     quantified variable *)
  specialize HP with (x := 42).

  assumption.
Qed.

Lemma forall_example_2 :
  forall (P : nat -> Prop),
    (forall x, P x) ->
    P 42.
Proof.
  intros P HP.
  (* we can use [apply] with the keyword [with] to instantiate the
     universally quantified variable *)
  apply HP with (x := 42).
Qed.

Lemma forall_example_3 :
  forall (P : nat -> Prop),
    (forall x, P x) ->
    P 42.
Proof.
  intros P HP.
  (* In this case, Coq does not need the annotation [with] because
     when we do [apply] it tries to unify the conclusion of the
     hypothesis with the goal. From this unification it can figure out
     that [x := 42]. Note that this is not always possible (see
     [forall_example_5]. *)
  apply HP.
Qed.

(** Here are some more convoluted examples *)

Lemma forall_example_4 :
  forall (P Q : nat -> Prop),
    (forall x, Q x -> P x) ->
    Q 3 ->
    P 3.
Proof.
  intros P Q HPQ HQ.
  apply HPQ. assumption.
Qed.


Lemma forall_example_5 :
  forall (P Q : nat -> Prop),
    (forall x y, Q (x + y) -> P x) ->
    Q 42 ->
    P 17.
Proof.
  intros P Q HPQ HQ.
  Fail apply HPQ.
  (* Here the [with] annotation is necessary, because Coq cannot
     figure out [y] using unification on the conclusion. *)
  apply HPQ with (y := 25).
  simpl.
  assumption.
Qed.


(** ** Inductively Defined Propositions *)

(** Constants [True] and [False] and most of the non-primitive logical
    connectives are defined as inductive propositions.

    Just as inductive types define new types and describe how values
    of new types can be constructed (e.g., think of [list] or [nat]),
    inductive propositions define new propositions and describe how
    evidence of new propositions can be constructed.

    In the usual mathematical notation of formal logic, these
    constructions are commonly represented by inference rules (we will
    see quite a few of these when we get to programming languages
    theory in the next lectures.  *)

(** Inference rules have the form
<<
       premise_1   ...   premise_n
    ---------------------------------
               conclusion
>>

    and describe how a conclusion can be derived by a set of premises.


    For example, we can define a predicate [even] using inference rules.

<<
    -------------  (base case)
       Even 0


        Even n
    ----------------  (inductive case)
     Even (S (S n))
>>


    We can use these inference rules to construct a _derivation tree_, which
    is _evidence_ that a conclusion holds.



<<
                        --------  (base case)
                         Even 0
                        --------  (inductive case)
                         Even 2
                        --------  (inductive case)
                         Even 4
>>

   This, in fact, is quite similar to proofs in Coq.

   We can mechanize all of the above in Coq.*)


Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSS : forall n, Even n -> Even (S (S n)).

(** Let's also define [Odd], as we will use it later on. *)
Inductive Odd : nat -> Prop :=
| Odd0 : Odd 1
| OddSS : forall n, Odd n -> Odd (S (S n)).

Check EvenSS.

Example Even4 : Even 4.
Proof.
  apply EvenSS.
  apply EvenSS.
  apply Even0.
Qed.

(** The above proof closely follows the handwritten one. *)

(** We can write it more succinctly using some convenient tactics. *)

Example Even4' : Even 4.
Proof.
  (* The [constructor] tactic will apply the first constructor of an
     inductive proposition that matches the goal (warning: this might
     now always be the desired one! *)
  constructor.
  constructor.
  constructor.
  (* Sometimes in class, we will be very explicit about the
     constructors we are applying, for the shake of clarity and
     understanding. *)
Qed.

Example Even4'' : Even 4.
Proof.
  (* the [repeat] tactic will repeatedly apply a tactic until it fails  *)
  repeat constructor.
Qed.


(** Now suppose we want to prove that if for some [n], [Even n] holds,
    then [Even (n - 2)] also holds. Let's first try to do it
    informally.

    We have [Even n]. There are two cases from which we can have
    obtained it.

    - Case 1: [n = 0] and [Even 0] (base case).

      Then by the definition of subtraction on [nat] we have [0 - 2 = 0].
      We need to prove that [Even 0] which follows from the assumption
      (or by applying the base case rule).


    - Case 2: [n = S (S n')] and [Even n'] (inductive case).

      We need to show [Even (S (S n') - 2)]. By the definition of
      [minus] we have [S (S n') - 2 = n']. We derive [Even n'] from
      the assumption.

    Now let's mechanize this proof. *)

Lemma even_minus2 :
  forall n, Even n -> Even (n - 2).
Proof.
  intros n Hyp.

  (* The [inversion] tactic lets us do exactly what we did above:
     examine how the derivation of an inductive proposition was
     obtained. It will also generate qualities for the arguments of
     the inductive predicate so that they match the arguments
     of the inductive predicate in the conclusion of the corresponding
     constructor. *)

  inversion Hyp as [ Heq | n' Hyp' Heq ].
  (* we use intro patterns with the same meaning as in [destruct] *)

  - subst. simpl. constructor. (* or [assumption.] *)

  - subst. simpl.

    Search (_ - 0).

    rewrite Nat.sub_0_r. assumption.
Qed.

(** Practice: write an inductive predicate Forall that takes as input
    a predicate over the type [A] and a list of type [list A], and
    holds if all elements of the list satisify the prefdicate. *)

(* In class *)
Inductive Forall {A : Type} (P : A -> Prop) : list A -> Prop :=
| Forall_nil: Forall P nil
| Forall_cons :
  forall (x : A) l, P x -> Forall P l -> Forall P (x :: l).



Lemma Forall_example:
  Forall Even [2;4;6].
Proof.
  (* In class *)
  apply Forall_cons.
  repeat constructor.

  apply Forall_cons.
  repeat constructor.

  apply Forall_cons.
  repeat constructor.

  apply Forall_nil.

Qed.

(** Now let's move on to see some common inductive propositions in Coq. *)

(** *** [True] and [False] *)

Module TrueFalse.


  (** Intuitively, [True] is a proposition for which we can _always_
      construct evidence for.

      A very simple way to represent this is with an inductive
      relation with one constructor that takes no arguments. *)

  Inductive True : Prop :=
  | I : True.

  (** There are, in fact, equivalent ways of defining this (can you
      think of any?), but that's the most succinct. *)

  (** Now, on the other hand, [False] is a proposition for which
      evidence can never be constructed.

      For example we could write the following: *)


  Inductive False1 : Prop :=
  | Absurd : Even 1 -> False1.

  (** We could never build a proof of such proposition: *)
  Lemma false_proof1:
    False1.
  Proof.
    apply Absurd.
    Fail constructor.
  Abort.


  (** In fact, if we were able to prove [False] we would be able to prove anything. *)

  Lemma ex_falso_quodlibet1: (* from contradiction, anything follows *)
    forall (Q : Prop), False1 -> Q.
  Proof.
    intros Q Hyp.
    inversion Hyp as [Hyp'].
    inversion Hyp'.
    (* Inversion cannot find a way to derive Hyp'. There are 0 cases,
       and the result follows vacuously *)
  Qed.


  (** Now, there is a more elegant way to write [False], which is also
      the definition of the standard library. *)


  Inductive False : Prop := .

  (** This is an inductive proposition with _no_ constructors. We
      obviously have no way of providing evidence of such proposition.

      Again, the two situations above still apply. *)


  Lemma false_proof:
    False.
  Proof.
    Fail constructor.
  Abort.

  (** Being able to prove [False] within a proof system would actually
      mean that the proof system is not sound

     In fact, if we were afle to prove [False] we would be able to
     prove anything. *)

  Lemma ex_falso_quodlibet:
    forall (Q : Prop), False -> Q.
  Proof.
    intros Q Hyp. inversion Hyp.
  Qed.

End TrueFalse.


(** *** Negation *)

Module Not.

  (** The logical negation of a proposition, [~ P] states that [P] is
      not provable. Not provable means that [P] is an absurd
      proposition for which there should be no way of providing
      evidence.

      Can you imagine how negation is defined?

      Since [P] is absurd, and as we saw, from absurdity we can derive
      anything, we could define negation as [~ P = forall Q, P -> Q]

      We can also define it in a simpler but equivalent way.

   *)

  Definition not (P : Prop) := P -> False.

  (** As usual, there is some convenient notation *)
  Notation "~ x" := (Logic.not x) : type_scope.

End Not.


(** **** [exfalso] and [contradiction] *)

(** Sometimes when we do proofs, we end up with hypotheses that are
    absurd or contradicting. In such cases we can use the tactics
    [exfalso] and [contradiction].

    [exfalso] just replaces the goal with [False], by applying a lemma
    similar to [ex_falso_quodlibet].

    [contradiction] solves any goal if the context contains [False] or
    contradictory hypotheses. Here are some examples: *)

Lemma exfalso_example :
  forall P Q,
    P -> ~ P -> Q.
Proof.
  intros P Q H1 H2.

  exfalso.

  unfold not in H2.
  apply H2. assumption.
Qed.


Lemma contradiction_example :
  forall P Q,
    P -> ~ P -> Q.
Proof.
  intros P Q H1 H2.
  contradiction.
Qed.


(** It is easy to prove that if we have a proof of [P], then we can
    obtain a proof of [~~P]. *)

Lemma P_implies_not_not_P :
  forall P, P -> ~ ~ P.
Proof.
  intros P HP.
  unfold not. (* optional *)
  intros HnotP.
  (* now, we have to _contradicting_ hypotheses, [P] and [~P] we have
     a number of tactics at hand to prove this. The following all
     work. *)

  (* This works: [apply HnotP. assumption.]  *)

  (* This also works: [auto.] *)

  contradiction.

Qed.

(** **** Proof by Contradiction *)

Lemma not_not_P_implies_P :
  forall P, ~ ~ P -> P.
Proof.
  unfold not.
  intros P HP. (* there is no obvious way to proceed *)
Abort.

(** As it turns out, there is no obvious way to _construct_ this
    intuitive claim.

    In fact, to proceed, we would have to do a proof _by
    contradiction_.  A proof by contradiction (not to be confused with
    the tactic [contradiction]) is a form of proof that establishes a
    claim by by showing that assuming the claim to be false leads to a
    contradiction.

    Here's a handwritten proof by contradiction of the above claim:

    Given [~~ P], we must prove [P]. Assume that [~P]. Then by the
    hypothesis we can prove [False]. Which is a contradiction.
    Therefore, [P] must hold.

    Proof by contradiction is equivalent to saying that for each
    proposition [P], either [P] or [~ P]. This is known as law of
    excluded middle.

    This is not directly provable in Coq. If we want to extend the
    reasoning to include this law, we must add it as a logical
    axiom. This is a logically consistent axiom: the resulting logical
    system will be sound (meaning we wouldn't be able to derive a
    proof of a false proposition). In fact, standard mathematical
    proofs very often use proofs by contraction. A logic that assumes
    the law of excluded middle is called _classical_.

    A logic like Coq's that does not assume the principle of excluded
    middle is called _constructive_. The advantage of not
    adding the axiom of excluded is that proofs carry _evidence_ of
    the fact that we are proving.

    For example, with the law of excluded middle we could prove that
    for any program [p], [p] either terminates or not:

                   [halts p \/ ~ halts p]

    It is perfectly reasonable to expect this from any program, but
    the proof itself cannot be used to provide evidence as to weather
    a particular program [p] terminates or not. Formalizing the [or]
    connective will make this clearer. *)

(** *** Disjunction *)

Module Or.

  (** Having a proof of [P \/ Q] means that we can provide a proof of
      [P] or a proof of [Q]. This is formalized in the inductive
      relation below. *)

  Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> or A B (* we have a proof of A *)
  | or_intror : B -> or A B. (* we have a proof of B *)

  Notation "A \/ B" := (or A B) : type_scope.

End Or.


Lemma bool_dec :
  forall (b : bool), b = true \/ b = false.
Proof.
  intros b. destruct b.
  - (* [left] is a tactic that is the same as applying the first
       constructor of an inductive proposition with two
       constructors. In the case of a disjunction, it is the same as
       [apply or_introl]. *)
    left. reflexivity.
  - (* [right] is a tactic that is the same as applying the second
       constructor of an inductive proposition with two
       constructors. In the case of a disjunction, it is the same as
       [apply or_intror]. *)
    right. reflexivity.
Qed.


(** Let's prove that every number is either [Even] or [Odd] *)

(** We must prove a slight variation of this theorem, that will give
    us a stronger induction hypothesis. *)

Lemma even_or_odd_aux :
  forall n m, m <= n -> Even m \/ Odd m.
Proof.
  intros n.
  (* To derive a general enough induction hypothesis, we must keep [m]
     generalized in the statement and not introduce it to the
     context.  *)
  induction n as [| n' IHn' ]; intros m Hlt.

  - (* case [n = 0] *)

    destruct m as [| m' ].

    + (* case [m = 0] *)

      (* Notice that we used a different kind of bullet for the inner
         cases. Available bullets are: [-], [+], [*], [--], [++],
         [**], and so on. *)

      left. constructor.

    + (* case [m = S m'] *)
      (* The hypothesis [Hth] is absurd *)

      (* [<=] is an inductive proposition.  We can use inversion to
         invert it. Since there is no possible way to obtain it, we
         proof is done *)
      Print le. (* [<=] is notation for [leq] *)
      inversion Hlt.

  - (* case [n = S n'] *)

    destruct m as [| m'].
    + (* case [m = 0] *)
      left. constructor.

    + (* case [m = S m'] *)
      destruct m' as [| m''].

      * (* case [m' = 0] *)
        right. constructor.

      * (* case [m' = S m'' ] *)

        (* During proofs we can use assert to prove intermediate results. *)
        assert (Hlt' : m'' <= n').
        { (* [lia] is a tactic that implements a decision procedure for
             linear integer arithmetic *)
          lia.
        }

        (* [specialize] is a convenient tactic to apply arguments to a
           term. We can use it to instantiate universal quantifiers
           and implications. *)
        specialize (IHn' m'' Hlt') as Hyp.
        (* Notice that we could have also done [apply IHn' in Hlt'] *)

        inversion Hyp.

        -- (* We have [Even m''] *)
           left. constructor. assumption.

        -- (* We have [Odd m''] *)
          right. constructor. assumption.

Defined. (* This is a little trick. It will allow us to inspect the constructed proof *)


Corollary even_or_odd : forall x, Even x \/ Odd x.
Proof.
  intros.
  (* We want to use the previous proof by instantiating the
     universally quantified variable [n] with [x] and the universally
     quantified variable [m] with [x]. To do this, we can use the
     [with] keyword. *)

  apply even_or_odd_aux with (n := x).

  lia.

Defined.

(** Now, [even_or_odd] is not just a proof that every number is even
    or odd.  It also builds _evidence_ for whether a number is even or
    odd. In this sense, it is an algorithm that decides if a number is
    even or odd. *)


Compute (even_or_odd 8).
(* We can see the exact proof derivation that 8 is even, and also that
   the left constructor was used to prove the disjunction. *)
Compute (even_or_odd 7).
(* We can see the exact proof derivation that 7 is odd, and also that
   the right constructor was used to prove the dis junction. *)


(** **** Excluded middle *)


Module EM.

  (** As we saw earlier, the intuitive claim that for all propositions
      [P], we have [P] or [~P] is not directly provable.

      In order to prove such a claim, one would have to provide a
      decision procedure for a logical formula. For example, one can
      prove the following. *)

  Lemma decideP :
    forall (b : bool) P,
      (b = true -> P) ->
      (b = false -> ~ P) ->
      P \/ ~ P.
  Proof.
    intros b P Htrue Hfalse.

    destruct b.

    - (* b = true *)
      left; auto.

    - (* b = false *)
      right; auto.
  Qed.

  (** This means, that in the constructive logic of Coq, one can prove
      the excluded middle only for propositions that are
      decidable. That is, we must know which which side of the
      disjunction holds in order to prove it. The benefit of
      constructive logic is that we can extract evidence from our
      proofs, or in other words that proofs have a so-called
      _computational interpretation_.

      Constructive logic has, however, limitations. There are
      statements that can easily be proven in classical logic but have
      complicated constructive proofs, and there are some statements
      that have no constructive proof at all. If we want to reason
      using classical logic, we can assume the excluded middle as
      axiom. *)

  Axiom EM: forall P, P \/ ~ P.

    (** This is a sound thing to do. That is, it doesn't lead to
      contradictions. Proving that the logical system of Coq together
      with the law of excluded middle is consistent is a
      metatheoretical property of the system that cannot be carried
      out in the system itself. We can however prove that the excluded
      middle is irrefutable: [(forall P, ~~ P \/ ~ P)]. That is, the
      negation of excluded middle is contradictory. Hence, assuming
      the excluded middle as an axiom is safe. *)

End EM.

(** *** Conjunction *)

Module And.

  (** Having a proof of [P /\ Q] means that we can provide a proof of
      [P] and a proof of [Q]. This is formalized in the inductive
      relation below. *)

  Inductive and (A B : Prop) : Prop :=
  | conj : A -> B -> and A B. (* we have a proof of A and B *)

  Notation "A /\ B" := (or A B) : type_scope.

End And.

(** Given [P] and [Q] we can prove [P /\ Q] *)
Lemma impl_and :
  forall P Q, P -> Q -> P /\ Q.
Proof.
  intros P Q H1 H2.
  (* [split] can be used as a shorthand for applying the constructor
     [conj]. *)
  split.

  - auto.

  - auto.
Qed.

(** Given [P /\ Q] we can prove [P] *)
Lemma and_left :
  forall P Q, P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [H1 H2].
  assumption.
Qed.

Lemma and_comp :
  forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  (* in class *)
  intros P Q.

  intros H.

  inversion  H as [H1 H2].

  split; assumption.

Qed.

(** *** If and only if *)

Module Iff.

  (* We can define equivalence of propositions using [->] and [/\] *)
  Definition iff (A B : Prop) := (A -> B) /\ (B -> A).

  Notation "A <-> B" := (iff A B) : type_scope.

End Iff.

Lemma iff_example1 :
  forall P Q, (P <-> Q) -> P -> Q.
Proof.
  intros  P Q H1 Hp.
  (* equivalences can be applied both ways. *)
  apply H1; eauto.
Qed.

Lemma iff_example2 :
  forall P Q, P <-> Q -> Q -> P.
Proof.
  intros  P Q H1 Hq.
  (* equivalences can be applied both ways. *)
  apply H1; auto.
Qed.

Lemma iff_example3 :
  forall P Q, (P -> Q) -> (Q -> P) -> P <-> Q.
Proof.
  intros  P Q H1 H2.
  (*to prove an equivalence can use [split] since it is a conjunction. *)
  split; eauto.
Qed.

Lemma iff_example4 :
  forall P Q R, (P -> Q -> R) <-> (P /\ Q -> R).
Proof.
  intros  P Q R. split; intros H1.
  - intros H2; inversion H2 as [H3 H4].
    apply H1; assumption.

  - intros H2 H3. apply H1. split; assumption.
Qed.


(** *** Equality *)

Module Eq.

  (** Equality is a binary relation that we have already seen. It's
      type is [forall (A : Type), A -> A -> Prop]. It is also
      inductively defined.

      The definition of equality captures that only [x = x] can be
      proved.  *)



  Inductive eq {A : Type} (x : A) : A -> Prop :=
  | eq_refl : eq x x.

  Notation "x = y" := (eq x y) : type_scope.

End Eq.

(** Coq has built in tactics to deal with equalities.

    We have already seen [rewrite H] and [rewrite H in H'] that
    rewrite the hypothesis [H] in the goal or the hypothesis [H']
    respectively.

    The tactic [reflexivity] establishes a goal of the form [x = x].
    It is the same as applying the constructor [eq_refl].

    Two other useful tactics when working with equalities are
    [discriminate] and [congruence]. *)


(** The [discriminate] tactic proves any goal from an assumption
    stating that two structurally different terms are equal. *)

Lemma eq_false : forall x, S x = 0 -> False.
Proof.
  intros x H.
  discriminate.
  (* [inversion H] would also prove the goal. *)
Qed.


(** The [congruence] tactic automatically proves a goal by applying
    the following rules of reasoning:

    - [x = x] (reflexivity)

    - if [x = y] and [P x] then [P y]

    - [~ (C1 x1 ... xn = C2 y1 ... ym)] when [C1 <> C2]

    - If [C x1 ... xn = C y1 ... yn] then [x1 = y1] ... [xn = yn] (injectivity of constructors)
*)                       
                       
Lemma congurence_example_1 :
  forall n m p, S n = S m -> n + p = m + p.
Proof.
  intros. (* intros without arguments will pick arbitrary names *)
  congruence.
Qed.

Lemma congurence_example_2 :
  forall n m p, S n = S m -> S m = S p -> n = p.
Proof.
  intros. (* intros without arguments will pick arbitrary names *)
  congruence.
Qed.

(** *** Existential Quantification *)

Module Exists.

  (** To prove that [exists x, P x] for a predicate [P : A -> Prop],
      we must provide an [x] and a proof of [P x]. *)
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall a : A, P a -> ex A P.


  (** Some convenient notation. *)
  Notation "'exists' x , p" :=
    (ex _ (fun x => p))
      (at level 200, x binder, right associativity) : type_scope.

End Exists.

Lemma fourtytwo_is_even_1 :
  exists (n : nat), 42 = n + n.
Proof.
  apply ex_intro with (x := 21).

  reflexivity.
Qed.

Lemma fourtytwo_is_even_2 :
  exists (n : nat), 42 = n + n.
Proof.
  (* There is a more intuitive way to prove this *)

  (* Use the tactic [exist] to provide the evidence *)
  exists 21. (* This is equivalent to [apply ex_intro with (x := 21).] *)

  (* prove the proposition about the evidence *)
  reflexivity.
Qed.


Lemma exists_inv :
  forall m,
    (exists (n : nat), n + 1 = m) ->
    (exists (n : nat), m = n + 1).
Proof.
  intros m H1.
  (* if we have an hypothesis with an existential quantifier
     we can use [inversion] to obtain the evidence and a proof
     that the predicates holds on the evidence. *)
  inversion H1 as [n Hn].

  exists n.
  rewrite Hn. reflexivity.
Qed.


(** *** Existential Variables *)

(** Earlier, we used specialize to explicitly the quantifiers of
    hypotheses and lemmas in order to apply them to a specific goal.

    Coq let's us avoid doing this with a number of helpful tactics
    that let us delay instantiation of quantified variables. These
    tactics are [eapply], [eauto], [eexists] and [econstructor]. Let's
    see how they work in practice.

    We will revisit the corollary [even_or_odd]. *)


Corollary even_or_odd_again_1 : forall x, Even x \/ Odd x.
Proof.
  intros.
  (* We want to use the previous proof with [n = x] and [m = x]. Now
     we want to omit explicitly providing the variables. *)


  Fail apply even_or_odd_aux.
  (* The above tactic fails with the message:

      [Unable to find an instance for the variable n.]

      Indeed, the theorem states:

      [forall n m : nat, m <= n -> Even m \/ Odd m]

      There is no way for Coq to know with what we want to instantiate
      [n] with.

      We can use [eapply].  *)

  eapply even_or_odd_aux.

  (* Now the goal is [x <= ?n].  The strange variable name [?n]
      signifies a yet uninstantiated variable. This is called
      existential variable.

      We know that we want [?n] to be [x].

      We will apply the theorem [Nat.le_refl: forall n : nat, n <= n]
      that states that [<=] is reflexive. This will automatically
      instantiate [?n] with [x].  *)

  apply Nat.le_refl.
Qed.


(** Let's see some more examples of tactics dealing with existential
variables. *)

Lemma eapply_example :
  forall (P Q R : nat -> Prop),
    (forall n m, P (m + n) -> Q m -> R n) ->
    P 7 ->
    Q 4 ->
    R 3.
Proof.
  intros P Q R Hyp HP HQ.
  Fail apply Hyp. (* Fails with: Unable to find an instance for the variable m. *)

  eapply Hyp.

  (* Now it's easier to solve the goal 2 first, so we can unify
     [?m]. Coq lets us select the goal we want to work with with the
     syntax [N:{ ... }]. Inside the braces we put the proof of the
     goal. *)

  2:{ Fail assumption.  eassumption. (* [eassumption] can deal with existential variables. *) }
  simpl.
  assumption.

Qed.

Lemma eauto_example :
  forall (P : nat -> nat -> Prop) (Q R : nat -> Prop),
    (forall n m, P m n -> Q m -> R n) ->
    P 4 3 ->
    Q 4 ->
    R 3.
Proof.
  intros P Q R Hyp HP HQ.
  (* The proof of this lemma consists only of [eapply] and
    [eassumption]. We want to use [auto] to solve this, but [auto]
    does not deal with existential variables. Coq provides [eauto]
    that will try to solve a goal using [eapply], [reflexivity],
    [eexists], [split], [left], [right]. *)

  auto. (* Does nothing *)

  eauto. (* Solves the goal *)
Qed.


Lemma eexists_example :
  forall (P : nat -> Prop), P 42 -> exists n, P n.
Proof.
  intros P H42.

  (* Instead of providing immediately the witness, we can use
     [eexists] *)
  eexists.
  eassumption.
Qed.


Lemma econstructor_example :
  forall (P : nat -> Prop), P 42 -> exists n, P n.
Proof.
  intros P H42.

  (* Now we want to prove the existential by applying the constructor
     of [ex] instead of using [eexists]. *)

  Fail constructor.  (* Fails with: Unable to find an instance for the
  variable x. *)

  econstructor.

  eassumption.
Qed.


(** ** Induction on the Derivation of Logical Propositions *)

(** Just as we can do induction on terms of inductive types, we can do
    induction over derivations of inductive propositions. The form of
    the induction principle is similar in both cases.

    Say that we want to prove that an inductive proposition [Q x1 ... xn]
    with zero or more parameters [x1], ..., [xn],  implies [P x1 ... xn].

    To show this we may proceed by induction on the way that the proof of [Q x1 ... xn]
    was constructed, i.e. induction on its derivation.

    To show that [forall x1 .. xn, Q x1 ... xn -> P x1 ... xn] we must show the following.

    1) Base cases: For each base derivation rule of the form
<<
           H1 ... Hm
       -----------------
          Q t1 ... tn
>>

       - assume that [H1], ..., [Hm]

       - prove [P t1 ... tn]


    2) Inductive cases: For each inductive derivation rule of the form
<<
           H1 ... Hm
       -----------------
         Q t1 ... tn
>>

       - assume that [H1], ..., [Hm]
       - for each [Hi] that is a is subderivation showing [Q w1 ... wn]
         also assume that [P w1 ... wn] (inductive hypotheses)
       - prove [P t1 ... tn]
*)

(** Induction over derivations will be better understood with an
    example. We write an inductive relation [le : nat -> nat -> Prop]
    that is true if and only iff the first natural number is less than
    or equal to the second. *)

Module le.
  Inductive le : nat -> nat -> Prop :=
  | leO : forall m, le 0 m
  | leS : forall n m, le n m -> le (S n) (S m).

  (** We can prove or disprove the relation for certain arguments. *)

  Example leq_3_5:
    le 3 5.
  Proof.
    apply leS.
    apply leS.
    apply leS.
    apply leO.
    (* or just [repeat constructor] *)
  Qed.


  Example not_leq_5_2:
    ~ le 5 3.
  Proof.
    intros Habsurd.
    (* invert the derivation until no constructor applies *)

    inversion Habsurd as [ | n m Habsurd' Heq1 Heq2 ]; subst.
    inversion Habsurd' as [ | n m Habsurd'' Heq1 Heq2 ]; subst.
    inversion Habsurd'' as [ | n m Habsurd''' Heq1 Heq2 ]; subst.
    inversion Habsurd'''.
  Qed.

  (** Coq has generated an induction principle for this inductive
      relation. *)

  Check le_ind.

  (** Let's examine its type. *)

  Definition le_ind_type :=
    forall P : nat -> nat -> Prop,

      (* Premise (base case):
         If [le n m] is derived with [leO], therefore [n = 0]),
         then show [P 0 m].  *)
      (forall m : nat, P 0 m) ->

      (* Premise (inductive case):
         If [le n m] is derived with [leS]
         <<

                le n' m'
          --------------------(leS)
             le (S n') (S m')
         >>
         then assuming that [le n' m'], [P n' m'] (inductive hypothesis), [n = S n'], [m = S n']

         show [le (S n') (S m')]. *)
    (forall n' m' : nat, le n' m' -> P n' m' -> P (S n') (S m')) ->

    (* Conclusion: for all [n] [m], [le n m] implies [P n m] *)
    forall n m : nat, le n m -> P n m.


  (** We will use induction on the derivation to show that [le] is transitive. *)

  Lemma le_transitive :
    forall n m k,
      le n m ->
      le m k ->
      le n k.
  Proof.
    intros n m k Hle. revert k.
    induction Hle as [| n' m' HP IHle Heq1 Heq2];
      intros k Hle'.
    - apply leO.
    - inversion Hle'; subst. (* [Hle'] can only be derived by [leS] *)

       apply leS.
       apply IHle. assumption.
  Qed.

  (** Note: In this case we can also do the proof by induction on [n]. *)

End le.
