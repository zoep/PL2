From Stdlib Require Import Lists.List Arith.Arith Lia Sorting.Permutation.
Import ListNotations.

(** * Verified Merge Sort *)

(** Can we write an efficient sorting function in Rocq and prove it
    correct? We implement merge sort, which performs O(n log n)
    comparisons, and prove that it returns a sorted permutation of its
    input.

    The interesting part is termination. Rocq only accepts structurally
    recursive functions, and neither [merge] nor merge sort is
    structurally recursive in the obvious way. *)


(** ** Specification *)

(** A sorting function must return, for every input [l], a list that

    - is sorted, and

    - is a permutation of [l] (same elements, same multiplicities).

    A list is sorted if every element is at most the next one. *)

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_one : forall x, sorted [x]
| sorted_cons : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

(** For permutations we use the inductive definition of the standard
    library. *)

Print Permutation.

(** Why do we need both conditions? Find a function that satisfies only
    the first one, and a function that satisfies only the second one. *)


(** ** Merging Sorted Lists *)

(** The textbook definition of [merge] is rejected: *)

Fail Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x :: l1', y :: l2' =>
      if x <=? y then x :: merge l1' l2 else y :: merge l1 l2'
  end.

(** The first recursive call shrinks [l1] and the second shrinks [l2],
    but Rocq needs one argument that shrinks in _every_ recursive call.
    The function does terminate, because the pair [(l1, l2)] decreases
    lexicographically. We express this with a nested fixpoint: the outer
    [merge] recurses on [l1], and, for a fixed [l1 = x :: l1'], the inner
    [merge_aux] recurses on [l2]. *)

Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | x :: l1' =>
      let fix merge_aux (l2 : list nat) : list nat :=
        match l2 with
        | [] => l1
        | y :: l2' =>
            if x <=? y then x :: merge l1' l2 else y :: merge_aux l2'
        end
      in merge_aux l2
  end.

Compute merge [1; 4; 6] [2; 3; 5; 7].

(** Prints: [= [1; 2; 3; 4; 5; 6; 7] : list nat] *)

(** On [merge (x :: l1) (y :: l2)], [simpl] displays the inner [fix] in
    the [else] branch instead of [merge (x :: l1) l2]. So we state the
    equation we want once, and use it with [rewrite]. It holds by
    [reflexivity]: the two sides are equal by computation. *)

Lemma merge_cons : forall x l1 y l2,
  merge (x :: l1) (y :: l2) =
  if x <=? y then x :: merge l1 (y :: l2) else y :: merge (x :: l1) l2.
Proof. reflexivity. Qed.


(** ** Splitting a List *)

(** [halve] deals the elements of a list into two piles, like a card
    dealer: it halves the tail, swaps the two piles, and puts the head
    on the first one. *)

Fixpoint halve (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | x :: l' => let (l1, l2) := halve l' in (x :: l2, l1)
  end.

Compute halve [1; 2; 3; 4; 5].

(** Prints: [= ([1; 3; 5], [2; 4]) : list nat * list nat] *)


(** ** Merge Sort *)

(** Merge sort splits the list in two, sorts the two halves recursively,
    and merges the results. For lists with at least two elements, we put
    the first two elements [x] and [y] in different halves (this is
    exactly what [halve (x :: y :: l')] does). Again, Rocq rejects the
    definition: *)

Fail Fixpoint msort (l : list nat) : list nat :=
  match l with
  | [] | [_] => l
  | x :: y :: l' =>
      let (l1, l2) := halve l' in
      merge (msort (x :: l1)) (msort (y :: l2))
  end.

(** [x :: l1] and [y :: l2] are not subterms of [l]. Yet [msort]
    terminates: both lists are shorter than [l], since each one misses
    [x] or [y].

    We use the fuel technique of the Imp interpreter ([cinterp]): an
    extra argument that shrinks in every recursive call. Unlike there,
    we know how much fuel suffices: [length l], since every recursive
    call is on a strictly shorter list. *)

Fixpoint msort_fuel (fuel : nat) (l : list nat) : list nat :=
  match l with
  | [] | [_] => l
  | x :: y :: l' =>
      match fuel with
      | O => l (* out of fuel: unreachable when [length l <= fuel] *)
      | S fuel' =>
          let (l1, l2) := halve l' in
          merge (msort_fuel fuel' (x :: l1)) (msort_fuel fuel' (y :: l2))
      end
  end.

Definition msort (l : list nat) : list nat := msort_fuel (length l) l.

Example msort_example : msort [5; 3; 8; 1; 9; 2; 7] = [1; 2; 3; 5; 7; 8; 9].
Proof. reflexivity. Qed.

(** Why is it efficient? [halve] splits evenly, so the recursion is
    about log2 n levels deep, and each level does O(n) work in [halve]
    and [merge]: O(n log n) in total. The fuel is just a counter. *)


(** ** Correctness *)

(** *** The Output Is a Permutation of the Input *)

(** [Permutation] is an equivalence relation, and the standard library
    proves that [cons] and [++] respect it. This lets us use [rewrite],
    [reflexivity] and [symmetry] with [Permutation], just as with [=]
    (generalized rewriting). *)

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [| x l1 IH1]; intros l2.
  - reflexivity.
  - induction l2 as [| y l2 IH2].
    + simpl. rewrite app_nil_r. reflexivity.
    + rewrite merge_cons. destruct (x <=? y).
      * simpl. apply perm_skip. apply IH1.
      * rewrite <- IH2. symmetry. apply Permutation_middle.
Qed.

Lemma halve_perm : forall l l1 l2, halve l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  induction l as [| x l IH]; intros l1 l2 H; simpl in H.
  - (* [as <- <-] replaces [l1] and [l2] by their values in [H] *)
    injection H as <- <-. reflexivity.
  - (* [destruct] replaces [halve l] in [IH] too *)
    destruct (halve l) as [l1' l2']. injection H as <- <-. simpl.
    apply perm_skip. rewrite Permutation_app_comm. apply IH. reflexivity.
Qed.

(** Note that this holds for any amount of fuel. *)

Lemma msort_fuel_perm : forall fuel l, Permutation l (msort_fuel fuel l).
Proof.
  induction fuel as [| fuel IH]; intros [| x [| y l]]; simpl; try reflexivity.
  (* Only the recursive case is left. *)
  destruct (halve l) as [l1 l2] eqn:Hh.
  rewrite <- merge_perm, <- !IH. simpl.
  (* Goal: [Permutation (x :: y :: l) (x :: l1 ++ y :: l2)] *)
  apply perm_skip, Permutation_cons_app, halve_perm, Hh.
Qed.


(** *** The Output Is Sorted *)

(** If [x] can be put in front of both [l1] and [l2], then it can be put
    in front of their merge. *)

Lemma merge_sorted_cons : forall l1 l2 x,
  sorted (x :: l1) -> sorted (x :: l2) -> sorted (x :: merge l1 l2).
Proof.
  induction l1 as [| a l1 IH1]; intros l2.
  - intros x _ H2. exact H2.
  - induction l2 as [| b l2 IH2]; intros x H1 H2.
    + exact H1.
    + inversion H1; subst. inversion H2; subst.
      rewrite merge_cons. destruct (a <=? b) eqn:Hab.
      * apply Nat.leb_le in Hab.
        apply sorted_cons; [assumption |].
        apply IH1; [assumption | apply sorted_cons; assumption].
      * apply Nat.leb_gt in Hab.
        apply sorted_cons; [assumption |].
        apply IH2; [apply sorted_cons; [lia | assumption] | assumption].
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  intros [| x l1] [| y l2] H1 H2; try assumption.
  rewrite merge_cons. destruct (x <=? y) eqn:Hxy.
  - apply Nat.leb_le in Hxy.
    apply merge_sorted_cons; [assumption | apply sorted_cons; assumption].
  - apply Nat.leb_gt in Hxy.
    apply merge_sorted_cons; [apply sorted_cons; [lia | assumption] | assumption].
Qed.

(** Unlike the permutation property, sortedness needs enough fuel:
    [msort_fuel 0 [2; 1] = [2; 1]]. *)

Lemma msort_fuel_sorted : forall fuel l, length l <= fuel -> sorted (msort_fuel fuel l).
Proof.
  induction fuel as [| fuel IH]; intros [| x [| y l]] Hlen; simpl in *.
  (* fuel = 0 *)
  - apply sorted_nil.
  - apply sorted_one.
  - lia. (* at least two elements, but no fuel *)
  (* fuel = S fuel *)
  - apply sorted_nil.
  - apply sorted_one.
  - destruct (halve l) as [l1 l2] eqn:Hh.
    (* The lengths of the halves add up to [length l]. *)
    apply halve_perm, Permutation_length in Hh. rewrite length_app in Hh.
    apply merge_sorted; apply IH; simpl; lia.
Qed.


(** *** The Main Theorem *)

Theorem msort_correct : forall l, sorted (msort l) /\ Permutation l (msort l).
Proof.
  intros l. split.
  - apply msort_fuel_sorted. lia.
  - apply msort_fuel_perm.
Qed.

(** No axioms were used: *)

Print Assumptions msort_correct.


(** ** Food for Thought *)

(** - _The specification determines the function_. Prove that
      [sorted l1 -> sorted l2 -> Permutation l1 l2 -> l1 = l2]. So every
      correct sorting function (e.g., insertion sort) is extensionally
      equal to [msort]. Which properties of [<=] does this proof need?

    - _Transitivity_. The sortedness proofs use only two facts
      about [<=]: [x <=? y = true -> x <= y] and
      [x <=? y = false -> y <= x]. Transitivity is never used, so they
      would work for any comparison [leb] with
      [leb x y = false -> leb y x = true]. Is this suspicious? (Hint:
      what does [sorted] say about elements that are not adjacent?)

    - _Balance_. The proofs about [msort] use only [halve_perm], so they
      still work if we replace [halve] by [fun l => (l, [])]. What does
      [msort] become, and how fast is it? How would you prove that
      [msort] performs O(n log n) comparisons? (Hint: count comparisons
      with the writer monad.)

    - _Stability_. Generalize [msort] to sort pairs by their first
      component, and sort [[(0, "a"); (1, "b"); (1, "c")]]. Do pairs with
      equal keys keep their order? How would you fix it?

    - _Fuel vs. well-founded recursion_. Rocq's general mechanism for
      non-structural recursion (used by [Program Fixpoint], [Function],
      and the Equations plugin) is also structural recursion: on a proof
      of the accessibility predicate [Acc] instead of a number. See
      [Print Fix_F]. What happens to [fuel] and to [Acc] proofs when we
      extract the code to OCaml?

    - _No fuel at all_. The standard library's [Stdlib.Sorting.Mergesort]
      is bottom-up: it keeps a stack of sorted runs of lengths 2^k that
      behaves like a binary counter, and every function is structurally
      recursive. *)
