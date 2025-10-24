Parameter (Prog : Type)
  (Result : Type)
  (comp : Prog -> Prog)
  (sem : Prog -> Result -> Prop).


(* Definition: the transformation comp is correct *)
Definition correct := 
  forall p v, sem p v <-> sem (comp p) v.

(* We assume that for the language in question if there is no result
   that the program evaluates then the program _diverges_ (i.e., loops
   infinitely).

   Note that, in general, it is not necessary: if there is no [x] such
   that [sem p x] the program may also be in a "stuck state".  *)
Definition div (p : Prog) := ~ exists x, sem p x.

(* We want to know that the [p] diverges if and only if the [comp p]
   diverges. *)
Definition div_preserved := 
  forall p, div p <-> div (comp p).

(* We show that it suffices to prove [correct] in order to show
   [div_preserved]. *)
Theorem correct_div_preserved :
  correct -> div_preserved.
Proof.
  intros Hcor p; split; intros Hdiv [v Heval];
    eapply Hcor in Heval; eauto.
Qed.

(* Definition: [sem] is deterministic *)
Definition deterministic := forall x y z, sem x y -> sem x z -> y = z.

(* How a deterministic program we can prove the following in order to
   derive [correct]. *)
Definition det_correct := 
  (forall p v, sem p v -> sem (comp p) v) /\
    (forall p, div p -> div (comp p)).

Axiom EM : forall P, P \/ ~ P.

Theorem det_correct_correct :
  deterministic -> det_correct -> correct. 
Proof.
  intros Hdet [Heval Hdiv] p v. split; intros Heval'; eauto.
  
  destruct (EM (exists v, sem p v)) as [[v' Hevalp] | Hnot].

  - assert (Heq : v = v').
    { apply Heval in Hevalp. eapply Hdet; eauto. }
    subst; eauto. 

  - apply Hdiv in Hnot. exfalso; eauto.
Qed.

