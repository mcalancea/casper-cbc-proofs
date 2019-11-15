From Casper
Require Import vlsm_preamble.

Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

Lemma exist_eq
  {X}
  (P : X -> Prop)
  (a b : {x : X | P x})
  : a = b <-> proj1_sig a = proj1_sig b.
Proof.
  destruct a as [a Ha]; destruct b as [b Hb]; simpl.
  split; intros Heq.
  - inversion Heq. reflexivity.
  - subst. apply f_equal. apply proof_irrelevance.
Qed.

Lemma DepEqDec
  {X}
  (Heqd : EqDec X)
  (P : X -> Prop)
  : EqDec {x : X | P x}.
Proof.
  intros [x Hx] [y Hy].
  specialize (Heqd x y).
  destruct Heqd as [Heq | Hneq].
  - left. subst. apply f_equal. apply proof_irrelevance.
  - right.  intros Heq. apply Hneq. inversion Heq. reflexivity.
Qed.

