
Class EqDec X :=
  eq_dec : forall x y : X, {x = y} + {x <> y}.


Lemma nat_eq_dec : EqDec nat.
Proof.
  unfold EqDec. induction x; destruct y.
  - left. reflexivity.
  - right. intros C; inversion C.
  - right. intros C; inversion C.
  - specialize (IHx y). destruct IHx as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intros Heq. inversion Heq. contradiction.
Qed.