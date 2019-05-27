Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Reals.

Require Import List.
Import ListNotations.

Inductive fold {A:Type} (rel : A -> A -> A -> Prop) : list A -> A -> Prop :=
  | fold_singleton : forall a, fold rel [a] a
  | fold_cons : forall a b l fab fa,
    fold rel (b :: l) fa ->
    rel a fa fab ->
    fold rel (a :: b :: l) fab
  .

Lemma Forall_tail : forall A (a:A) l P,
  Forall P (a :: l) -> Forall P l.
Proof.
  intros. inversion H. assumption.
Qed.

Class TotalOrder {A} (lt : relation A) : Prop :=
   totality : forall c1 c2, c1 = c2 \/ lt c1 c2 \/ lt c2 c1.

Class Commutative {A} (op : A -> A -> A -> Prop) : Prop :=
   commutativity : forall c1 c2 c12, op c1 c2 c12 -> op c2 c1 c12.

Class EqualityFn {A} (eqb : A -> A -> bool) : Prop :=
    equality_fn : forall x y, eqb x y = true <-> x = y.

Class RelationFn {A} (r : relation A) (rb : A -> A -> bool) : Prop :=
  relation_fn : forall x y, r x y <-> rb x y = true.

Theorem strict_total_order_eq_dec : forall (A : Type) (rel : A -> A -> Prop),
  StrictOrder rel ->
  TotalOrder rel ->
  forall x y : A, x = y \/ x <> y.
Proof.
  intros.
  destruct H.
  destruct (H0 x y) as [Heq | [H | H]]
  ; try (left; assumption)
  ; try (right; intro; subst; apply (StrictOrder_Irreflexive _ H); assumption)
  .
Qed.

(** This lemma is needed in fault_weight_state_backwards **)
Lemma Rplusminus_assoc : forall r1 r2 r3, 
  (r1 + r2 - r3)%R = (r1 + (r2 - r3))%R.
Proof.
  intros. unfold Rminus.
  apply Rplus_assoc.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplusminus_assoc_r : forall r1 r2 r3, 
  (r1 - r2 + r3)%R = (r1 + (- r2 + r3))%R.
Proof.
  intros. unfold Rminus.
  apply Rplus_assoc.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_opp_l : forall r, (Ropp r + r)%R = 0%R.
Proof.
  intros.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_ge_reg_neg_r : forall r1 r2 r3,
  (r2 <= 0)%R -> (r3 <= r1 + r2)%R -> (r3 <= r1)%R.
Proof.
  intros.
  apply Rge_le.
  apply Rle_ge in H.
  apply Rle_ge in H0.
  apply (Rplus_ge_reg_neg_r r1 r2 r3 H H0).
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rminus_lt_r : forall r1 r2,
  (0 <= r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  apply Rplus_le_compat_l. 
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  assumption.
Qed.