Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.sorted_lists.
Require Import Casper.validators.
Require Import Casper.consensus_values.
Require Import Casper.FullStates.states.
Require Import Casper.FullStates.messages.
Require Import Casper.FullStates.add_in_sorted.
Require Import Casper.FullStates.in_state.
Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.locally_sorted.

(****************************)
(** Fault Weight of States **)
(****************************)

(*************************)
(* equivocating_messages *)
(*************************)

Definition equivocating_messages (msg1 msg2 : message) : Prop :=
  match msg1, msg2 with
    (c1, v1, j1), (c2, v2, j2) =>
      v1 = v2 /\
      (c1 <> c2 \/ j1 <> j2) /\
      not (in_state (c1,v1,j1) j2) /\
      not (in_state (c2,v2,j2) j1)
  end.

Lemma equivocating_messages_dec : forall msg1 msg2,
  equivocating_messages msg1 msg2 \/ ~ equivocating_messages msg1 msg2.
Proof.
  intros.
  destruct msg1 as [(c1,v1) j1].
  destruct msg2 as [(c2,v2) j2].
  destruct (v_eq_dec v1 v2); subst.
  - destruct (c_eq_dec c1 c2); subst.
    + destruct (state_eq_dec j1 j2); subst.
      * right. unfold not. intros.
        inversion H. destruct H1. destruct H1. contradiction. contradiction.
      * destruct (in_state_dec (c2,v2,j1) j2).
        { right. unfold not. intros. inversion H1. destruct H3. destruct H4. contradiction. }
        { destruct (in_state_dec (c2,v2,j2) j1). 
           {right. unfold not. intros. inversion H2. destruct H4. destruct H5. contradiction. }
           { left. constructor; try reflexivity. split.
              { right. assumption. }
              { split; assumption. }
           }
        }
    + destruct (in_state_dec (c1,v2,j1) j2).
      * right. unfold not. intros. inversion H1. destruct H3. destruct H4. contradiction.
      * destruct (in_state_dec (c2,v2,j2) j1).
        { right. unfold not. intros. inversion H2. destruct H4. destruct H5. contradiction. }
        { left. constructor; try reflexivity. split.
          { left. assumption. }
          { split; assumption. }
        }
 - right. unfold not. intros. inversion H0. contradiction.
Qed.

(******************************)
(* equivocating_message_state *)
(******************************)

(* work in progress *)

Inductive equivocating_message_state : message -> state -> Prop :=
  | equivocating_message_state_head: forall msg1 msg2 sigma,
      equivocating_messages msg1 msg2 ->
      equivocating_message_state msg1 (next msg2 sigma)
  | equivocating_message_state_tail: forall msg1 msg2 sigma,
      ~ equivocating_messages msg1 msg2 ->
      equivocating_message_state msg1 sigma ->
      equivocating_message_state msg1 (next msg2 sigma)
 .

Lemma equivocating_message_state_empty : forall msg,
  ~ equivocating_message_state msg Empty.
Proof.
  unfold not. intros.
  inversion H
  ; subst
  ; apply no_confusion_next_empty in H0
  ; inversion H0.
Qed.


Lemma equivocating_message_state_next : forall msg1 msg2 sigma,
  equivocating_message_state msg1 sigma ->
  equivocating_message_state msg1 (next msg2 sigma).
Proof.
  intros.
  destruct (equivocating_messages_dec msg1 msg2).
  - apply equivocating_message_state_head. assumption.
  - apply equivocating_message_state_tail; assumption.
Qed.


Lemma equivocating_message_state_dec : forall msg sigma,
  equivocating_message_state msg sigma \/ ~ equivocating_message_state msg sigma.
Proof.
  intros.
  induction sigma.
  - right. apply equivocating_message_state_empty. 
  - rewrite add_is_next.
    destruct (equivocating_messages_dec msg (c,v,sigma1)).
    + left. apply equivocating_message_state_head. assumption.
    + inversion IHsigma2.
      * left. apply equivocating_message_state_tail; assumption.
      * right. unfold not. intros. 
        inversion H1; subst
        ; rewrite add_is_next in H2; apply no_confusion_next in H2; destruct H2; subst
        ; contradiction. 
Qed.


Lemma equivocating_message_state_sorted_subset : forall sigma sigma' msg,
  sorted_subset sigma sigma' ->
  equivocating_message_state msg sigma ->
  equivocating_message_state msg sigma'.
Proof.
  intros. generalize dependent msg.
  induction H; intros.
  - apply equivocating_message_state_empty in H0. inversion H0.
  - inversion H0; subst
    ; apply no_confusion_next in H1
    ; destruct H1; subst.
    + apply equivocating_message_state_head. assumption.
    + apply IHsorted_subset in H4.
      apply equivocating_message_state_tail; assumption.
  - apply IHsorted_subset in H0.
    apply equivocating_message_state_next. assumption.
Qed.

(***************************)
(* equivocating_validators *)
(***************************)

Inductive equivocating_validators : state -> list V -> Prop :=
  | equivocating_validators_Empty : equivocating_validators Empty []
  | equivocating_validators_Next : forall c v j sigma vs vs',
      equivocating_message_state (c, v, j) sigma ->
      equivocating_validators sigma vs ->
      @add_in_sorted_list V v_lt v vs vs' ->
      equivocating_validators (next (c, v, j) sigma) vs'
  | equivocating_validators_Next' : forall msg sigma vs,
      ~ equivocating_message_state msg sigma ->
      equivocating_validators sigma vs ->
      equivocating_validators (next msg sigma) vs
  .

Lemma equivocating_validators_empty : forall vs,
  equivocating_validators Empty vs ->
  vs = [].
Proof.
  intros.
  inversion H; subst.
  - reflexivity.
  - apply no_confusion_next_empty in H0. inversion H0.
Qed.

Lemma equivocating_validators_fold_nonnegative : forall vs,
  (0 <= fold_right (fun r1 r2 : R => r1 + r2) 0 (map weight vs))%R.
Proof.
  intros.
  induction vs; simpl.
  - apply Rle_refl.
  - rewrite <- (Rplus_0_l 0).
    assert (H := weight_positive a).
    apply Rlt_le in H.
    apply Rplus_le_compat
    ; try rewrite Rplus_0_l
    ; assumption.
Qed.

Lemma equivocating_validators_functional : forall sigma vs1 vs2,
  equivocating_validators sigma vs1 ->
  equivocating_validators sigma vs2 ->
  vs1 = vs2
  .
Proof.
  intros. 
  generalize dependent vs2.
  induction H; intros.
  - apply equivocating_validators_empty in H0; subst. reflexivity.
  - inversion H2; subst.
    + apply IHequivocating_validators in H9; subst.
      apply (add_in_sorted_list_functional V v_compare v_compare_strict_order v vs0 vs' vs2 H1 H10).
    + rewrite add_is_next in H3. apply no_confusion_next in H3. destruct H3; subst.
      contradiction.
  - inversion H1; subst.
    + symmetry in H3. apply no_confusion_next_empty in H3. inversion H3.
    + rewrite add_is_next in H2. apply no_confusion_next in H2. destruct H2; subst.
      contradiction.
    + apply no_confusion_next in H2. destruct H2; subst.
      apply IHequivocating_validators in H4. assumption.
Qed.
    
Lemma equivocating_validators_total : forall sigma,
  exists vs, equivocating_validators sigma vs.
Proof.
  intros. induction sigma.
  - exists nil. constructor.
  - rewrite add_is_next.
    destruct IHsigma2.
    destruct (equivocating_message_state_dec (c,v,sigma1) sigma2).
    + assert (Hvs := add_in_sorted_list_total V v_compare v x v_compare_strict_order).
      destruct Hvs.
      exists x0.
      apply (equivocating_validators_Next c v sigma1 sigma2 x x0 H0 H H1).
    + exists x.
      apply (equivocating_validators_Next' (c,v,sigma1) sigma2 x H0 H).
Qed.

Lemma equivocating_validators_sorted_subset : forall sigma sigma' vs vs',
  sorted_subset sigma sigma' ->  
  equivocating_validators sigma vs ->
  equivocating_validators sigma' vs' ->
  incl vs vs'.
Proof.
  intros. 
  generalize dependent vs. generalize dependent vs'.
  induction H; intros.
  - apply equivocating_validators_empty in H0; subst. 
    unfold incl. intros. inversion H.
  - inversion H0; subst.
    + unfold incl. intros. inversion H2.
    + rewrite add_is_next in H2.
      destruct msg as [(mc,mv) mj].
      apply no_confusion_next in H2. destruct H2; subst. 
      inversion H2; subst. 
      inversion H1; subst.
      * apply (IHsorted_subset _ H12) in H4.
        unfold incl. intros.
        apply (add_in_sorted_list_in _ _ _ _ H5) in H6.
        destruct H6; subst.
        apply add_in_sorted_list_head in H13. assumption.
        apply add_in_sorted_list_tail in H13.
        apply (incl_tran H4) in H13.
        unfold incl in H13.
        apply H13. assumption.
      * rewrite add_is_next in H6.
        destruct msg as [(mc',mv') mj'].
        apply no_confusion_next in H6. destruct H6; subst. 
        inversion H6; subst.
        apply (equivocating_message_state_sorted_subset _ _ _ H) in H3.
        contradiction.
    + apply no_confusion_next in H2. destruct H2; subst.
      inversion H1; subst.
      * symmetry in H5.
        apply no_confusion_next_empty in H5. inversion H5.
      * rewrite add_is_next in H2.
        apply no_confusion_next in H2. destruct H2; subst.
        apply (IHsorted_subset _ H6) in H4.
        apply add_in_sorted_list_tail in H7.
        apply (incl_tran H4 H7).
      * apply no_confusion_next in H2. destruct H2; subst.
        apply (IHsorted_subset _ H6 _ H4).
  - inversion H1; subst.
    + symmetry in H3. apply no_confusion_next_empty in H3. inversion H3.
    + rewrite add_is_next in H2. 
      apply no_confusion_next in H2. destruct H2; subst.
      apply (IHsorted_subset _ H4) in H0.
      apply add_in_sorted_list_tail in H5.
      apply (incl_tran H0 H5).
    + apply no_confusion_next in H2. destruct H2; subst.
      apply (IHsorted_subset _ H4 _ H0).
Qed.


Lemma equivocating_validators_fold_subset : forall vs vs' sigma sigma',
  equivocating_validators sigma vs ->
  equivocating_validators sigma' vs' ->
  incl vs vs' ->
  (fold_right (fun r1 r2 : R => r1 + r2) 0 (map weight vs) 
    <=
   fold_right (fun r1 r2 : R => r1 + r2) 0 (map weight vs')
  )%R.
Proof.
  Admitted.
(*
  intros. generalize dependent vs'.
  induction vs; intros; simpl.
  - apply equivocating_validators_fold_nonnegative.
  - apply (incl_tl a) in H.
    assert (H1 : incl vs (a :: vs)).
    + apply incl_tl. apply incl_refl.
    + apply (incl_tran H1) in H.
      apply IHvs in H. simpl in H.
*)


(**********************)
(* fault_weight_state *)
(**********************)

Inductive fault_weight_state : state -> R -> Prop :=
  fault_weight_state_intro : forall sigma vs,
    equivocating_validators sigma vs ->
    fault_weight_state sigma (fold_right (fun r1 r2 => (r1 + r2)%R) 0%R (map weight vs))
  .

Lemma fault_weight_state_empty : forall r,
  fault_weight_state Empty r ->
  (r = 0)%R.
Proof.
  intros.
  inversion H; subst.
  apply equivocating_validators_empty in H0; subst.
  simpl. reflexivity.
Qed.

Lemma fault_weight_state_empty' : 
  fault_weight_state Empty 0.
Proof.
  intros.
  destruct (equivocating_validators_total Empty).
  apply fault_weight_state_intro in H as H1.
  apply equivocating_validators_empty in H; subst.
  simpl in H1. assumption.
Qed.

Lemma fault_weight_state_nonnegative : forall sigma r,
  fault_weight_state sigma r ->
  (0 <= r)%R.
Proof.
  intros.
  induction H.
  apply equivocating_validators_fold_nonnegative.
Qed.


Lemma fault_weight_state_functional : forall sigma r1 r2,
  fault_weight_state sigma r1 ->
  fault_weight_state sigma r2 ->
  r1 = r2
  .
Proof.
  intros.
  generalize dependent r2.
  induction H; intros.
  inversion H0; subst.
  apply (equivocating_validators_functional _ _ _ H) in H1; subst.
  reflexivity.
Qed.

Lemma fault_weight_state_total : forall sigma,
  exists r, fault_weight_state sigma r.
Proof.
  intros. induction sigma.
  - exists 0%R. apply fault_weight_state_empty'.
  - destruct (equivocating_message_state_dec (c,v,sigma1) sigma2)
    ; rewrite add_is_next.
    + destruct (equivocating_validators_total sigma2).
      assert (Hx := add_in_sorted_list_total V v_compare v x v_compare_strict_order). destruct Hx.
      apply (equivocating_validators_Next c v sigma1 sigma2 x x0 H H0) in H1.
      apply fault_weight_state_intro in H1.
      exists (fold_right (fun r1 r2 : R => (r1 + r2)%R) 0%R (map weight x0)).
      assumption.
    + destruct (equivocating_validators_total sigma2).
      apply (equivocating_validators_Next' (c,v,sigma1) sigma2 x H) in H0.
      apply fault_weight_state_intro in H0.
      exists (fold_right (fun r1 r2 : R => (r1 + r2)%R) 0%R (map weight x)).
      assumption.
Qed.

(** Needed for the proof of common-futures theorem **)

Lemma fault_weight_state_sorted_subset : forall sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  inversion H0; subst.
  inversion H1; subst.
  assert (H4 := equivocating_validators_sorted_subset _ _ _ _ H H2 H3).
  apply (equivocating_validators_fold_subset _ _ _ _ H2 H3 H4).
Qed.

Corollary fault_weight_state_add : forall msg sigma sigma' r1 r2,
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  apply (add_in_sorted_sorted_subset _ _ _ H H0) in H1.
  apply (fault_weight_state_sorted_subset sigma sigma' r1 r2); assumption.
Qed.
