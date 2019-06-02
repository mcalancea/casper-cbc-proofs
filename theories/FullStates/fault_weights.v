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

Lemma equivocating_validators_functional : forall sigma vs1 vs2,
  equivocating_validators sigma vs1 ->
  equivocating_validators sigma vs2 ->
  vs1 = vs2
  .
  Admitted.

Lemma equivocating_validators_total : forall sigma,
  exists vs, equivocating_validators sigma vs.
  Admitted.

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

Lemma equivocating_validators_empty : forall vs,
  equivocating_validators Empty vs ->
  vs = [].
Proof.
  intros.
  inversion H; subst.
  - reflexivity.
  - apply no_confusion_next_empty in H0. inversion H0.
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

Lemma fault_weight_state_functional : forall sigma r1 r2,
  fault_weight_state sigma r1 ->
  fault_weight_state sigma r2 ->
  r1 = r2
  .
  Admitted.

Lemma fault_weight_state_total : forall sigma,
  exists r, fault_weight_state sigma r.
  Admitted.


Lemma fault_weight_state_empty : forall r,
  fault_weight_state Empty r ->
  (r = 0)%R.
Proof.
  intros.
  inversion H; subst.
  apply equivocating_validators_empty in H0; subst.
  simpl. reflexivity.
Qed.

Lemma fault_weight_state_nonnegative : forall sigma r,
  fault_weight_state sigma r ->
  (0 <= r)%R.
Proof.
  intros.
  induction H.
  apply equivocating_validators_fold_nonnegative.
Qed.


(** Needed for theorem proof. Proofs for them are below **)

Lemma fault_weight_state_add : forall msg sigma sigma' r1 r2,
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
  Admitted.

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

(* 

Theorem fault_weight_msg_functional : forall msg1 msg2 r1 r2,
  fault_weight_msg msg1 msg2 r1 ->
  fault_weight_msg msg1 msg2 r2 ->
  r1 = r2.
Proof.
  intros. inversion H; subst; clear H; inversion H0; subst; clear H0
  ; try reflexivity
  ; try contradiction.
  - destruct H6; contradiction.
  - destruct H1; contradiction.
Qed.

Theorem fault_weight_msg_total : forall msg1 msg2,
  exists r, fault_weight_msg msg1 msg2 r.
Proof.
  intros.
  destruct msg1 as [(c1, v1) j1].
  destruct msg2 as [(c2, v2) j2].
  destruct (v_eq_dec v1 v2).
  - destruct (c_eq_dec c1 c2).
    + destruct (state_eq_dec j1 j2); subst.
      * exists 0%R. apply fault_weight_c_msg.
      * destruct (in_state_dec (c2, v2, j1) j2).
        { exists 0%R. apply fault_weight_msg1. assumption. }
        destruct (in_state_dec (c2, v2, j2) j1).
        { exists 0%R. apply fault_weight_msg2. assumption. }
        exists (weight v2).
        apply fault_weight_next; try assumption.
        right. assumption.
    + subst.
      destruct (in_state_dec (c1, v2, j1) j2).
      { exists 0%R. apply fault_weight_msg1. assumption. }
      destruct (in_state_dec (c2, v2, j2) j1).
      { exists 0%R. apply fault_weight_msg2. assumption. }
      exists (weight v2).
      apply fault_weight_next; try assumption.
      left. assumption.
  - exists 0%R. apply fault_weight_v_diff. assumption.
Qed.

Theorem fault_weight_msg_nonnegative : forall msg1 msg2 r,
  fault_weight_msg msg1 msg2 r ->
  (0 <= r)%R.
Proof.
  intros.
  inversion H
    ; subst
    ; try apply Rle_refl.
  left.
  apply weight_positive.
Qed.

(*******************************)
(* fauult_weight_message_state *)
(*******************************)

Inductive fault_weight_message_state : message -> state -> Prop :=
  | fault_weight_message_state_Next: forall msg1 msg2 sigma r1 r2,
      fault_weight_msg msg1 msg2 0 ->
      fault_weight_message_state msg1 sigma r ->
      fault_weight_message_state msg1 (next msg2 sigma) r%R
  | fault_weight_message_state_Next: forall msg1 msg2 sigma r1 r2,
      fault_weight_msg msg1 msg2 r ->
      (r > 0)%R ->
      fault_weight_message_state msg1 (next msg2 sigma) r%R
.

Lemma fault_weight_message_state_empty_zero : forall msg r,
  fault_weight_message_state msg Empty r ->
  r = 0%R.
Proof.
  intros.
  inversion H; subst; try reflexivity.
  apply no_confusion_next_empty in H0. inversion H0.
Qed.

Lemma fault_weight_message_state_nonnegative : forall msg sigma r,
  fault_weight_message_state msg sigma r ->
  (0 <= r)%R.
Proof.
  intros.
  induction H.
  - apply Rle_refl.
  - apply fault_weight_msg_nonnegative in H0.
    apply (Rplus_le_le_0_compat _ _ IHfault_weight_message_state H0).
Qed.

Theorem fault_weight_message_state_functional : forall msg sigma r1 r2,
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma r2 ->
  r1 = r2.
Proof.
  intros. 
  generalize dependent r2.
  induction H; intros.
  - apply fault_weight_message_state_empty_zero in H0; subst. reflexivity.
  - inversion H1; subst.
    * symmetry in H4. apply no_confusion_next_empty in H4. inversion H4.
    * apply no_confusion_next in H2; subst. destruct H2; subst.
      apply (fault_weight_msg_functional _ _ _ _ H0) in H5; subst.
      apply Rplus_eq_compat_r.
      apply IHfault_weight_message_state in H3.
      assumption.
Qed.

Theorem fault_weight_message_state_total : forall msg sigma,
  exists r, fault_weight_message_state msg sigma r.
Proof.
  intros.
  induction sigma.
  - exists 0%R. constructor.
  - rewrite add_is_next.
    destruct (fault_weight_msg_total msg (c,v,sigma1)) as [r2 H1].
    destruct IHsigma2 as [r1 H2].
    apply (fault_weight_message_state_Next _ _ _ _ _ H2) in H1.
    exists (r1 + r2)%R. assumption.
Qed.

Lemma fault_weight_message_state_backwards : forall msg msg' sigma r1 r2,
  fault_weight_msg msg msg' r1 ->
  fault_weight_message_state msg (next msg' sigma) r2 ->
  fault_weight_message_state msg sigma (r2 - r1)%R.
Proof.
  intros.
  inversion H0; subst.
  - symmetry in H3.
    apply no_confusion_next_empty in H3. inversion H3.
  - apply no_confusion_next in H1. destruct H1; subst.
    apply (fault_weight_msg_functional msg msg' r1 r3 H) in H4; subst.
    rewrite Rplusminus_assoc. unfold Rminus.
    rewrite Rplus_opp_r. rewrite Rplus_0_r.
    assumption.
Qed.

Lemma fault_weight_message_state_backwards_msg : forall msg msg' sigma r1 r2,
  fault_weight_message_state msg (next msg' sigma) r1 ->
  fault_weight_message_state msg sigma r2 ->
  fault_weight_msg msg msg' (r1 - r2)%R.
Proof.
  intros.
  inversion H; subst.
  - symmetry in H3.
    apply no_confusion_next_empty in H3. inversion H3.
  - apply no_confusion_next in H1. destruct H1; subst.
    apply (fault_weight_message_state_functional msg sigma r2 r0 H0) in H2; subst.
    rewrite Rplus_comm.
    rewrite Rplusminus_assoc. unfold Rminus.
    rewrite Rplus_opp_r. rewrite Rplus_0_r.
    assumption.
Qed.

Lemma fault_weight_message_state_sorted_subset : forall msg sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_message_state msg sigma r1 ->
  fault_weight_message_state msg sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  generalize dependent r1. generalize dependent r2.
  induction H; intros.
  + apply fault_weight_message_state_empty_zero in H0; subst.
    apply fault_weight_message_state_nonnegative in H1.
    assumption.
  + destruct (fault_weight_msg_total msg msg0) as [r H2].
    apply (fault_weight_message_state_backwards _ _ _ _ _ H2) in H1.
    apply (fault_weight_message_state_backwards _ _ _ _ _ H2) in H0.
    apply (IHsorted_subset _ H1) in H0.
    unfold Rminus in H0. apply Rplus_le_reg_r in H0.
    assumption.
  + destruct (fault_weight_msg_total msg msg0) as [r H2].
    apply (fault_weight_message_state_backwards _ _ _ _ _ H2) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply fault_weight_msg_nonnegative in H2.
    apply (Rminus_lt_r r2 r) in H2.
    apply (Rle_trans _ _ _ H0 H2).
Qed.

(**********************)
(* fault_weight_state *)
(**********************)

Inductive fault_weight_state : state -> R -> Prop :=
  | fault_weight_state_Empty: 
      fault_weight_state Empty 0
  | fault_weight_state_Next: forall msg sigma r1 r2,
      fault_weight_message_state msg sigma r1 ->
      fault_weight_state sigma r2 ->
      fault_weight_state (next msg sigma) (r1 + r2)%R
.

Lemma fault_weight_state_empty : forall r,
  fault_weight_state Empty r ->
  (r = 0)%R.
Proof.
  intros.
  inversion H; subst.
  - reflexivity.
  - apply no_confusion_next_empty in H0. inversion H0.
Qed.

Lemma fault_weight_state_nonnegative : forall sigma r,
  fault_weight_state sigma r ->
  (0 <= r)%R.
Proof.
  intros.
  induction H.
  - apply Rle_refl.
  - apply fault_weight_message_state_nonnegative in H.
    apply (Rplus_le_le_0_compat _ _ H IHfault_weight_state).
Qed.

Theorem fault_weight_state_functional : forall sigma r1 r2,
  fault_weight_state sigma r1 ->
  fault_weight_state sigma r2 ->
  r1 = r2.
Proof.
  intros.
  generalize dependent r2.
  induction H; intros.
  - apply fault_weight_state_empty in H0. symmetry. assumption.
  - inversion H1; subst.
    + symmetry in H3. apply no_confusion_next_empty in H3. inversion H3.
    + apply no_confusion_next in H2; subst. destruct H2; subst.
      apply (fault_weight_message_state_functional _ _ _ _ H) in H3; subst.
      apply Rplus_eq_compat_l.
      apply IHfault_weight_state in H4. 
      assumption.
Qed.

Theorem fault_weight_state_total : forall sigma,
  exists r, fault_weight_state sigma r.
Proof.
  intros.
  induction sigma.
  - exists 0%R. constructor.
  - rewrite add_is_next.
    destruct (fault_weight_message_state_total (c,v,sigma1) sigma2) as [r1 H1].
    destruct IHsigma2 as [r2 H2].
    apply (fault_weight_state_Next _ _ _ _ H1) in H2.
    exists (r1+r2)%R. assumption.
Qed.

Lemma fault_weight_state_backwards : forall msg sigma r1 r2,
  fault_weight_message_state msg sigma r1 ->
  fault_weight_state (next msg sigma) r2 ->
  fault_weight_state sigma (r2 - r1)%R.
Proof.
  intros.
  inversion H0; subst.
  - symmetry in H2.
    apply no_confusion_next_empty in H2. inversion H2.
  - apply no_confusion_next in H1. destruct H1; subst.
    apply (fault_weight_message_state_functional msg sigma r1 r0 H) in H2; subst.
    rewrite Rplusminus_assoc.
    rewrite Rplus_minus.
    assumption.
Qed.

Lemma fault_weight_state_sorted_subset : forall sigma sigma' r1 r2,
  sorted_subset sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  generalize dependent r1. generalize dependent r2.
  induction H; intros.
  + apply fault_weight_state_empty in H0; subst.
    apply fault_weight_state_nonnegative in H1. 
    assumption.
  + destruct (fault_weight_message_state_total msg sigma) as [r1' H2].
    destruct (fault_weight_message_state_total msg sigma') as [r2' H3].
    apply (fault_weight_state_backwards _ _ _ _ H2) in H0.
    apply (fault_weight_state_backwards _ _ _ _ H3) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply (fault_weight_message_state_sorted_subset _ _ _ _ _ H H2) in H3.
    (* maybe this part can be proved easier *)
    apply (Rplus_le_compat_r r1' _ _) in H0.
    rewrite Rplusminus_assoc_r in H0.
    rewrite Rplus_opp_l in H0.
    rewrite Rplus_0_r in H0.
    apply (Rplus_le_compat_l (Ropp r2') _ _) in H3.
    rewrite Rplus_opp_l in H3.
    rewrite Rplusminus_assoc_r in H0.
    apply (Rplus_ge_reg_neg_r r2 (Ropp r2' + r1') r1 H3) in H0 .
    assumption.
  + destruct (fault_weight_message_state_total msg sigma') as [r2' H3].
    apply (fault_weight_state_backwards _ _ _ _ H3) in H1.
    apply (IHsorted_subset _ H1) in H0.
    apply fault_weight_message_state_nonnegative in H3.
    assert (H4 := Rminus_lt_r r2 r2' H3).
    apply (Rle_trans _ _ _ H0 H4).
Qed.

Lemma fault_weight_state_add : forall msg sigma sigma' r1 r2,
  locally_sorted sigma ->
  locally_sorted sigma' ->
  add_in_sorted msg sigma sigma' ->
  fault_weight_state sigma r1 ->
  fault_weight_state sigma' r2 ->
  (r1 <= r2)%R.
Proof.
  intros.
  apply add_in_sorted_sorted_subset in H1; try assumption.
  apply (fault_weight_state_sorted_subset sigma sigma' r1 r2 H1 H2 H3).
Qed.
 *)