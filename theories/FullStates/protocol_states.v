Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.

Require Import Casper.preamble.
Require Import Casper.ListExtras.
Require Import Casper.ListSetExtras.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.FullStates.threshold.


(*********************)
(** Protocol states **)
(*********************)

Module Protocol_States
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PEstimator : Estimator PCons PVal PVal_Weights)
        (PThreshold : Threshold PVal PVal_Weights)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PThreshold.
Import PEstimator.

Module PThreshold_Properties := Threshold_Properties PCons PVal PVal_Weights PEstimator PThreshold.
Export PThreshold_Properties.


(*******************************)
(** Protocol state conditions **) 
(*******************************)

(** The Full Node condition. Assumes sigma1 and sigma2 are sorted **)

Definition full_node_condition (sigma1 sigma2 : state) : Prop :=
    syntactic_state_inclusion sigma1 sigma2.

(** The valid message condition **)
Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
    estimator sigma c.

(** The fault tolerance condition **)
Definition fault_tolerance_condition (sigma : state) : Prop :=
  (fault_weight_state sigma <= t)%R.

Lemma fault_tolerance_condition_singleton : forall msg,
  fault_tolerance_condition (next msg Empty).
Proof.
  intros [(c, v) j].
  unfold fault_tolerance_condition.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold equivocating_message_state. simpl.
  unfold equivocating_messages. 
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. apply threshold_nonnegative.
Qed.

Lemma fault_tolerance_condition_subset : forall sigma sigma',
  syntactic_state_inclusion sigma sigma' ->
  fault_tolerance_condition sigma' ->
  fault_tolerance_condition sigma.
Proof.
  unfold fault_tolerance_condition.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

(** Protocol states **)
Inductive protocol_state : state -> Prop :=
  | protocol_state_empty : protocol_state Empty
  | protocol_state_next : forall c v sigma sigma',
      protocol_state sigma -> 
      protocol_state sigma' ->
      full_node_condition sigma sigma' ->
      valid_estimate_condition c sigma ->
      fault_tolerance_condition (add_in_sorted_fn (c, v, sigma) sigma') ->
      protocol_state (add_in_sorted_fn (c, v, sigma) sigma')
  .


Lemma protocol_state_fault_tolerance : forall sigma,
  protocol_state sigma ->
  fault_tolerance_condition sigma.
Proof.
  intros.
  inversion H.
  - unfold fault_tolerance_condition. unfold fault_weight_state.
    simpl. apply Rge_le. apply threshold_nonnegative.
  - assumption.
Qed.

Lemma protocol_state_sorted : forall state,
  protocol_state state -> 
  locally_sorted state.
Proof.
  intros.
  induction H.
  - constructor.
  - apply (add_in_sorted_sorted (c, v, sigma) sigma'); try assumption.
    apply locally_sorted_message_justification. assumption.
Qed.

Lemma protocol_state_singleton : forall c v,
  valid_estimate_condition c Empty ->
  protocol_state (next (c, v, Empty) Empty).
Proof.
  intros.
  assert (Heq : add_in_sorted_fn (c, v, Empty) Empty = (next (c, v, Empty) Empty))
  ; try reflexivity.
  rewrite <- Heq.
  apply protocol_state_next; try assumption; try apply protocol_state_empty.
  - apply incl_refl. 
  - simpl. rewrite add_is_next. apply fault_tolerance_condition_singleton.
Qed.

Definition estimator_functional : Prop :=
  forall sigma c1 c2, estimator sigma c1 -> estimator sigma c2 -> c1 = c2.

Lemma protocol_state_empty_justification : forall sigma,
  protocol_state sigma ->
  sigma = Empty \/ exists msg, in_state msg sigma /\ justification msg = Empty.
Proof.
  intros. induction H; try (left; reflexivity). right.
  destruct sigma.
  - exists (c, v, Empty). split; try reflexivity.
    apply in_state_add_in_sorted_iff. left. reflexivity.
  - destruct IHprotocol_state2.
    + subst. exfalso. apply (in_empty_state (c0, v0, sigma1)). apply H1. 
      simpl. left. reflexivity.
    + destruct H4 as [msg [Hin Hj]].
      exists msg. split; try assumption.
      apply in_state_add_in_sorted_iff. right. assumption.
Qed.

Lemma extend_protocol_state : forall sigma,
  protocol_state sigma ->
  forall c,
  valid_estimate_condition c sigma ->
  forall v,
  protocol_state (add_in_sorted_fn (c, v, sigma) sigma).
Proof.
  intros sigma Hps c Hc v.
  constructor; try assumption; try apply incl_refl.
  unfold fault_tolerance_condition.
  apply fault_tolerance_condition_subset with (add (c,v,sigma) to sigma).
  - unfold syntactic_state_inclusion. apply set_eq_add_in_sorted.
  - unfold fault_tolerance_condition. unfold fault_weight_state.
    rewrite equivocating_senders_extend.
    apply protocol_state_fault_tolerance in Hps. assumption.
Qed.

Definition Reachable sigma1 sigma2 :=
  protocol_state sigma1 /\ protocol_state sigma2 /\ syntactic_state_inclusion sigma1 sigma2.

Notation "sigma2 'in_Futures' sigma1" :=
  (Reachable sigma1 sigma2)
  (at level 20).

Lemma in_Futures_trans : forall sigma1 sigma2 sigma3,
  sigma1 in_Futures sigma2 ->
  sigma2 in_Futures sigma3 ->
  sigma1 in_Futures sigma3.
Proof.
  intros. destruct H as [Hps2 [Hps1 Hincl21]]. destruct H0 as [Hps3 [_ Hincl32]].
  repeat (split; try assumption). apply incl_tran with (get_messages sigma2); assumption.
Qed.


Definition two_senders := exists (v1 v2 : V), v1 <> v2.

Lemma distinct_sender : two_senders -> forall v1 : V, exists v2 : V, v1 <> v2.
Proof.
  intros.
  destruct H  as [v1' [v2' Hneq]].
  destruct (v_eq_dec v1 v1') eqn:Heq.
  - subst. exists v2'. assumption.
  - exists v1'. assumption.
Qed.

Theorem not_extx_in_x : forall c v j j',
  syntactic_state_inclusion j' j ->
   ~ in_state (c, v, j) j'.
Proof.
  induction j'; intros;  unfold in_state; simpl; intro; try assumption.
  destruct H0.
  - inversion H0; subst; clear H0.
    apply IHj'1; try apply incl_refl. apply H. left. reflexivity.
  - apply IHj'2; try assumption.
    intros msg Hin. apply H. right. assumption.
Qed.

Theorem equivocating_messages_exists :
  two_senders ->
  forall c v j,
    protocol_state j ->
    estimator j c ->
    exists j' c',
      j' in_Futures j /\
      estimator j' c' /\
      equivocating_messages (c, v, j) (c', v, j') = true.
Proof.
  intros H c v j H0 Hestj.
  destruct (distinct_sender H v) as [v' Hneq].
  exists (add_in_sorted_fn (c, v', j) j).
  remember (add_in_sorted_fn (c, v', j) j) as j'.
  destruct (estimator_total j') as [c' Hest].
  exists c'.
  split.
  - split; try assumption.
    split
    ; try (subst; intros msg Hin; apply in_state_add_in_sorted_iff; right; assumption).
    subst. constructor; try assumption; try apply incl_refl.
    unfold fault_tolerance_condition. unfold fault_weight_state.
    apply protocol_state_fault_tolerance in H0. unfold fault_tolerance_condition in H0.
    apply Rle_trans with (fault_weight_state j); try assumption.
    apply sum_weights_incl; try apply set_map_nodup.
    unfold equivocating_senders. apply set_map_incl.
    intros msg Hin.
    apply filter_In in Hin. apply filter_In. destruct Hin.
    apply in_state_add_in_sorted_iff in H1. destruct H1 as [Heq | Hin].
    + subst. exfalso. unfold equivocating_message_state in H2.
      rewrite existsb_exists in H2. destruct H2 as [msg [Hin Hequiv]].
      apply in_state_add_in_sorted_iff in Hin.
      destruct Hin as [Heq | Hin].
      * subst. unfold equivocating_messages in Hequiv. rewrite eq_dec_if_true in Hequiv; try reflexivity.
        inversion Hequiv.
      * rewrite equivocating_messages_comm in Hequiv. rewrite non_equivocating_messages_extend in Hequiv
        ; try assumption. inversion Hequiv.
    + split; try assumption.
      unfold equivocating_message_state in H2. apply existsb_exists in H2.
      destruct H2 as [msg' [Hin' Hequiv]].
      apply existsb_exists. exists msg'. split; try assumption.
      apply in_state_add_in_sorted_iff in Hin'.
      destruct Hin'; try assumption; subst.
      exfalso. rewrite non_equivocating_messages_extend in Hequiv; try assumption. inversion Hequiv.
  - split; try assumption.
    unfold equivocating_messages.
    rewrite eq_dec_if_false.
    + rewrite eq_dec_if_true; try reflexivity.
      rewrite andb_true_iff.
      split; rewrite negb_true_iff
      ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity
      ; intro.
      * subst. apply in_state_add_in_sorted_iff in H1.
      { destruct H1.
        - inversion H1. subst. apply Hneq. reflexivity.
        - apply (not_extx_in_x c v j j); try assumption.
          apply incl_refl.
      }
      * apply (not_extx_in_x c' v j' j); try assumption. subst.
        intros msg Hin. apply in_state_add_in_sorted_iff. right. assumption.
    + intro. inversion H1; subst; clear H1.
      apply (not_extx_in_x c' v' j j); try apply incl_refl. rewrite H4 at 2.
      apply in_state_add_in_sorted_iff. left. reflexivity.
Qed.



End Protocol_States.