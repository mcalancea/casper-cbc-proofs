Require Import Coq.Lists.ListSet.
Require Import List.

Require Import Casper.preamble.

Require Import Casper.FullStates.consensus_values.
Require Import Casper.FullStates.validators.
Require Import Casper.FullStates.estimator.
Require Import Casper.FullStates.fault_weights.
Require Import Casper.FullStates.threshold.
Require Import Casper.FullStates.protocol_states.

Module Common_Futures
        (PCons : Consensus_Values) 
        (PVal : Validators)
        (PVal_Weights : Validators_Weights PVal)
        (PThreshold : Threshold PVal PVal_Weights)
        (PEstimator : Estimator PCons PVal)
        .

Import PCons.
Import PVal.
Import PVal_Weights.
Import PThreshold.
Import PEstimator.

Module PProtocol_States := Protocol_States PCons PVal PVal_Weights PThreshold PEstimator.
Export PProtocol_States.

(** Two party common futures **)

Lemma union_protocol_2states : forall sigma1 sigma2,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  fault_tolerance_condition (state_union sigma1 sigma2) ->
  protocol_state (state_union sigma1 sigma2).
Proof.
  intros sig1 sig2 Hps1 Hps2.
  induction Hps2; intros.
  - unfold state_union. simpl. rewrite list_to_state_sorted; try assumption.
    apply protocol_state_sorted. assumption.
  - clear IHHps2_1.
    rewrite (state_union_add_in_sorted sig1 (c, v, sigma) sigma') in *
    ; try (apply (locally_sorted_message_justification c v sigma))
    ; try (apply protocol_state_sorted; assumption)
    .
    assert (protocol_state (state_union sig1 sigma')).
    { apply IHHps2_2.
      apply fault_tolerance_condition_subset with
        (add_in_sorted_fn (c, v, sigma) (state_union sig1 sigma'))
      ; try assumption.
      intros msg Hin. apply set_eq_add_in_sorted. right. assumption.
    }
    constructor; try assumption.
    + intros msg Hin. apply state_union_iff. right. apply H. assumption.
Qed.

Theorem two_party_common_futures : forall sigma1 sigma2,
  protocol_state sigma1 ->
  protocol_state sigma2 ->
  fault_tolerance_condition (state_union sigma1 sigma2) ->
  exists sigma',
  protocol_state sigma' /\
  sigma' in_Futures sigma1  /\
  sigma' in_Futures sigma2.
Proof.
  intros.
  exists (state_union sigma1 sigma2).
  split.
  - apply (union_protocol_2states _ _ H H0 H1).
  - split; constructor; try assumption ; split; try apply union_protocol_2states; try assumption; intros msg Hin; apply state_union_messages; apply set_union_intro.
    + left. assumption.
    + right. assumption.
Qed.

Lemma union_protocol_nstates : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
  protocol_state (fold_right state_union Empty sigmas).
Proof.
  induction sigmas; intros.
  - simpl. constructor.
  - inversion H; subst; clear H.
    simpl in H0. 
    apply (fault_tolerance_condition_subset (fold_right state_union Empty sigmas)) in H0 as Hftc.
    + simpl. apply union_protocol_2states; try assumption. apply IHsigmas; try assumption.
    + apply state_union_incl_right.
Qed.

Theorem n_party_common_futures : forall sigmas,
  Forall protocol_state sigmas ->
  fault_tolerance_condition (fold_right state_union Empty sigmas) ->
  exists sigma',
    protocol_state(sigma') /\
    Forall (fun sigma => sigma' in_Futures sigma) sigmas.
Proof.
  intros.
  exists (fold_right state_union Empty sigmas).
  apply (union_protocol_nstates sigmas) in H0; try assumption.
  split; try assumption.
  apply Forall_forall; intros.
  rewrite Forall_forall in H. apply H in H1 as Hpsx.
  constructor; try assumption. split; try assumption.
  apply state_union_incl_iterated. assumption.
Qed.

End Common_Futures.