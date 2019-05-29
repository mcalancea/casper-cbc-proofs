(************************************************************)
(** Consistent Decisions on Properties of Protocol States  **)
(************************************************************)

Require Import List.
Import ListNotations.

Require Import Casper.preamble.

Require Import Casper.full_version.
Require Import Casper.full_states.
Require Import Casper.full_messages.

Require Import Casper.FullStates.sorted_subset.
Require Import Casper.FullStates.locally_sorted.
Require Import Casper.FullStates.sorted_union.

Require Import Casper.common_futures.


(* work in progress *)

(* Decided properties of protocol states *)

Definition decided (q : state -> Prop) (sigma : state) : Prop := forall sigma',
  sigma' in_Futures sigma ->
  q sigma'.

(*
Inductive decided' : (state -> Prop) -> state -> Prop :=
  is_decided : forall (p : state -> Prop) sigma,
    protocol_state sigma ->
    (forall sigma',
      protocol_state sigma' ->
      sigma => sigma' ->
      p sigma'
    ) ->
  decided' p sigma.


Lemma decided2 : forall (p : state -> Prop) sigma,
  decided p sigma <-> decided' p sigma.
Proof.
  intros. split; intros.
  - unfold decided in H. destruct H. constructor; try assumption.
  - inversion H; subst. split; assumption.
Qed.
 *)

(* Forward consistency *)
Lemma forward_consistency : forall sigma sigma' q,
  protocol_state(sigma) ->
  protocol_state(sigma') ->
  sigma' in_Futures sigma ->
  decided q sigma ->
  decided q sigma'.
Admitted.


(* n-party consensus safety for properties of protocol states  *)
Theorem n_party_consensus_safety_for_properties_of_protocol_states : forall sigmas sigma,
  Forall protocol_state sigmas ->
  fold sorted_union sigmas sigma ->
  fault_tolerance_condition sigma ->
  exists sigma',
    protocol_state(sigma') /\
    forall (q : state -> Prop),
      Exists (decided q) sigmas ->
      q sigma'
  .
Proof.
  intros.
  destruct (n_party_common_futures _ _ H H0 H1) as [sigma' CF]. destruct CF.
  exists sigma'.
  split; try assumption.
  intros.
  apply Exists_exists in H4.
  destruct H4 as [sigma0 H5]. destruct H5.
  apply H5.
  rewrite Forall_forall in H3.
  apply (H3 sigma0 H4).
Qed.
