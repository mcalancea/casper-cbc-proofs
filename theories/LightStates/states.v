Require Import Coq.Lists.ListSet.
Require Import List.

Require Import Casper.LightStates.messages.

(** Hash sets **)

Definition state := set message.

Definition state_empty := empty_set message.

Definition state_add := set_add message_eq_dec.

Definition state_remove := set_remove message_eq_dec.

Definition state_in := set_mem message_eq_dec.

Definition state_union := set_union message_eq_dec.

Lemma state_eq_dec : forall (sigma1 sigma2 : state), {sigma1 = sigma2} + {sigma1 <> sigma2}.
Proof.
  intros. apply list_eq_dec. apply message_eq_dec.
Qed.