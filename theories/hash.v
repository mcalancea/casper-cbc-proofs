Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import List.

Require Import Casper.preamble.
Require Import Casper.sorted_lists.

(*******************)
(** Hash universe **)
(*******************)

Parameter hash : Set .

(** Comparison function on hashes **)

Parameter hash_compare : hash -> hash -> comparison.

(** hash set totally ordered **)

Parameter hash_compare_strict_order : CompareStrictOrder hash_compare.

Lemma hash_compare_refl : forall h, hash_compare h h = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 hash_compare_strict_order).
Qed.

Definition hash_lt : hash -> hash -> Prop := compare_lt hash_compare.

Definition hash_lt_strict_order: StrictOrder hash_lt :=
  compare_lt_strict_order hash hash_compare hash_compare_strict_order.

Definition hash_lt_total_order: TotalOrder hash_lt :=
  compare_lt_total_order hash hash_compare hash_compare_strict_order.

Definition hash_eq_dec : EqualityDec hash :=
  compare_eq_dec hash hash_compare hash_compare_strict_order.

(** Hash sets **)

Definition hash_list_in := Inb hash_compare.

Definition hash_list_compare_in : forall a l,
  In a l <-> hash_list_in a l = true
  := compare_in hash hash_compare hash_compare_strict_order.

Definition hash_list_compare_not_in : forall a l,
  not (In a l) <-> hash_list_in a l = false
  := compare_not_in hash hash_compare hash_compare_strict_order.

Definition hash_list_compare := list_compare hash_compare.

Definition hash_list_compare_strict_order : CompareStrictOrder hash_list_compare :=
  list_compare_strict_order hash hash_compare hash_compare_strict_order.

Lemma hash_list_compare_refl : forall hs, hash_list_compare hs hs = Eq.
Proof.
  apply compare_eq_refl . 
  apply (proj1 hash_list_compare_strict_order).
Qed.

Definition hash_list_lt := compare_lt hash_list_compare.

Definition hash_list_lt_strict_order : StrictOrder hash_list_lt :=
  compare_lt_strict_order (list hash) hash_list_compare hash_list_compare_strict_order.

Definition hash_list_lt_total_order : TotalOrder hash_list_lt :=
  compare_lt_total_order (list hash) hash_list_compare hash_list_compare_strict_order.

Definition add_in_hash_set := @add_in_sorted_list hash hash_lt.

Definition hash_list_eq_dec : EqualityDec (list hash) :=
  compare_eq_dec (list hash) hash_list_compare hash_list_compare_strict_order.
