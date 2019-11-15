From Casper
Require Import vlsm vlsm_preamble composed_vlsm composed_vlsm_projections indexed_vlsm.

Definition indexed_vlsm_projection
  {message : Type}
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {IL : forall i : oindex, @LSM message (IS i)}
  (IM : forall i : oindex, @VLSM message _ (IL i))
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_sig IS (inhabits i))
    (indexed_sig_composed_instance IS (inhabits i))
    (indexed_lsm IL (inhabits i))
    (indexed_lsm_composed_instance IL (inhabits i))
    (indexed_vlsm IM (inhabits i))
    (@indexed_vlsm_composed_instance oindex message Heqd IS IL IM (inhabits i))
    i
  .

Definition indexed_vlsm_constrained_projection
  {message : Type}
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {IL : forall i : oindex, @LSM message (IS i)}
  (IM : forall i : oindex, @VLSM message _ (IL i))
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_sig IS (inhabits i))
    (indexed_sig_composed_instance IS (inhabits i))
    (indexed_lsm IL (inhabits i))
    (indexed_lsm_composed_instance IL (inhabits i))
    (indexed_vlsm_constrained IM (inhabits i) constraint)
    (@indexed_vlsm_constrained_composed_instance oindex message Heqd IS IL IM (inhabits i) constraint)
    i
  .

