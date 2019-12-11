From Casper
Require Import vlsm composed_vlsm composed_vlsm_projections indexed_vlsm.


Definition indexed_vlsm_constrained_projection
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (IM : forall i : oindex, @VLSM message (IS i))
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_sig IS i)
    (indexed_sig_composed_instance IS i)
    (indexed_vlsm_constrained IM i constraint)
    (indexed_vlsm_constrained_composed_instance IM i constraint)
    i
  .


Definition indexed_vlsm_free_projection
  {message : Type}
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (IM : forall i : oindex, @VLSM message (IS i))
  (i : oindex)
  : VLSM (message : Type)
  :=
  indexed_vlsm_constrained_projection IM free_constraint i.

