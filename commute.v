Require Import Bool List Streams Logic.Epsilon.
Import List Notations.
From Casper 
Require Import preamble ListExtras ListSetExtras RealsExtras protocol common definitions vlsm indexed_vlsm composed_vlsm composed_vlsm_projections indexed_vlsm_projections.

(* 3.1 Decisions on consensus values *) 

(* Need to add consensus values (and decision functions) to VLSM definitions? *) 
(* Class VLSM_plus `{VLSM} :=
  { C : Type;
    about_C : exists (c1 c2 : C), c1 <> c2;
  }.
 *)
Definition decision `{VLSM} (C : Type) : Type := state -> option C. 

(* 3.2.1 Decision finality *)
(* Program Definition prot_state0 `{VLSM} : protocol_state := 
  exist protocol_state_prop (proj1_sig s0) _.
Next Obligation.
  red.
  exists None. 
  constructor.
Defined.
 *)
Definition Trace_nth `{VLSM} (tr : Trace)
  : nat -> option protocol_state :=
  fun (n : nat) => match tr with
              | Finite ls => nth_error ls n
              | Infinite st => Some (Str_nth n st) end. 

Definition decisions_final `{X : VLSM} {C} (D : decision C) : Prop :=
  forall (tr : Trace),
      forall (n1 n2 : nat)
        (oc1 := option_map D (option_map (@proj1_sig _ _) (Trace_nth tr n1)))
        (oc2 := option_map D (option_map (@proj1_sig _ _) (Trace_nth tr n2))),
        (oc1 <> None) ->
        (oc2 <> None) ->
        oc1 = oc2.

(* 3.2.2 Decision consistency *)
Definition in_trace `{VLSM} : protocol_state -> Trace -> Prop :=
  fun (s : protocol_state) (tr : Trace) => exists (n : nat), Trace_nth tr n = Some s.

Definition decisions_final_consistent
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  {C : Type}
  (ID : forall i : index, @decision _ _ (indexed_vlsm_constrained_projection IM constraint i) C)
  : Prop
  :=
    (* Assuming we want traces of the overall protocol *)
    forall (tr : @protocol_trace _ _ (indexed_vlsm_constrained IM Hi constraint)),
      forall (n1 n2 : nat) (j k : index)
        (osn1 := option_map (@proj1_sig _ _) (Trace_nth tr n1))
        (osn2 := option_map (@proj1_sig _ _) (Trace_nth tr n2))
        (proj := @istate_proj _ _ (@indexed_sig_composed_instance _ _ Heqd IS Hi))
        (osn1j := option_map (proj j) osn1)
        (osn2k := option_map (proj k) osn2)
        (oc1j := option_map (ID j) osn1j)
        (oc2k := option_map (ID k) osn2k),
        (oc1j <> None) ->
        (oc2k <> None) ->
        oc1j = oc2k.

Lemma decisions_final_consistent_includes_decisions_final
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  {C : Type}
  (ID : forall i : index, @decision _ _ (indexed_vlsm_constrained_projection IM constraint i) C)
  : decisions_final_consistent Hi constraint ID -> forall i : index, decisions_final (ID i).
Proof.
  intros DFC i tr n1 n2 oc1 oc2 H1 H2.
  specialize (DFC tr n1 n2).
  remember oc1 as oc1'. unfold oc1 in *; clear oc1.
  destruct oc1'; try (exfalso; apply H1; reflexivity); clear H1.
  remember oc2 as oc2'. unfold oc2 in *; clear oc2.
  destruct oc2'; try (exfalso; apply H2; reflexivity); clear H2.
  apply f_equal.
 simpl.
  
(* 3.3.1 Initial protocol state bivalence *)
Definition bivalent `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) =>
    (* All initial states decide on None *) 
    (forall (s0 : protocol_state),
      initial_state_prop (proj1_sig s0) ->
      D s0 None) /\
    (* Every protocol trace (already beginning from an initial state) contains a state deciding on each consensus value *) 
    (forall (c : C) (tr : protocol_trace),
        exists (s : protocol_state) (n : nat), 
          (Trace_nth tr n) = s /\ D s (Some c)).

(* 3.3.2 No stuck states *) 
Definition stuck_free `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) =>
    (exists (s : protocol_state),
        forall (tr : protocol_trace_from (fun s => s = s)) (n : nat),
            D (Trace_nth tr n) None) -> False. 

(* 3.3.3 Protocol definition symmetry *) 
(* How do we formalize this property set-theoretically? *)
Definition behavior `{VLSM_plus} : decision -> Prop := fun _ => True. 
Definition symmetric `{VLSM_plus} :=
  forall (D : decision),
  exists (f : decision -> decision),
    behavior D = behavior (f D). 

(* 3.4 Liveness *) 
Definition live `{VLSM_plus} : (nat -> VLSM_plus) -> (nat -> decision) -> Prop :=
  fun (IS : nat -> VLSM_plus) (ID : nat -> decision) =>
    (* Here we want traces starting at the initial states *)
    forall (tr : protocol_trace),
      complete_trace_prop tr -> 
      exists (i n : nat) (c : C),
        (ID i) (Trace_nth tr n) (Some c). 

(* Section 4 *) 



  
