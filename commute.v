Require Import Bool List Streams Logic.Epsilon.
Import List Notations.
From Casper 
Require Import preamble ListExtras ListSetExtras RealsExtras protocol common definitions vlsm indexed_vlsm.

(* 3.1 Decisions on consensus values *) 

(* Need to add consensus values (and decision functions) to VLSM definitions? *) 
Class VLSM_plus `{VLSM} :=
  { C : Type;
    about_C : exists (c1 c2 : C), c1 <> c2;
  }.

Definition decision `{VLSM_plus} : Type := protocol_state -> option C -> Prop. 

(* 3.2.1 Decision finality *)
Program Definition init_state0 `{VLSM} : initial_state := _. 
Next Obligation.
  assert (H_inhabited := protocol_state_inhabited). 
  apply (epsilon_statement (fun a => True)) in H_inhabited.
  destruct H_inhabited as [witness _].
  exact witness. 
Qed.

Program Definition prot_state0 `{VLSM} : protocol_state := _. 
Next Obligation.
  assert (H_inhabited := protocol_state_inhabited).
  apply (epsilon_statement (fun a => True)) in H_inhabited.
  destruct H_inhabited as [witness _].
  exact (exist protocol_state_prop (proj1_sig witness) (initial_protocol_state witness)). 
Defined. 

Definition Trace_nth `{VLSM} (tr : Trace)
  : nat -> protocol_state :=
  fun (n : nat) => match tr with
              | Finite ls => nth n ls prot_state0
              | Infinite st => Str_nth n st end. 

Definition final `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) => forall (tr : Trace), 
      forall (n1 n2 : nat) (c1 c2 : option C),
        (D (Trace_nth tr n1) c1 -> c1 <> None) ->
        (D (Trace_nth tr n1) c2 -> c2 <> None) ->
        c1 = c2.

(* 3.2.2 Decision consistency *)
Definition in_trace `{VLSM} : protocol_state -> Trace -> Prop :=
  fun (s : protocol_state) (tr : Trace) => exists (n : nat), Trace_nth tr n = s.

Definition consistent
  {index : Set}
  {message : Type}
  `{VLSM_plus}
  {IS : index -> LSM_sig message}
  {IL : forall i : index, @LSM message (IS i)}
  (IM : forall i : index, @VLSM message _ (IL i))
  (ID : index -> decision)
  : Prop
  :=
    (* Assuming we want traces of the overall protocol *)
    forall (tr : protocol_trace) (s : protocol_state),
      in_trace s tr ->
      forall (n1 n2 j k : index),
      exists (c1 c2 : C),
        (ID n1) s (Some c1) -> (ID n2) s (Some c2) ->
        forall (c : C),
          (ID n1) s (Some c) <-> (ID n2) s (Some c).       
  
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

(* Creating a full-node instance of VLSM *)
Parameters (CV V : Type) (about_CV : StrictlyComparable CV) (about_V : StrictlyComparable V). 
Definition vstate := @definitions.state CV V. 

Parameter about_vstate : StrictlyComparable vstate. 

Definition vlabel : Type := (option (CV * V)).

Definition vmessage : Type := (CV * V * vstate).

Fixpoint get_messages (sigma : vstate) : list vmessage :=
  match sigma with
  | Empty => nil
  | Next c v j sigma' => (c,v,j) :: get_messages sigma'
  end.

Fixpoint unget_messages (lm : list vmessage) : vstate :=
  match lm with
  | nil => Empty
  | (c,v,j) :: tl => Next c v j (unget_messages tl)
  end.

Theorem get_unget_idempotent :
  forall (lm : list vmessage),
    get_messages (unget_messages lm) = lm.
Proof.
  induction lm as [|hd tl IHlm]. 
  - reflexivity.
  - destruct hd as [[c v] j].
    simpl. rewrite IHlm.
    reflexivity.
Qed. 

Theorem unget_get_idempotent :
  forall (s : vstate),
    unget_messages (get_messages s) = s.
Proof.
  intros s.
  induction s.
  - reflexivity.
  - simpl. rewrite IHs2.
    reflexivity. 
Qed.

Definition vreach (s1 s2 : vstate) : Prop :=
  incl (get_messages s1) (get_messages s2).

Definition proto_vmessage_prop : vmessage -> Prop :=
  fun msg => True. 

Definition proto_vmessage : Type :=
  { m : vmessage | proto_vmessage_prop m}. 

Lemma proto_vmessage_decidable :
  forall msg, {proto_vmessage_prop msg} + {~ proto_vmessage_prop msg}. 
Proof. 
  intros msg.
  left.
  red. auto.
Qed.

Definition initial_vstate_prop : vstate -> Prop :=
  fun s => s = Empty.

Parameter message0 : vmessage. 

Definition initial_vmessage_prop : proto_vmessage -> Prop :=
  fun msg => proj1_sig msg = message0. 

Definition initial_vmessage := { m : proto_vmessage | initial_vmessage_prop m }. 

Lemma protocol_vstate_inhabited : {_ : vstate | True}. 
Proof.
  remember (Empty : vstate) as state0.
  assert (about_state0 : True) by auto. 
  remember (exist _ state0 about_state0) as witness.
  exact witness.
Qed. 

Lemma vmessage_inhabited : {m : vmessage | True}. 
Proof.
  exists message0. auto.
Qed.

Lemma vlabel_inhabited : vlabel. 
Proof.
  destruct about_CV.
  destruct inhabited as [c _].
  destruct about_V.
  destruct inhabited as [v _].
  exact (Some (c,v)).
Qed.

Definition add_vmessage (msg : vmessage) (s : vstate) : vstate :=
  match msg with
  | (c,v,j) => Next c v j s
  end. 

Program Definition make_proto_vmessage (msg : vmessage) : { msg : vmessage | proto_vmessage_prop msg} := _. 
Next Obligation.
  exists msg. red. auto.
Defined.

Definition vtransition (l : vlabel) (sm : vstate * option {m : vmessage | proto_vmessage_prop m}) : vstate * option {m : vmessage | proto_vmessage_prop m} :=
  match l with 
  | None => match (snd sm) with 
           | None => ((fst sm), None)
           | Some msg => (add_vmessage (proj1_sig msg) (fst sm), None) 
           end
  | Some (c, v) => match (snd sm) with
                  | None => (fst sm, None)
                  | Some msg => (add_vmessage (proj1_sig msg) (fst sm), Some (make_proto_vmessage (c,v,(fst sm))))
                  end
  end.

Parameter not_heavy : vstate -> Prop.
Parameter not_heavyb : vstate -> bool.
Parameter estimator : CV -> vstate -> Prop. 
Parameter estimatorb : CV -> vstate -> bool.
Parameter vreachb : vstate -> vstate -> bool. 

Inductive valid_client : vlabel -> vstate * option {m : vmessage | proto_vmessage_prop m} -> Prop :=
| valid_none : forall (s : vstate), valid_client None (s, Some (make_proto_vmessage message0))
| valid_receive : forall (s : vstate) (msg : CV * V * vstate),
    vreach (snd msg) s ->
    not_heavy (add_vmessage (msg) s) ->
    valid_client None (s, Some (make_proto_vmessage msg))
| valid_produce : forall (s : vstate) (vl : CV * V) (msg : CV * V * vstate),
    estimator (fst vl) s -> valid_client (Some vl) (s, Some (make_proto_vmessage msg)).

Definition unoption_vmessage (vmsg : option {m : vmessage | proto_vmessage_prop m}) : vmessage :=
  match vmsg with
  | None => message0
  | Some msg => proj1_sig msg
  end. 

Definition valid_clientb : vlabel -> vstate * option {m : vmessage | proto_vmessage_prop m} -> bool :=
  fun l sm =>
    match l with
    | None => vreachb (add_vmessage (unoption_vmessage (snd sm)) (fst sm)) (fst sm) &&
                                  not_heavyb (fst sm)
    | Some (c,v) => estimatorb c (fst sm)
    end.

Lemma valid_client_correct :
  forall (l : vlabel) (sm : vstate * option {m : vmessage | proto_vmessage_prop m}),
    valid_clientb l sm = true <-> valid_client l sm. 
Proof. Admitted.

Lemma valid_client_correct' :
  forall (l : vlabel) (sm : vstate * option {m : vmessage | proto_vmessage_prop m}),
    valid_clientb l sm = false <-> ~ valid_client l sm. 
Proof.
  intros. apply mirror_reflect_curry.
  apply valid_client_correct.
Qed.

Lemma valid_vdecidable : forall l som, {valid_client l som} + {~valid_client l som}. 
Proof.
  intros. 
  case_eq (valid_clientb l som); intro H.
  - left.
    now apply valid_client_correct.
  - right.
    now apply valid_client_correct'.
Qed. 

Class VLSM_unredundant (message : Type) :=
  { state : Type
  ; label : Type
  ; proto_message_prop : message -> Prop
  ; proto_message_decidable : forall m, {proto_message_prop m} + {~ proto_message_prop m}
  ; proto_message := { m : message | proto_message_prop m }
  ; initial_state_prop : state -> Prop
  ; initial_state := { s : state | initial_state_prop s }
  ; initial_message_prop : proto_message -> Prop
  ; initial_message := { m : proto_message | initial_message_prop m }
  ; transition : label -> state * option proto_message -> state * option proto_message
  ; valid : label -> state * option proto_message -> Prop
  ; valid_decidable : forall l som, {valid l som} + {~valid l som}
  }.

Instance VLSM_full_client : VLSM_unredundant vmessage := 
  { state := vstate
  ; label := vlabel
  ; proto_message_prop := proto_vmessage_prop 
  ; proto_message_decidable := proto_vmessage_decidable
  ; initial_state_prop := initial_vstate_prop
  ; initial_message_prop := initial_vmessage_prop
  ; transition := vtransition
  ; valid := valid_client
  ; valid_decidable := valid_vdecidable
  }.



  
