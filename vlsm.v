Require Import List Streams.
Import ListNotations.

From Casper
Require Import ListExtras.

Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

Lemma exist_eq
  {X}
  (P : X -> Prop)
  (a b : {x : X | P x})
  : a = b <-> proj1_sig a = proj1_sig b.
Proof.
  destruct a as [a Ha]; destruct b as [b Hb]; simpl.
  split; intros Heq.
  - inversion Heq. reflexivity.
  - subst. apply f_equal. apply proof_irrelevance.
Qed.

Class EqDec X :=
  eq_dec : forall x y : X, {x = y} + {x <> y}.

Lemma DepEqDec
  {X}
  (Heqd : EqDec X)
  (P : X -> Prop)
  : EqDec {x : X | P x}.
Proof.
  intros [x Hx] [y Hy].
  specialize (Heqd x y).
  destruct Heqd as [Heq | Hneq].
  - left. subst. apply f_equal. apply proof_irrelevance.
  - right.  intros Heq. apply Hneq. inversion Heq. reflexivity.
Qed.

Lemma nat_eq_dec : EqDec nat.
Proof.
  unfold EqDec. induction x; destruct y.
  - left. reflexivity.
  - right. intros C; inversion C.
  - right. intros C; inversion C.
  - specialize (IHx y). destruct IHx as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intros Heq. inversion Heq. contradiction.
Qed.

(* 2.2.1 VLSM Parameters *)

Class LSM_sig (message : Type) :=
  { state : Type
  ; proto_message_prop : message -> Prop
  ; proto_message_decidable : forall m, {proto_message_prop m} + {~ proto_message_prop m}
  ; proto_message := { m : message | proto_message_prop m }
  ; initial_state_prop : state -> Prop
  ; initial_state := { s : state | initial_state_prop s }
  ; initial_message_prop : proto_message -> Prop
  ; initial_message := { m : proto_message | initial_message_prop m }
  ; protocol_state_inhabited : inhabited initial_state
  ; message_inhabited : inhabited proto_message
  }.

Class PLSM (message : Type) `{Sig : LSM_sig message} :=
  {
    plabel : Type
  ; plabel_inhabited : inhabited plabel
  ; ptransition : plabel -> state * option proto_message -> option (state * option proto_message)
  }.

Class VLSM (message : Type) `{Sig : LSM_sig message } := 
  {
    label : Type
  ; label_inhabited : inhabited label
  ; transition : label -> state * option proto_message -> state * option proto_message
  ; valid : label -> state * option proto_message -> Prop
  }.

Definition ptransition_to_transition
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  (l : plabel)
  (som :  state * option proto_message)
  : state * option proto_message
  :=
  match ptransition l som with
  | Some som' => som'
  | None => (fst som, None)
  end
  .

Definition ptransition_to_valid
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  (l : plabel)
  (som :  state * option proto_message)
  : Prop
  :=
  ptransition l som = None
  .

Definition PLSM_VLSM_instance
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  : @VLSM message Sig
  :=
    {|  label := plabel
     ;  label_inhabited := plabel_inhabited
     ;  transition := ptransition_to_transition
     ;  valid := ptransition_to_valid
  |}.

Class VLSM_vdecidable (message : Type) `{M : VLSM message} :=
  { valid_decidable : forall l som, {valid l som} + {~valid l som} 
  }.

Definition transition_valid_ptransition
  {message}
  {Sig : LSM_sig message}
  {VM : @VLSM message Sig}
  `{DVM : @VLSM_vdecidable message Sig VM}
  (l : label)
  (som :  state * option proto_message)
  : option (state * option proto_message)
  :=
  if valid_decidable l som
  then Some (transition l som)
  else None
  .

Definition DVLSM_PLSM_instance
  {message}
  {Sig : LSM_sig message}
  {VM : @VLSM message Sig}
  `(DVM : @VLSM_vdecidable message Sig VM)
  : @PLSM message Sig
  :=
    {|  plabel := label;
        plabel_inhabited := label_inhabited;
        ptransition := transition_valid_ptransition
  |}.


(* 2.2.2 VLSM protocol states and protocol messages *)

(* Due to the mutually recursive nature of the definition, we need to distinct between
the label-with-message and label-with-no-message transition types.
A separate characterization and induction principle glossing over these details is
provided later on. *)

Inductive
  protocol_state_prop
    {message}
    `{V : VLSM message}
    : state -> Prop
    := 
      | initial_protocol_state
        : forall s : initial_state,
        protocol_state_prop (proj1_sig s)
      | next_protocol_state_no_message
        : forall (s s' : state) (l : label) (om' : option proto_message),
        protocol_state_prop s ->
        valid l (s, None) ->
        transition l (s, None) = (s', om') ->
        protocol_state_prop s'
      | next_protocol_state_with_message
        : forall (s s' : state) (l : label) (m : proto_message) (om' : option proto_message),
        protocol_state_prop s ->
        protocol_message_prop m ->
        valid l (s, Some m) ->
        transition l (s, Some m) = (s', om') ->
        protocol_state_prop s'
  with
  protocol_message_prop
    {message}
    `{V : VLSM message}
    : proto_message -> Prop
    := 
      | initial_protocol_message
        : forall m : initial_message,
        protocol_message_prop (proj1_sig m)
      | create_protocol_message
        : forall (s s' : state) (l : label) (m' : proto_message),
        protocol_state_prop s ->
        valid l (s, None) ->
        transition l (s, None) = (s', Some m') ->
        protocol_message_prop m'
      | receive_protocol_message
        : forall (s s' : state) (l : label) (m m' : proto_message),
        protocol_state_prop s ->
        protocol_message_prop m ->
        valid l (s, Some m) ->
        transition l (s, Some m) = (s', Some m') ->
        protocol_message_prop m'
  .

Definition protocol_state
  {message}
  `{V : VLSM message}
  : Type := { s : state | protocol_state_prop s }.

Definition protocol_message
  {message}
  `{V : VLSM message}
  : Type := { m : proto_message | protocol_message_prop m }.

(* Restating validity and transition using protocol_state and protocol_messages. *)

Definition protocol_valid
  {message}
  `{V : VLSM message}
  (l : label)
  (ps_opm : protocol_state * option protocol_message)
  : Prop
  :=
  valid l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

Definition protocol_transition
  {message}
  `{V : VLSM message}
  (l : label)
  (ps_opm : protocol_state * option protocol_message)
  : state * option proto_message
  :=
  transition l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

(* Protocol state characterization - similar to the definition in the report. *)

Lemma protocol_state_prop_iff
  {message}
  `{V : VLSM message}
  : forall s' : state,
  protocol_state_prop s'
  <-> (exists is : initial_state, s' = proj1_sig is)
  \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
    protocol_valid l (s, om)
    /\ s' = fst (protocol_transition l (s, om)).
Proof.
  intros; split.
  - intro Hps'. inversion Hps' as [is His | s s'' l om' Hps Hv Ht Heq| s s'' l m om' Hps Hpm Hv Ht Heq]; try (left; exists is; reflexivity)
    ; right; subst; exists (exist _ s Hps); exists l; unfold protocol_transition; unfold protocol_valid; simpl
    ; (exists (Some (exist _ m Hpm)) || exists None)
    ; simpl ; rewrite Ht; split; auto.
  - intros [[[s His] Heq] | [[s Hps] [l [[[m Hpm]|] [Hv Ht]]]]]; try (subst; apply initial_protocol_state)
    ; unfold protocol_valid in Hv; simpl in Hv; unfold protocol_transition in Ht; simpl in Ht.
    + destruct (transition l (s, Some m)) as [s'' om'] eqn:Heq; simpl in Ht; subst.
      apply (next_protocol_state_with_message s s'' l m om'); try assumption.
    + destruct (transition l (s, None)) as [s'' om'] eqn:Heq; simpl in Ht; subst.
      apply (next_protocol_state_no_message s s'' l om'); try assumption.
Qed.

(* Protocol message characterization - similar to the definition in the report. *)

Lemma protocol_message_prop_iff
  {message}
  `{V : VLSM message}
  : forall m' : proto_message,
  protocol_message_prop m'
  <-> (exists im : initial_message, m' = proj1_sig im)
  \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
    protocol_valid l (s, om)
    /\ Some m' = snd (protocol_transition l (s, om)).
Proof.
  intros; split.
  - intro Hpm'. inversion Hpm' as [im Him | s s'' l om' Hps Hv Ht Heq| s s'' l m om' Hps Hpm Hv Ht Heq]; try (left; exists im; reflexivity)
    ; right; subst; exists (exist _ s Hps); exists l; unfold protocol_transition; unfold protocol_valid; simpl
    ; (exists (Some (exist _ m Hpm)) || exists None)
    ; simpl ; rewrite Ht; split; auto.
  - intros [[[m Him] Heq] | [[s Hps] [l [[[m Hpm]|] [Hv Ht]]]]]; try (subst; apply initial_protocol_message)
    ; unfold protocol_valid in Hv; simpl in Hv; unfold protocol_transition in Ht; simpl in Ht.
    + destruct (transition l (s, Some m)) as [s'' om'] eqn:Heq; simpl in Ht; subst.
      apply (receive_protocol_message s s'' l m m'); try assumption.
    + destruct (transition l (s, None)) as [s'' om'] eqn:Heq; simpl in Ht; subst.
      apply (create_protocol_message s s'' l m'); try assumption.
Qed.

Corollary protocol_state_destruct
  {message}
  `{V : VLSM message}
  : forall s' : protocol_state,
    (exists is : initial_state, proj1_sig s' = proj1_sig is)
    \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
      protocol_valid l (s, om)
      /\ proj1_sig s' = fst (protocol_transition l (s, om)).
Proof.
  intros [s' Hps']. simpl. apply protocol_state_prop_iff. assumption.
Qed.

(* Induction principle for protocol states *)

Lemma protocol_state_ind
  {message}
  `{V : VLSM message}
  : forall (P : state -> Prop),
  (forall is : initial_state, P (proj1_sig is)) ->
  (forall (s : protocol_state) (Hind : P (proj1_sig s)) (l : label) (om : option protocol_message)
          (Hv : protocol_valid l (s, om)),
          P (fst (protocol_transition l (s, om)))) ->
  (forall s : protocol_state, P (proj1_sig s)).
Proof.
  intros P HIi HIt [s Hps]. simpl. induction Hps as [is | s s'' l om' Hps Hp Hv Ht| s s'' l m om' Hps Hp Hpm Hv Ht].
  - apply HIi.
  - specialize (HIt (exist _ s Hps)). unfold protocol_valid in HIt. simpl in HIt.
    specialize (HIt Hp l None). simpl in HIt.
    specialize (HIt Hv). unfold protocol_transition in HIt. simpl in HIt.
    rewrite Ht in HIt. simpl in HIt. assumption.
  - specialize (HIt (exist _ s Hps)). unfold protocol_valid in HIt. simpl in HIt.
    specialize (HIt Hp l (Some (exist _ m Hpm))). simpl in HIt.
    specialize (HIt Hv). unfold protocol_transition in HIt. simpl in HIt.
    rewrite Ht in HIt. simpl in HIt. assumption.
Qed.


(* Valid VLSM transitions *)

Definition labeled_valid_transition
  {message}
  `{V : VLSM message}
  (opm : option protocol_message)
  (l : label)
  (ps ps' : protocol_state)
  : Prop
  :=
  protocol_valid l (ps, opm) /\ fst (protocol_transition l (ps, opm)) = proj1_sig ps'.


Definition valid_transition
  {message}
  `{V : VLSM message}
  (ps ps' : protocol_state)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_transition opm l ps ps'.

(* Valid  VLSM trace *)

Inductive valid_trace
  {message}
  `{V : VLSM message}
  : protocol_state -> protocol_state -> Prop :=
  | valid_trace_one
    : forall s s',
    valid_transition s s' ->
    valid_trace s s'
  | valid_trace_more
    : forall s s' s'',
    valid_transition s s' ->
    valid_trace s' s'' ->
    valid_trace s s''
  .

Lemma extend_valid_trace
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3,
  valid_trace s1 s2 ->
  valid_transition s2 s3 ->
  valid_trace s1 s3.
Proof.
  intros s1 s2 s3 Htrace.
  induction Htrace as [s1 s2 Ht12| s1 s1' s2 Ht11' Htrace1'2 IHtrace1'3]; intros Ht23.
  - apply valid_trace_more with s2; try assumption.
    apply valid_trace_one. assumption.
  - specialize (IHtrace1'3 Ht23).
    apply valid_trace_more with s1'; assumption.
Qed.

Definition valid_reflexive_trace
  {message}
  `{V : VLSM message}
  (s s' : protocol_state)
  : Prop
  :=
  s = s' \/ valid_trace s s'.

Lemma extend_valid_reflexive_trace
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3,
  valid_reflexive_trace s1 s2 ->
  valid_transition s2 s3 ->
  valid_trace s1 s3.
Proof.
  intros s1 s2 s3 Htrace12 Ht23.
  destruct Htrace12 as [Heq | Htrace12].
  - subst. apply valid_trace_one. assumption.
  - apply extend_valid_trace with s2; assumption.
Qed.


Definition labeled_valid_message_production
  {message}
  `{V : VLSM message}
  (opm : option protocol_message)
  (l : label)
  (ps : protocol_state)
  (pm' : protocol_message)
  : Prop
  :=
  protocol_valid l (ps, opm) /\ snd (protocol_transition l (ps, opm)) = Some (proj1_sig pm').

Definition valid_message_production
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_message_production opm l s m'.

Definition valid_trace_message
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists s', valid_reflexive_trace s s' /\ valid_message_production s' m'.

Lemma valid_protocol_message
  {message}
  `{V : VLSM message}
  : forall (pm : protocol_message),
  (exists im : initial_message, proj1_sig pm = proj1_sig im)
  \/
  (exists (s : protocol_state),
   exists (pm' : protocol_message),
   valid_trace_message s pm' /\ proj1_sig pm = proj1_sig pm').
Proof.
  intros. destruct pm as [m Hpm].  simpl.
  apply protocol_message_prop_iff in Hpm as Hpm'.
  destruct Hpm' as [Him | [s [l [om [Hv Ht]]]]]; try (left; assumption).
  right. exists s. exists (exist _ m Hpm). simpl. split; auto.
  exists s. split; try (left; auto).
  exists om. exists l. split; auto.
Qed.

(* Trace segments *)

Inductive trace_from_to
  {message}
  `{V : VLSM message}
  : protocol_state -> protocol_state -> list protocol_state -> Prop
  :=
  | trace_from_to_one
    : forall s1 s2, valid_transition s1 s2 -> trace_from_to s1 s2 [s1; s2]
  | trace_from_to_more
    : forall s1 s3 ts s2, valid_transition s1 s2 -> trace_from_to s2 s3 ts -> trace_from_to s1 s3 (s1 :: ts)
  .

Lemma extend_trace_from_to_left
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3 ls,
  trace_from_to s2 s3 ls ->
  valid_transition s1 s2 ->
  trace_from_to s1 s3 (s1 :: ls).
Proof.
  intros s1 s2 s3 ls Ht23 Hv12.
  apply trace_from_to_more with s2; assumption.
Qed.

Lemma extend_trace_from_to_right
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3 ls,
  trace_from_to s1 s2 ls ->
  valid_transition s2 s3 ->
  trace_from_to s1 s3 (ls ++ [s3]).
Proof.
  intros s1 s2 s3 ls Ht12 Hv23.
  induction Ht12 as [s1 s2 Hv12 | s1 s2 ls s1' Hv11' Ht1'2 Ht1'3].
  - simpl. apply trace_from_to_more with s2; try assumption.
    apply trace_from_to_one. assumption.
  - specialize (Ht1'3 Hv23).
    rewrite <- app_comm_cons.
    apply extend_trace_from_to_left with s1'; assumption.
Qed.

(* Infinite trace from state *)

CoInductive infinite_trace_from
  {message}
  `{V : VLSM message}
  : protocol_state -> Stream protocol_state -> Prop
  :=
  | infinite_trace_first
    : forall s1 ts s2,
    valid_transition s1 s2 ->
    infinite_trace_from s2 ts ->
    infinite_trace_from s1 (Cons s1 ts)
.


(* A trace is either finite or infinite *)

Inductive Trace `{VLSM} : Type :=
  | Finite : list protocol_state -> Trace
  | Infinite : Stream protocol_state -> Trace
  .

(* finite traces originating in a set *)

Definition filtered_finite_trace
  {message}
  `{V : VLSM message}
  (subset : protocol_state -> Prop)
  (ts : list protocol_state)
  : Prop
  :=
  match ts with
  | [] => False
  | [s] => False
  | s :: t => subset s /\ trace_from_to s (last t s) ts
  end.

Definition initial_protocol_state_prop
  {message}
  `{V : VLSM message}
  (ps : protocol_state)
  : Prop
  :=
  initial_state_prop (proj1_sig ps).

Definition start_protocol_state_prop `{VLSM} (s0 : protocol_state) (ts : list protocol_state) : Prop :=
  filtered_finite_trace (fun s => s = s0) ts. 
           

(* finite traces originating in the set of initial states *)

Definition protocol_finite_trace_prop
  {message}
  `{V : VLSM message}
  (ts : list protocol_state)
  : Prop
  := filtered_finite_trace initial_protocol_state_prop ts.

(* infinite traces originating in a set *)

Definition filtered_infinite_trace
  {message}
  `{V : VLSM message}
  (subset : protocol_state -> Prop)
  (ts : Stream protocol_state)
  : Prop
  :=
  subset (hd ts) /\ infinite_trace_from (hd ts) ts.

(* infinite traces originating in the set of initial states *)

Definition protocol_infinite_trace_prop
  {message}
  `{V : VLSM message}
  (ts : Stream protocol_state)
  : Prop
  := filtered_infinite_trace initial_protocol_state_prop ts.

(* a protocol trace is a (finite or infinite) trace,
originating in the set of initial states *)

Definition protocol_trace_prop
  {message}
  `{V : VLSM message}
  (t : Trace)
  : Prop
  :=
  match t with
  | Finite ts => protocol_finite_trace_prop ts
  | Infinite ts => protocol_infinite_trace_prop ts
  end.

Definition protocol_trace
  {message}
  `{V : VLSM message}
  : Type := { t : Trace | protocol_trace_prop t}.

Definition protocol_trace_proj1
  `{VLSM}
  (tr : protocol_trace) 
  : Trace := proj1_sig tr.

Coercion protocol_trace_proj1 : protocol_trace >-> Trace.

(* a protocol trace segment is a (finite or infinite) trace, 
originating in some set of states *)
Definition protocol_trace_from_prop `{VLSM} (P : protocol_state -> Prop) (t : Trace) : Prop :=
  match t with
  | Finite ts => filtered_finite_trace P ts 
  | Infinite ts => filtered_infinite_trace P ts
  end.

Definition protocol_trace_from `{VLSM} (P : protocol_state -> Prop) : Type :=
  { t : Trace | protocol_trace_from_prop P t}. 

Definition protocol_trace_from_proj1
  `{VLSM} {P}
  (tr : protocol_trace_from P) 
  : Trace := proj1_sig tr.

Coercion protocol_trace_from_proj1 : protocol_trace_from >-> Trace.

Definition first
  {message}
  `{V : VLSM message}
  (pt : protocol_trace) : protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact h.
  - destruct t as [h t].
    exact h.
Defined.

Definition last
  {message}
  `{V : VLSM message}
  (pt : protocol_trace) : option protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact (Some (last t h)).
  - exact None.
Defined.

Lemma extend_protocol_trace
  {message}
  `{V : VLSM message}
  : forall (pt2 : protocol_trace) s2 s3,
  last pt2 = Some s2 ->
  valid_transition s2 s3 ->
  exists (pt3 : protocol_trace),  last pt3 = Some s3.
Proof.
  intros [[t2 | t2] Hpt2] s2 s3 Hlast2 Hv.
  - unfold protocol_trace_prop in Hpt2. unfold protocol_finite_trace_prop in Hpt2. unfold filtered_finite_trace in Hpt2.
    destruct t2 as [| s1 [| s1' t2]]; try contradiction.
    destruct Hpt2 as [His1 Ht12]. simpl in Hlast2. simpl in Ht12. inversion Hlast2 as [Hlast2']. rewrite Hlast2' in Ht12.
    apply (extend_trace_from_to_right s1 s2 s3) in Ht12; try assumption.
    assert (Hpt3 : protocol_trace_prop (Finite ((s1 :: s1' :: t2) ++ [s3]))).
    { unfold protocol_trace_prop. unfold protocol_finite_trace_prop. unfold filtered_finite_trace. simpl.
      rewrite last_is_last. split; try assumption. destruct t2; assumption.
    }
    exists (exist _ (Finite ((s1 :: s1' :: t2) ++ [s3])) Hpt3).
    simpl. apply f_equal. rewrite last_is_last. destruct t2; reflexivity.
  - simpl in Hlast2. inversion Hlast2.
Qed.

(* Any protocol state is reachable through a (finite) protocol_trace. *)
Lemma protocol_state_reachable
  {message}
  `{V : VLSM message}
  : forall ps : protocol_state,
  initial_state_prop (proj1_sig ps) \/
  exists t : protocol_trace,
  exists ps' : protocol_state,
  last t = Some ps' /\ proj1_sig ps = proj1_sig ps'.
Proof.
  apply (protocol_state_ind
    (fun s => 
      initial_state_prop s \/ 
      exists t : protocol_trace, exists ps' : protocol_state, last t = Some ps' /\ s = proj1_sig ps'
    )); intros.
  - left. destruct is as [s His]. assumption.
  - right.
    remember (fst (protocol_transition l (s, om))) as s'.
    assert (Hps' : protocol_state_prop s') by
        (apply protocol_state_prop_iff; right; exists s; exists l; exists om; split; assumption).
    remember (exist _ s' Hps') as ps'.
    assert (Hvt : valid_transition s ps').
    { subst. exists om. exists l. split; try assumption. reflexivity. }
    destruct Hind as [His | Hstep]
    + remember (exist _ (proj1_sig s) His) as is.
      assert (Hips : initial_protocol_state_prop s)
        by (subst; unfold initial_protocol_state_prop; assumption).
      assert (Pt : trace_from_to s ps' [s; ps']) by (apply trace_from_to_one; assumption).
      assert (Hpt : protocol_trace_prop (Finite [s; ps']))  by (split; assumption).
      exists (exist _ (Finite [s; ps']) Hpt). exists ps'. subst. simpl. split; reflexivity.
    + destruct Hstep as [pt [ps [Heq_last Heq_s]]].
      assert (s = ps) by (destruct s; destruct ps; simpl in Heq_s; subst; apply f_equal; apply proof_irrelevance).
      rewrite H in Hvt.
      apply (extend_protocol_trace pt ps ps') in Hvt; try assumption.
      destruct Hvt as [pt' Hlast].
      exists pt'. exists ps'. split; subst; auto.
Qed.
  
(* Since we already assume choice etc., might as well make it into a function *) 

(* A final state is one which is stuck (no further valid transition is possible) *)

Definition final_state_prop
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  : Prop
  :=
  ~ exists s' : protocol_state, valid_transition s s'.

Definition final_state
  {message}
  `{V : VLSM message}
  : Type := { s : protocol_state | final_state_prop s}.

(* A terminating trace is a finite protocol_trace ending in a final state *)

Definition terminating_trace_prop
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  match last t with
  | Some ps => final_state_prop ps
  | None => False
  end.

Definition infinite_trace_prop
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  last t = None.

(* A complete trace is either inifinite or terminating  *)

Definition complete_trace_prop
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  infinite_trace_prop t \/ terminating_trace_prop t.
