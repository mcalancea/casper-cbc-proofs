(* 2.2.1 VLSM Parameters *)

Class LSM_sig (message : Type) :=
  { state : Type
  ; label : Type
  ; proto_message_prop : message -> Prop
  ; proto_message_decidable : forall m, {proto_message_prop m} + {~ proto_message_prop m}
  ; proto_message := { m : message | proto_message_prop m }
  ; initial_state_prop : state -> Prop
  ; initial_state := { s : state | initial_state_prop s }
  ; initial_message_prop : proto_message -> Prop
  ; initial_message := { m : proto_message | initial_message_prop m }
  ; protocol_state_inhabited : inhabited initial_state
  ; message_inhabited : inhabited proto_message
  ; label_inhabited : inhabited label
  }.

Class PLSM (message : Type) `{Sig : LSM_sig message} :=
  { ptransition : label -> state * option proto_message -> option (state * option proto_message)
  }.

Class LSM (message : Type) `{Sig : LSM_sig message } :=
  { transition : label -> state * option proto_message -> state * option proto_message
  }.

Class VLSM (message : Type) `{L : LSM message } :=
  { valid : label -> state * option proto_message -> Prop
  }.


Definition ptransition_to_transition
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  (l : label)
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
  (l : label)
  (som :  state * option proto_message)
  : Prop
  :=
  ptransition l som = None
  .

Definition PLSM_LSM_instance
  {message}
  {Sig : LSM_sig message}
  `(PM : @PLSM message Sig)
  : @LSM message Sig
  :=
  {|  transition := ptransition_to_transition
  |}.

Definition PLSM_VLSM_instance
  {message}
  {Sig : LSM_sig message}
  `(PM : @PLSM message Sig)
  : @VLSM message Sig (PLSM_LSM_instance PM)
  :=
  {|  valid := ptransition_to_valid
  |}.

Class VLSM_vdecidable (message : Type) `{M : VLSM message} :=
  { valid_decidable : forall l som, {valid l som} + {~valid l som} 
  }.

Definition transition_valid_ptransition
  {message}
  {Sig : LSM_sig message}
  {LM : @LSM message Sig}
  {VM : @VLSM message Sig LM}
  `{DVM : @VLSM_vdecidable message Sig LM VM}
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
  {LM : @LSM message Sig}
  {VM : @VLSM message Sig LM}
  `(DVM : @VLSM_vdecidable message Sig LM VM)
  : @PLSM message Sig
  :=
  {|  ptransition := transition_valid_ptransition
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


Lemma valid_transition_proof_irrelevance
  {message}
  `{V : VLSM message}
  (ps1 ps1' : protocol_state)
  (Hv : valid_transition ps1 ps1')
  (ps2 : protocol_state)
  (Heq_s : proj1_sig ps1 = proj1_sig ps2)
  : valid_transition ps2 ps1'.
Proof.
  destruct ps1 as [s1 Hps1]. destruct ps2 as [s2 Hps2]. simpl in Heq_s. subst.
  destruct Hv as [opm [l [Hv Ht]]].
  exists opm. exists l. 
  split; try assumption.
Qed.

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

