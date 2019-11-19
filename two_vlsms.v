Require Import Logic.FunctionalExtensionality.

From Casper
Require Import vlsm.

Section Two_VLSMs.

  Context (message : Type) (S1 : LSM_sig message) (S2 : LSM_sig message). 

  Definition composed2_proto_message_prop (m : message) : Prop :=
    (@proto_message_prop _ S1 m) \/ (@proto_message_prop _ S2 m).

  Lemma composed2_proto_message_decidable
    : forall m : message, {composed2_proto_message_prop m} + {~ composed2_proto_message_prop m}.
  Proof.
    intros.
    destruct (@proto_message_decidable _ S1 m) as [Hm1 | Hm1'].
    - left. left. assumption.
    - destruct (@proto_message_decidable _ S2 m) as [Hm2 | Hm2'].
      + left. right. apply Hm2.
      + right. intros H. destruct H as [H | H]; contradiction.
  Qed.

  Definition composed2_proto_message :=
    { m : message | composed2_proto_message_prop m }.

  Definition composed2_initial_state_prop (s : (@state message S1) * (@state message S2)) : Prop
    :=
      match s with
      | (s1, s2) => initial_state_prop s1 /\ initial_state_prop s2
      end.

  Definition composed2_initial_state :=
    { s : (@state message S1) * (@state message S2) | composed2_initial_state_prop s }.

  Lemma composed2_protocol_state_inhabited : inhabited composed2_initial_state.
  Proof.
    destruct (@protocol_state_inhabited message S1) as [s1].
    destruct (@protocol_state_inhabited message S2) as [s2].
    destruct s1 as [i1 Hi1]. destruct s2 as [i2 Hi2].
    constructor. exists (i1, i2). split; assumption.
  Qed.

  Definition composed2_initial_message_prop (m : composed2_proto_message) : Prop.
    destruct m as [m Hm].
    destruct (@proto_message_decidable _ S1 m) as [H1 | _]; destruct (@proto_message_decidable _ S2 m) as [H2 | _].
    - exact (initial_message_prop (exist _ m H1) \/ initial_message_prop (exist _ m H2)).
    - exact (initial_message_prop (exist _ m H1)).
    - exact (initial_message_prop (exist _ m H2)).
    - exact False.
  Defined.

  Lemma composed2_message_inhabited : inhabited composed2_proto_message.
  Proof.
    destruct (@message_inhabited message S1) as [[m Hm]].
    constructor.  exists m. left. assumption.
  Qed.

  Definition lift_proto_message1 (m1 : @proto_message message S1) : composed2_proto_message.
    destruct m1 as [m1 Hm1].
    exists m1.
    unfold composed2_proto_message_prop. left. assumption.
  Defined.

  Definition lift_proto_message2 (m2 : @proto_message _ S2) : composed2_proto_message.
    destruct m2 as [m2 Hm2].
    exists m2.
    unfold composed2_proto_message_prop. right. assumption.
  Defined.

  Instance composed2_sig : LSM_sig message :=
    {| state := (@state message S1) * (@state message S2) 
       ; proto_message_prop := composed2_proto_message_prop 
       ; proto_message_decidable := composed2_proto_message_decidable 
       ; initial_state_prop := composed2_initial_state_prop 
       ; protocol_state_inhabited := composed2_protocol_state_inhabited 
       ; initial_message_prop := composed2_initial_message_prop 
       ; message_inhabited := composed2_message_inhabited 
    |}.

  Context (M1 : @PLSM message S1) (M2 : @PLSM message S2). 

  Definition composed2_plabel := sum (@plabel message S1 M1) (@plabel message S2 M2).

  Lemma composed2_plabel_inhabited : inhabited composed2_plabel. 
  Proof.
    destruct (@plabel_inhabited message S1 M1). 
    constructor. left. exact X.
  Qed.

  Definition composed2_ptransition (l : composed2_plabel) 
             (som : @state message composed2_sig * option (@proto_message _ composed2_sig))
    : option (@state message composed2_sig * option (@proto_message _ composed2_sig)).
    destruct som as [[s1 s2] [[m Hm]|]].
    - destruct l as [l1 | l2].
      + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
        * destruct (ptransition l1 (s1, Some (exist _ m H1))) as [som'|].
          { exact (Some ((fst som', s2), option_map lift_proto_message1 (snd som'))). }
          exact None.
        * exact None.
      + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
        * destruct (ptransition l2 (s2, Some (exist _ m H2))) as [som'|].
          { exact (Some ((s1, fst som'), option_map lift_proto_message2 (snd som'))). }
          exact None.
        * exact None.
    - destruct l as [l1 | l2].
      + destruct (ptransition l1 (s1, None)) as [som'|].
        * exact (Some ((fst som', s2), option_map lift_proto_message1 (snd som'))).
        * exact None.
      + destruct (ptransition l2 (s2, None)) as [som'|].
        * exact (Some ((s1, fst som'), option_map lift_proto_message2 (snd som'))).
        * exact None.
  Defined.
  
  Instance composed2_plsm: @PLSM message composed2_sig
    :=
      {|  plabel := composed2_plabel;
          plabel_inhabited := composed2_plabel_inhabited;
          ptransition := composed2_ptransition
      |}.

  Context (V1 : @VLSM message S1) (V2 : @VLSM message S2). 

  Definition composed2_label := sum (@label message S1 V1) (@label message S2 V2).

  Lemma composed2_label_inhabited : inhabited composed2_label. 
  Proof.
    destruct (@label_inhabited message S1 V1). 
    constructor. left. exact X.
  Qed.
  
  Definition composed2_transition
             (l : composed2_label)
             (som : @state message composed2_sig * option (@proto_message _ composed2_sig))
    : @state message composed2_sig * option (@proto_message _ composed2_sig).
    destruct som as [[s1 s2] [[m Hm]|]].
    - destruct l as [l1 | l2].
      + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
        * remember (transition l1 (s1, Some (exist _ m H1))) as som'.
          exact ((fst som', s2), option_map lift_proto_message1 (snd som')).
    * exact ((s1, s2), None).
  + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
    * remember (transition l2 (s2, Some (exist _ m H2))) as som'.
      exact ((s1, fst som'), option_map lift_proto_message2 (snd som')).
    * exact ((s1, s2), None).
- destruct l as [l1 | l2].
  + remember (transition l1 (s1, None)) as som'.
    exact ((fst som', s2), option_map lift_proto_message1 (snd som')).
  + remember (transition l2 (s2, None)) as som'.
      exact ((s1, fst som'), option_map lift_proto_message2 (snd som')).
Defined.

  Definition composed2_valid (l : composed2_label) (som : @state message composed2_sig * option (@proto_message _ composed2_sig))
    : Prop.
    destruct som as [[s1 s2] [[m Hm]|]].
    - destruct l as [l1 | l2].
      + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
        * exact (valid l1 (s1, Some (exist _ m H1))).
        * exact False.
      + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
        * exact (valid l2 (s2, Some (exist _ m H2))).
        * exact False.
    - destruct l as [l1 | l2].
      + exact (valid l1 (s1, None)).
      + exact (valid l2 (s2, None)).
  Defined.

  Instance composed2_vlsm : @VLSM message composed2_sig :=
    {|  label := composed2_label;
        label_inhabited := composed2_label_inhabited;
        transition := composed2_transition;
        valid := composed2_valid
    |}.

  Context (DV1 : @VLSM_vdecidable message S1 V1)
          (DV2 : @VLSM_vdecidable message S2 V2).
  
  Definition composed2_valid_decidable (l : @label message composed2_sig composed2_vlsm) (som : @state _ composed2_sig * option (@proto_message _ composed2_sig))
    : {@valid _ _ composed2_vlsm l som} + {~@valid _ _ composed2_vlsm l som}.
    destruct som as [[s1 s2] [[m Hm]|]].
    - destruct l as [l1 | l2]; simpl.
      + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
        * apply valid_decidable.
        * right. intro. assumption.
      + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
        * apply valid_decidable.
        * right. intro. assumption.
    - destruct l as [l1 | l2]; simpl; apply valid_decidable.
  Defined.

  Instance composed2_vlsm_vdecidable : @VLSM_vdecidable message _ composed2_vlsm :=
    {|
      valid_decidable := composed2_valid_decidable
    |}.

  Definition composed2_ptransition_constrained
             {constraint : composed2_plabel -> ((@state message S1) * (@state message S2)) * option composed2_proto_message -> Prop}
             (constraint_decidable : forall (l : composed2_plabel) (som : ((@state message S1) * (@state message S2)) * option composed2_proto_message), {constraint l som} + {~constraint l som})
             (l : composed2_plabel)
             (som : @state message composed2_sig * option (@proto_message _ composed2_sig))
    : option (@state message composed2_sig * option (@proto_message _ composed2_sig))
    :=
      if constraint_decidable l som then composed2_ptransition l som else None.

  Instance composed2_plsm_constrained
             {constraint : composed2_plabel -> ((@state message S1) * (@state message S2)) * option composed2_proto_message -> Prop}
             (constraint_decidable : forall (l : composed2_plabel) (som : ((@state message S1) * (@state message S2)) * option composed2_proto_message), {constraint l som} + {~constraint l som})
    : @PLSM message composed2_sig
    :=
      {|  plabel := composed2_plabel;
          plabel_inhabited := composed2_plabel_inhabited;
          ptransition := composed2_ptransition_constrained constraint_decidable
      |}.

  Definition composed2_valid_constrained
             (constraint : composed2_label -> @state message composed2_sig * option (@proto_message _ composed2_sig) -> Prop)
             (l : composed2_label)
             (som : @state message composed2_sig * option (@proto_message _ composed2_sig))
    :=
      composed2_valid l som /\ constraint l som.

  Instance composed2_vlsm_constrained
             (constraint : composed2_label -> (@state message S1 * @state message S2) * option composed2_proto_message -> Prop)
    : @VLSM message composed2_sig
    :=
      {|
        label := composed2_label;
        label_inhabited := composed2_label_inhabited;
        transition := composed2_transition;
        valid := composed2_valid_constrained constraint
      |}.

  Program Instance composed2_vlsm_constrained_vdecidable
             {constraint : composed2_label -> (@state message S1 * @state message S2) * option composed2_proto_message -> Prop}
             (constraint_decidable : forall (l : composed2_label) (som : ((@state message S1) * (@state message S2)) * option composed2_proto_message), {constraint l som} + {~constraint l som})
    : @VLSM_vdecidable message _ (composed2_vlsm_constrained constraint)
    :=
      {|
        valid_decidable := _ (* composed2_constrained_valid_decidable constraint_decidable *)
      |}.
  Next Obligation. 
    remember ((s,s0), o) as som. 
    unfold label in l; simpl in l.
    unfold proto_message in som. 
    simpl in som. 
    destruct (constraint_decidable l som) as [Hc | Hnc].
    - destruct (composed2_valid_decidable l som) as [Hv | Hnv].
      + left. split; try assumption.
      + right. intros [Hv _]. contradiction.
    - right. intros [_ Hc]. contradiction.
  Defined.

End Two_VLSMs. 


Section VLSM_Commutation. 

  Context {message : Type}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  {DS1 : @VLSM_vdecidable message S1 M1}
  {DS2 : @VLSM_vdecidable message S2 M2}
  {constraint : (@label message S1 M1) + (@label message S2 M2) -> (@state message S1 * @state message S2) * option (composed2_proto_message message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1 M1) + (@label message S2 M2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message message S1 S2)), {constraint l som} + {~constraint l som}). 

  Lemma composed2_partial_composition_commute
    : let PM12 := DVLSM_PLSM_instance (composed2_vlsm_vdecidable message S1 S2 M1 M2 DS1 DS2) in
      let PM12' := composed2_plsm message S1 S2 (DVLSM_PLSM_instance DS1) (DVLSM_PLSM_instance DS2) in
      @ptransition _ _ PM12 = @ptransition _ _ PM12'.
  Proof.
    intros.
    apply functional_extensionality; intros [l1 | l2]; apply functional_extensionality; intros [[s1 s2] [[m Hm]|]];
      unfold ptransition; simpl;
        unfold transition_valid_ptransition; unfold valid_decidable; simpl; try destruct (proto_message_decidable m) as [Hpm | Hnpm]; try reflexivity
        ; destruct DS1 as [valid_decidable1]; destruct DS2 as [valid_decidable2]; simpl
    .
    - destruct (valid_decidable1 l1 (s1, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable1 l1 (s1, None)) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, None)) as [Hv | Hnv]; reflexivity.
  Qed.


  Lemma composed2_constrained_partial_composition_commute
  : let PM12 := DVLSM_PLSM_instance (composed2_vlsm_constrained_vdecidable message S1 S2 M1 M2 DS1 DS2 constraint_decidable) in
    let PM12' := composed2_plsm_constrained message S1 S2 (DVLSM_PLSM_instance DS1) (DVLSM_PLSM_instance DS2) constraint_decidable in
    @ptransition _ _ PM12 = @ptransition _ _ PM12'.
  Proof.
    (*
    intros. 
    apply functional_extensionality; intros [l1 | l2]; apply functional_extensionality; intros [[s1 s2] [[m Hm]|]]
    ; unfold ptransition; simpl
    ; unfold transition_valid_ptransition; unfold composed2_ptransition_constrained
    ; unfold valid_decidable; simpl 
    ; unfold valid_decidable; simpl
    ; unfold composed2_valid_constrained; simpl
    ; try destruct
          (constraint_decidable (@inl (@label message S1) (@label message S2) l1)
                                (s1, s2,
                                 @Some (@proto_message message (@composed2_sig message S1 S2))
        (@exist message
           (fun m0 : message => @composed2_proto_message_prop message S1 S2 m0) m Hm))
    )
  ; try reflexivity
  ; try destruct
    (constraint_decidable (@inl (@label message S1) (@label message S2) l1)
      (s1, s2, @None (@proto_message message (@composed2_sig message S1 S2)))
    )
  ; try reflexivity
  ; try destruct
    (constraint_decidable (@inr (@label message S1) (@label message S2) l2)
      (s1, s2,
      @Some (@proto_message message (@composed2_sig message S1 S2))
        (@exist message
           (fun m0 : message => @composed2_proto_message_prop message S1 S2 m0) m Hm))
    )
  ; try reflexivity
  ; try destruct
    (constraint_decidable (@inr (@label message S1) (@label message S2) l2)
      (s1, s2, @None (@proto_message message (@composed2_sig message S1 S2)))
    )
  ; try reflexivity
  ; unfold transition_valid_ptransition; simpl
  ; unfold (@valid_decidable _ _ composed2_vlsm_contrained); destruct DS1 as [valid_decidable1]; destruct DS2 as [valid_decidable2]; simpl
  ; try destruct (proto_message_decidable m) as [Hpm | Hnpm]
  ; try reflexivity
  .
  - destruct (valid_decidable1 l1 (s1, Some (exist proto_message_prop m Hpm))); reflexivity.
  - destruct (valid_decidable1 l1 (s1, Some (exist proto_message_prop m Hpm))); reflexivity.
  - destruct (valid_decidable1 l1 (s1, None)) as [Hv | Hnv]; reflexivity.
  - destruct (valid_decidable2 l2 (s2, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
  - destruct (valid_decidable2 l2 (s2, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
  - destruct (valid_decidable2 l2 (s2, None)) as [Hv | Hnv]; reflexivity.
  Qed.

     *)
  Admitted.

End VLSM_Commutation. 
