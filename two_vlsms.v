Require Import Logic.FunctionalExtensionality.

From Casper
Require Import vlsm.

Definition composed2_proto_message_prop
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (m : message) : Prop
  :=
  (@proto_message_prop _ S1 m) \/ (@proto_message_prop _ S2 m).

Lemma composed2_proto_message_decidable
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  : forall m : message, {composed2_proto_message_prop S1 S2 m} + {~ composed2_proto_message_prop S1 S2 m}.
Proof.
  intros.
  destruct (@proto_message_decidable _ S1 m) as [Hm1 | Hm1'].
  - left. left. assumption.
  - destruct (@proto_message_decidable _ S2 m) as [Hm2 | Hm2'].
    + left. right. apply Hm2.
    + right. intros H. destruct H as [H | H]; contradiction.
Qed.

Definition composed2_proto_message
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  :=
  { m : message | composed2_proto_message_prop S1 S2 m }.

Definition composed2_initial_state_prop
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (s : (@state message S1) * (@state message S2)) : Prop
  :=
  match s with
  | (s1, s2) => initial_state_prop s1 /\ initial_state_prop s2
  end.

Definition composed2_initial_state
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  :=
  { s : (@state message S1) * (@state message S2) | composed2_initial_state_prop S1 S2 s }.

Lemma composed2_protocol_state_inhabited
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  : inhabited (composed2_initial_state S1 S2).
Proof.
  destruct (@protocol_state_inhabited message S1) as [s1].
  destruct (@protocol_state_inhabited message S2) as [s2].
  destruct s1 as [i1 Hi1]. destruct s2 as [i2 Hi2].
  constructor. exists (i1, i2). split; assumption.
Qed.

Definition composed2_initial_message_prop
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (m : composed2_proto_message S1 S2) : Prop.
destruct m as [m Hm].
destruct (@proto_message_decidable _ S1 m) as [H1 | _]; destruct (@proto_message_decidable _ S2 m) as [H2 | _].
- exact (initial_message_prop (exist _ m H1) \/ initial_message_prop (exist _ m H2)).
- exact (initial_message_prop (exist _ m H1)).
- exact (initial_message_prop (exist _ m H2)).
- exact False.
Defined.

Lemma composed2_message_inhabited
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  : inhabited (composed2_proto_message S1 S2)
  .
Proof.
  destruct (@message_inhabited message S1) as [[m Hm]].
  constructor.  exists m. left. assumption.
Qed.

Lemma composed2_label_inhabited
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  : inhabited ((@label message S1) + (@label message S2)).
Proof.
  destruct (@label_inhabited message S1) as [l].
  constructor.  left.  exact l.
Qed.


Definition lift_proto_message1
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (m1 : @proto_message _ S1)
  : composed2_proto_message S1 S2.
destruct m1 as [m1 Hm1].
exists m1.
unfold composed2_proto_message_prop. left. assumption.
Defined.


Definition lift_proto_message2
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (m2 : @proto_message _ S2)
  : composed2_proto_message S1 S2.
destruct m2 as [m2 Hm2].
exists m2.
unfold composed2_proto_message_prop. right. assumption.
Defined.

Definition composed2_sig
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  : LSM_sig message
  :=
  {| state := (@state message S1) * (@state message S2)
  ; label := (@label message S1) + (@label message S2)
  ; proto_message_prop := composed2_proto_message_prop S1 S2
  ; proto_message_decidable := composed2_proto_message_decidable S1 S2
  ; initial_state_prop := composed2_initial_state_prop S1 S2
  ; protocol_state_inhabited := composed2_protocol_state_inhabited S1 S2
  ; initial_message_prop := composed2_initial_message_prop S1 S2
  ; message_inhabited := composed2_message_inhabited S1 S2
  ; label_inhabited := composed2_label_inhabited S1 S2
  |}.


Definition composed2_ptransition
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @PLSM message S1)
  (M2 : @PLSM message S2)
  (l : @label message (composed2_sig S1 S2))
  (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  : option (@state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2))).
destruct som as [[s1 s2] [[m Hm]|]].
- destruct l as [l1 | l2].
  + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
    * destruct (ptransition l1 (s1, Some (exist _ m H1))) as [som'|].
      { exact (Some ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som'))). }
      exact None.
    * exact None.
  + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
    * destruct (ptransition l2 (s2, Some (exist _ m H2))) as [som'|].
      { exact (Some ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som'))). }
      exact None.
    * exact None.
- destruct l as [l1 | l2].
  + destruct (ptransition l1 (s1, None)) as [som'|].
    * exact (Some ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som'))).
    * exact None.
  + destruct (ptransition l2 (s2, None)) as [som'|].
    * exact (Some ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som'))).
    * exact None.
Defined.

Definition composed2_plsm
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @PLSM message S1)
  (M2 : @PLSM message S2)
  : @PLSM message (composed2_sig S1 S2)
  :=
  {|  ptransition := composed2_ptransition M1 M2
  |}.

Definition composed2_transition
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (l : @label message (composed2_sig S1 S2))
  (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)).
destruct som as [[s1 s2] [[m Hm]|]].
- destruct l as [l1 | l2].
  + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
    * remember (transition l1 (s1, Some (exist _ m H1))) as som'.
      exact ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som')).
    * exact ((s1, s2), None).
  + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
    * remember (transition l2 (s2, Some (exist _ m H2))) as som'.
      exact ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som')).
    * exact ((s1, s2), None).
- destruct l as [l1 | l2].
  + remember (transition l1 (s1, None)) as som'.
    exact ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som')).
  + remember (transition l2 (s2, None)) as som'.
      exact ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som')).
Defined.

Definition composed2_valid
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (l : @label message (composed2_sig S1 S2))
  (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
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

Definition composed2_vlsm
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  : @VLSM message (composed2_sig S1 S2)
  :=
  {|  transition := composed2_transition M1 M2
  ;   valid := composed2_valid M1 M2
  |}.


Definition composed2_valid_decidable
  {message}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  (DS1 : @VLSM_vdecidable message S1 M1)
  (DS2 : @VLSM_vdecidable message S2 M2)
  (l : @label message (composed2_sig S1 S2))
  (som : @state _ (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  : {@valid _ _ (composed2_vlsm M1 M2) l som} + {~@valid _ _ (composed2_vlsm M1 M2) l som}.
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

Definition composed2_vlsm_vdecidable
  {message}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  (DS1 : @VLSM_vdecidable message S1 M1)
  (DS2 : @VLSM_vdecidable message S2 M2)
  : @VLSM_vdecidable message _ (composed2_vlsm M1 M2)
  :=
  {|
    valid_decidable := composed2_valid_decidable DS1 DS2
  |}.

Definition composed2_ptransition_constrained
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @PLSM message S1)
  (M2 : @PLSM message S2)
  {constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  (l : @label message (composed2_sig S1 S2))
  (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  : option (@state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  :=
  if constraint_decidable l som then composed2_ptransition M1 M2 l som else None.

Definition composed2_plsm_constrained
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @PLSM message S1)
  (M2 : @PLSM message S2)
  {constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  : @PLSM message (composed2_sig S1 S2)
  :=
  {|  ptransition := composed2_ptransition_constrained M1 M2 constraint_decidable
  |}.

Definition composed2_valid_constrained
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (constraint : @label message (composed2_sig S1 S2) -> @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)) -> Prop)
  (l : @label message (composed2_sig S1 S2))
  (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  :=
  composed2_valid M1 M2 l som /\ constraint l som.

Definition composed2_vlsm_constrained
  {message}
  {S1 : LSM_sig message}
  {S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop)
  : @VLSM message (composed2_sig S1 S2)
  :=
  {|  transition := composed2_transition M1 M2
  ;   valid := composed2_valid_constrained M1 M2 constraint
  |}.

Definition composed2_constrained_valid_decidable
  {message}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  (DS1 : @VLSM_vdecidable message S1 M1)
  (DS2 : @VLSM_vdecidable message S2 M2)
  {constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  (l : @label message (composed2_sig S1 S2))
  (som : @state _ (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  : {@valid _ _ (composed2_vlsm_constrained M1 M2 constraint) l som} + {~@valid _ _ (composed2_vlsm_constrained M1 M2 constraint) l som}.
unfold label in l; simpl in l.
unfold state in som. unfold proto_message in som. simpl in som.
unfold valid; simpl.
destruct (constraint_decidable l som) as [Hc | Hnc].
- destruct (composed2_valid_decidable DS1 DS2 l som) as [Hv | Hnv].
  + left. split; try assumption.
  + right. intros [Hv _]. contradiction.
- right. intros [_ Hc]. contradiction.
Defined.

Definition composed2_vlsm_constrained_vdecidable
  {message}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  (DS1 : @VLSM_vdecidable message S1 M1)
  (DS2 : @VLSM_vdecidable message S2 M2)
  {constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  : @VLSM_vdecidable message _ (composed2_vlsm_constrained M1 M2 constraint)
  :=
  {|
    valid_decidable := composed2_constrained_valid_decidable DS1 DS2 constraint_decidable
  |}.

Lemma composed2_partial_composition_commute
  {message}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  (DS1 : @VLSM_vdecidable message S1 M1)
  (DS2 : @VLSM_vdecidable message S2 M2)
  : let PM12 := DVLSM_PLSM_instance (composed2_vlsm_vdecidable DS1 DS2) in
    let PM12' := composed2_plsm (DVLSM_PLSM_instance DS1) (DVLSM_PLSM_instance DS2) in
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
  {message}
  {S1 S2 : LSM_sig message}
  {M1 : @VLSM message S1}
  {M2 : @VLSM message S2}
  (DS1 : @VLSM_vdecidable message S1 M1)
  (DS2 : @VLSM_vdecidable message S2 M2)
  {constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop}
  (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
  : let PM12 := DVLSM_PLSM_instance (composed2_vlsm_constrained_vdecidable DS1 DS2 constraint_decidable) in
    let PM12' := composed2_plsm_constrained (DVLSM_PLSM_instance DS1) (DVLSM_PLSM_instance DS2) constraint_decidable in
    @ptransition _ _ PM12 = @ptransition _ _ PM12'.
Proof.
  intros.
  apply functional_extensionality; intros [l1 | l2]; apply functional_extensionality; intros [[s1 s2] [[m Hm]|]]
  ; unfold ptransition; simpl
  ; unfold transition_valid_ptransition; unfold composed2_ptransition_constrained
  ; unfold valid_decidable; simpl 
  ; unfold composed2_constrained_valid_decidable; simpl
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
  ; unfold valid_decidable; destruct DS1 as [valid_decidable1]; destruct DS2 as [valid_decidable2]; simpl
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
