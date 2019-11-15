From Casper
Require Import vlsm composed_vlsm non_constructive.

Definition vlsm_projection_initial_state_prop
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  (is : istate i)
  : Prop
  :=
  exists s : initial_state, istate_proj i (proj1_sig s) = proj1_sig is.

Definition vlsm_projection_initial_state
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  :=
  { s : istate i | vlsm_projection_initial_state_prop i s }.

Lemma vlsm_projection_protocol_state_inhabited
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  : inhabited (vlsm_projection_initial_state i).
Proof.
  destruct protocol_state_inhabited as [s].
  remember (proj_istate (proj1_sig s) i) as iis.
  assert (Hiis : vlsm_projection_initial_state_prop i iis)
    by (exists s; subst; reflexivity).
  constructor. exact (exist _ iis Hiis).
Qed.

Definition lift_proto_message
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  (m : {x : message | iproto_message_prop i x})
  : proto_message
  :=
  let m0 := proj1_sig m in
  let Hcm := iproto_message_consistent i m0 (proj2_sig m) in
  (exist _ m0 Hcm).

Definition vlsm_projection_initial_message_prop
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  (m : {x : message | iproto_message_prop i x})
  : Prop
  :=
  initial_message_prop (lift_proto_message i m).


Definition vlsm_sig_projection
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  : LSM_sig (message : Type)
  :=
  {|  state := istate i
  ;   label := ilabel_type i
  ;   proto_message_prop := iproto_message_prop i
  ;   proto_message_decidable := iproto_message_decidable i
  ;   initial_state_prop := vlsm_projection_initial_state_prop i
  ;   initial_message_prop := vlsm_projection_initial_message_prop i
  ;   protocol_state_inhabited := vlsm_projection_protocol_state_inhabited i
  ;   message_inhabited := iproto_message_inhabited i
  ;   label_inhabited := ilabel_type_inhabited i
  |}.

(*   ;   transition := vlsm_projection_transition i
  ;   valid := vlsm_projection_valid i
 *)

Definition transitioning_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom isom' : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  :=
  let (si, om) := isom in
  let (si', om') := isom' in
  exists (s s' : state),
    proj_istate s i = si /\
    proj_istate s' i = si' /\
    transition (proj1_sig il) (s, (option_map (lift_proto_message i) om)) = (s', (option_map (lift_proto_message i) (om')))
  .

Lemma vlsm_projection_transition_existence
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  : exists isom' : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m}, 
      transitioning_projection i il isom isom'.
Proof.
  destruct isom as [is iom].
  destruct il as [l Hl].
  destruct is as [is [s His]].
  remember (option_map (lift_proto_message i) iom) as om.

  destruct (transition l (s, om)) as [s' om'] eqn:Ht.

  destruct om' as [m'|].
  - specialize (transition_projection_message_type_preservation s om l s' m' Ht); intros Hmsg.
    rewrite Hl in Hmsg.
    exists (proj_istate s' i, Some (exist _ (proj1_sig m') Hmsg)).
    exists s. exists s'. rewrite <- His.
    simpl. repeat split; try reflexivity.  rewrite <- Heqom. rewrite Ht.
    apply f_equal. apply f_equal.
    unfold lift_proto_message; simpl.
    apply exist_eq. reflexivity.
  - exists (proj_istate s' i, None).
    exists s. exists s'. rewrite <- His. 
    simpl. repeat split; try reflexivity.
    rewrite <- Heqom.  assumption.
Qed.

Require Import Coq.Logic.IndefiniteDescription.

Definition vlsm_projection_transition
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m}
  :=
  (proj1_sig
    (constructive_indefinite_description
      (transitioning_projection i il isom)
      (vlsm_projection_transition_existence i il isom)
    )
  ).

Definition vlsm_projection_valid
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  : Prop
  :=
  let (si, omi) := isom in
  let om := option_map (lift_proto_message i) omi in
  exists s : state, istate_proj i s = proj1_sig si /\ valid (proj1_sig il) (s, om).

Definition vlsm_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  : @VLSM (message : Type) (vlsm_sig_projection i)
  :=
  {|  transition := vlsm_projection_transition i
  ;   valid := vlsm_projection_valid i
  |}.


Lemma protocol_state_projection
  {message : Type}
  {S : LSM_sig message}
  {V : @VLSM message S}
  {SV : @composed_sig_class _ S}
  `{CV : @composed_vlsm_class message _ SV V}
  : forall (i : index) (s :  protocol_state),
  @protocol_state_prop _ (vlsm_sig_projection i) (vlsm_projection i) (proj_istate (proj1_sig s) i).
Proof.
  intros i [s Hps]. simpl. induction Hps as [is | s s'' l om' Hps Hp Hv Ht| s s'' l m om' Hps Hp Hpm Hv Ht].
  - apply protocol_state_prop_iff. left. 
    remember (proj_istate (proj1_sig is) i) as iis.
    unfold initial_state.
    unfold initial_state_prop; simpl. unfold vlsm_projection_initial_state_prop.
    assert (His : exists s0 : initial_state, istate_proj i (proj1_sig s0) = proj1_sig iis)
      by (exists is; subst; reflexivity).
    exists (exist _ iis His); reflexivity.
  - remember None as om. 
(* 
    assert (Hps' : protocol_state_prop (fst (transition l (s, om)))).
    { apply protocol_state_prop_iff. right. exists (exist _ s Hps). exists l. exists None. 
      unfold protocol_valid; unfold protocol_transition; simpl. split; subst; try assumption; reflexivity. }
 *)
    remember (ilabel l) as j.
    destruct (index_eq_dec i j); subst.
    + apply protocol_state_prop_iff. right.
      exists (exist _ (proj_istate s (ilabel l)) Hp).
      remember (ilabel l) as j. symmetry in Heqj.
      exists (exist _ l Heqj).
      exists None. split.
      * unfold protocol_valid. simpl. exists s. split; try reflexivity. assumption.
      * simpl. unfold vlsm_projection_transition.
(* 
        remember
          (@constructive_indefinite_description
           (prod (@istate message V CV j)
              (option (@sig message (fun m : message => @iproto_message_prop message V CV j m))))
           (@transitioning_projection message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
           (@vlsm_projection_transition_existence message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
          ) as sjom'.
      clear Heqsjom'.
      destruct sjom' as [sjom' Hsjom'].
      rename om' into om''.
      destruct sjom' as [sj' om'].
      destruct Hsjom' as [s0 [s0' Hsjom']]. simpl in Hsjom'.
      destruct Hsjom' as [Heqs0 [Heqs0' Ht0]]. simpl.
      specialize transition_projection_consistency; intros Hpc.
      apply proj_istate_eq in Heqs0.
      specialize (Hpc s0 s None l j Heqs0 Heqj).
      rewrite Ht in Hpc. simpl in Hpc. destruct Hpc as [Hmsg Hst].
      apply proj_istate_eq in Hst. rewrite <- Hst. 
      rewrite Ht0. simpl. assumption.
    + specialize (transition_projection_state_preservation s None l i); intros Htp.
      assert (ni : ilabel l <> i) by (intro; subst; contradiction).
      specialize (Htp ni). rewrite Ht in Htp. simpl in Htp.
      apply proj_istate_eq in Htp.
      rewrite Htp. assumption.
  - remember (Some m) as om.
    remember (ilabel l) as j.
    destruct (index_eq_dec i j); subst.
    + remember (ilabel l) as j.
      destruct m as [m Hm].
      destruct (iproto_message_decidable j m) as [Hmj | Hnmj].
      * specialize (@next_protocol_state_with_message _ (vlsm_projection j)); intros Hpsj'.
        specialize (Hpsj' (proj_istate s j) (proj_istate s'' j)).
        symmetry in Heqj. specialize (Hpsj' (exist _ l Heqj)).
        specialize (Hpsj' (exist _ m Hmj)).
        admit.
      *
      unfold state in Hpsj'. simpl in Hpsj'.
admit.
    + specialize (transition_projection_state_preservation s (Some m) l i); intros Htp.
      assert (ni : ilabel l <> i) by (intro; subst; contradiction).
      specialize (Htp ni). rewrite Ht in Htp. simpl in Htp.
      apply proj_istate_eq in Htp.
      rewrite Htp. assumption.

(* 
    + apply protocol_state_prop_iff. right.
      remember (ilabel l) as j. exists (exist _ (proj_istate s j) Hp).
      symmetry in Heqj.
      exists (exist _ l Heqj).
      
      exists (Some (lift_proto_message j (exist _ m Hpm))). split.
      * unfold protocol_valid. simpl. exists s. split; try reflexivity. assumption.
      * simpl. unfold vlsm_projection_transition.
        remember
          (@constructive_indefinite_description
           (prod (@istate message V CV j)
              (option (@sig message (fun m : message => @iproto_message_prop message V CV j m))))
           (@transitioning_projection message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
           (@vlsm_projection_transition_existance message V CV j
              (@exist (@label message V)
                 (fun l0 : @label message V =>
                  @eq (@index message V CV) (@ilabel message V CV l0) j) l Heqj)
              (@pair (@istate message V CV j)
                 (option (@proto_message message (@vlsm_projection message V CV j)))
                 (@proj_istate message V CV s j)
                 (@None (@proto_message message (@vlsm_projection message V CV j)))))
          ) as sjom'.
      clear Heqsjom'.
      destruct sjom' as [sjom' Hsjom'].
      rename om' into om''.
      destruct sjom' as [sj' om'].
      destruct Hsjom' as [s0 [s0' Hsjom']]. simpl in Hsjom'.
      destruct Hsjom' as [Heqs0 [Heqs0' Ht0]]. simpl.
      specialize transition_projection_consistency; intros Hpc.
      apply proj_istate_eq in Heqs0.
      specialize (Hpc s0 s None l j Heqs0 Heqj).
      rewrite Ht in Hpc. simpl in Hpc. destruct Hpc as [Hmsg Hst].
      apply proj_istate_eq in Hst. rewrite <- Hst. 
      rewrite Ht0. simpl. assumption.
 *)
 *)
Admitted.
