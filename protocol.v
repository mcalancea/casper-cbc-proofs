Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts.
Import ListNotations.  
From Casper
Require Import preamble ListExtras ListSetExtras.

(* Proof irrelevance states that all proofs of the same proposition are equal *) 
Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
 
Lemma proj1_sig_injective {X : Type} :
    forall (P : X -> Prop)
      (x1 x2 : X) (H1 : P x1) (H2 : P x2),
      (exist P x1 H1) = (exist P x2 H2) <-> x1 = x2. 
Proof.
  intros P x1 x2 H1 H2; split.  
  - intro H_eq_dep.
    apply eq_sig_fst in H_eq_dep; assumption.
  - intro H_eq.
    subst. assert (H1 = H2) by eapply proof_irrelevance.
    rewrite H. reflexivity.
Qed.

Lemma sigify_eq_dec {X : Type} `{StrictlyComparable X} :
  forall (P : X -> Prop),
    forall (x1 x2 : {x | P x}), {x1 = x2} + {x1 <> x2}. 
Proof.
  intros P x1 x2;
    destruct x1 as [x1 about_x1];
    destruct x2 as [x2 about_x2].
  simpl.
  destruct (compare_eq_dec x1 x2) as [left | right].
  left. apply proj1_sig_injective; assumption. 
  right. intro Hnot. apply proj1_sig_injective in Hnot.
  contradiction.
Qed.

Program Definition sigify_compare {X} `{StrictlyComparable X} (P : X -> Prop) : {x | P x} -> {x | P x} -> comparison := _. 
Next Obligation.
  exact (compare X0 X1).
Defined.

(* Level 0 : *)
Class PartialOrder :=
  { A : Type;
    A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
    A_inhabited : exists (a0 : A), True; (* ? *) 
    A_rel : A -> A -> Prop;
    A_rel_refl :> Reflexive A_rel;
    A_rel_trans :> Transitive A_rel;
  }.

(* Level 1 : *) 
Class PartialOrderNonLCish `{PartialOrder} :=
  { no_local_confluence_ish : exists (a a1 a2 : A),
        A_rel a a1 /\ A_rel a a2 /\
        ~ exists (a' : A), A_rel a1 a' /\ A_rel a2 a';
  }.

(* Level Specific : *)
Class CBC_protocol_eq :=
   {
      (** Consensus values equipped with reflexive transitive comparison **) 
      consensus_values : Type; 
      about_consensus_values : StrictlyComparable consensus_values; 
      (** Validators equipped with reflexive transitive comparison **) 
      validators : Type; 
      about_validators : StrictlyComparable validators;
      (** Weights are positive reals **) 
      weight : validators -> {r | (r > 0)%R}; 
      (** Threshold is a non-negative real **) 
      t : {r | (r >= 0)%R}; 
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R;
      (** States with equality and union **)
      state : Type;
      about_state : StrictlyComparable state;
      state0 : state;
      state_eq : state -> state -> Prop;
      state_eq_equiv :> Equivalence state_eq;
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1);
      (** Reachability relation **) 
      reach : state -> state -> Prop;
      reach_refl : forall s, reach s s; 
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3; 
      reach_union : forall s1 s2, reach s1 (state_union s1 s2);  
      reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3;  
      (** Total estimator **)
      E : state -> consensus_values -> Prop; 
      estimator_total : forall s, exists c, E s c; 
      (** Protocol state definition as predicate **) 
      prot_state : state -> Prop; 
      about_state0 : prot_state state0; 
      (** Equivocation weights from states **) 
      equivocation_weight : state -> R; 
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R; 
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2);
   }.

Class CBC_protocol_eq_specific `{CBC_protocol_eq} :=
  {
    two_senders : exists (v1 v2 : validators), v1 <> v2;

    (* Being duplicate-free means something different across protocols *)
    state_nodup : state -> Prop;
    prot_state_nodup : forall (s : state), prot_state s ->
                                      state_nodup s;
    nodup_state_reach : forall (s : state), state_nodup s ->
                                       forall (s' : state), reach s' s ->
                                                       state_nodup s';
    protocol_state_incl : forall (s : state), prot_state s ->
                                         forall (s' : state),
                                           state_nodup s' ->
                                           reach s' s ->
                                           prot_state s';
    (* Notion of messages *) 
    message : Type;
    about_message : StrictlyComparable message;


    get_messages : state -> list message;
    justification : message -> state;
    sender : message -> validators;
    add_message : message -> state -> state;

    prot_state_extend_nodup : forall (s : state) (msg : message),
        justification msg = s -> state_nodup (add_message msg s);
    in_state : message -> state -> Prop;
    in_state_correct : forall (msg : message) (s : state),
        in_state msg s <-> In msg (get_messages s);
    in_state_morphism : forall (s1 s2 : state), reach s1 s2 ->
                                           forall (msg : message),
                                             in_state msg s1 ->
                                             in_state msg s2;
    add_message_in_state : forall (msg : message) (s : state), in_state msg (add_message msg s);
    add_message_get_messages_iff : forall sigma msg,
        get_messages (add_message msg sigma) = msg :: get_messages sigma;
    in_state_add_message_iff : forall msg msg' sigma',
        in_state msg (add_message msg' sigma') <->
        msg = msg' \/ in_state msg sigma';
    add_message_rel : forall (msg : message) (s : state), reach s (add_message msg s);

    (* Message-specific equivocation function *)
    equivocating_messages : message -> message -> bool;
    equivocating_messages_comm : forall msg1 msg2, equivocating_messages msg1 msg2 = equivocating_messages msg2 msg1; 
    equivocating_messages_correct : forall msg1 msg2, equivocating_messages msg1 msg2 = true <-> (msg1 <> msg2 /\
                                                                                           sender msg1 = sender msg2 /\
                                                                                          ~ in_state msg1 (justification msg2) /\
                                                                                          ~ in_state msg2 (justification msg1));
    

    (* Now we need to figure out exactly what we need to know about the next equivocation state *) 
    next_equivocation_state : state -> validators -> validators -> state;
    next_equivocation_state_incl : forall (j : state) (v v' : validators), reach j (next_equivocation_state j v v');
    
    next_equivocation_state_nodup : forall j v v',
        state_nodup (next_equivocation_state j v v'); 

    (* This is apparently not enough - we also need to know that we can create a horn from our next equivocation state. *)
    next_equivocation_state_horn : forall (j : state) (v v' : validators), exists msg1 msg2 msg3,
          next_equivocation_state j v v' = add_message msg3 (add_message msg2 (add_message msg1 j)) /\
          equivocating_messages msg2 msg3 = true /\
          sender msg2 = v /\ 
          sender msg1 = v' /\
          justification msg1 = j /\
          prot_state (add_message msg3 j) /\
          prot_state (add_message msg2 (add_message msg1 j)); 
  }.

Definition equivocating_messages_prop `{CBC_protocol_eq_specific} :=
  fun (msg1 msg2 : message) => msg1 <> msg2 /\
                            sender msg1 = sender msg2 /\
                            ~ in_state msg1 (justification msg2) /\
                            ~ in_state msg2 (justification msg1).

Lemma equivocating_messages_correct' `{CBC_protocol_eq_specific} : forall msg1 msg2,
    equivocating_messages msg1 msg2 = false <-> ~ equivocating_messages_prop msg1 msg2. 
Proof.
  intros. 
  apply mirror_reflect_curry.
  apply equivocating_messages_correct.
Qed. 
                                
Definition equivocating_in_state `{CBC_protocol_eq_specific} (msg : message) (sigma : state) : bool :=
  existsb (equivocating_messages msg) (get_messages sigma).

Definition equivocating_in_state_prop `{CBC_protocol_eq_specific} :=
  fun (msg : message) (s : state) =>
    exists (msg' : message), in_state msg' s /\ equivocating_messages_prop msg msg'.

Lemma equivocating_in_state_correct `{CBC_protocol_eq_specific} :
  forall msg s, equivocating_in_state msg s = true <-> equivocating_in_state_prop msg s.
Proof.
  rename H into elephant.
  rename H0 into squirrel.
  intros msg s.
  split; intro H.
  - unfold equivocating_in_state in H.
    rewrite existsb_exists in H.
    destruct H as [msg' [H_in H_equiv]].
    exists msg'. split.
    apply in_state_correct. assumption.
    unfold equivocating_messages_prop.
    rewrite <- equivocating_messages_correct. assumption.
  - destruct H as [msg' [H_in H_equiv]].
    apply existsb_exists.
    exists msg'; split. apply in_state_correct. assumption.
    rewrite equivocating_messages_correct. assumption.
Qed.

Lemma equivocating_in_state_correct' `{CBC_protocol_eq_specific} :
  forall msg s, equivocating_in_state msg s = false <-> ~ equivocating_in_state_prop msg s.
Proof.
  intros. 
  apply mirror_reflect_curry.
  exact equivocating_in_state_correct.
Qed.

Lemma equivocating_in_state_incl `{CBC_protocol_eq_specific} :
  forall sigma sigma',
  reach sigma sigma' ->
  forall msg,
    equivocating_in_state_prop msg sigma ->
    equivocating_in_state_prop msg sigma'.
Proof.
  intros. destruct H2 as [x [Hin Heq]]. exists x.
  split; try assumption.
  now apply in_state_morphism with sigma. 
Qed.

Lemma non_equivocating_messages_sender `{CBC_protocol_eq_specific} : forall msg1 msg2,
  sender msg1 <> sender msg2 ->
  equivocating_messages msg1 msg2 = false.
Proof.
  intros msg1 msg2 Hneq. simpl in Hneq.
Admitted. 

Lemma equivocating_in_state_not_seen `{CBC_protocol_eq_specific} :
  forall (msg : message) (sigma : state),
  ~ In (sender msg) (set_map (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) sender (get_messages sigma)) ->
  ~ equivocating_in_state_prop msg sigma.  
Proof.
  intros msg sigma Hnin. rewrite set_map_exists in Hnin. simpl in Hnin.
  rewrite <- equivocating_in_state_correct'. 
  apply existsb_forall.
  intros msg' Hin.
  apply non_equivocating_messages_sender. simpl.
  intro Heq. subst. apply Hnin.
  exists msg'. split; try assumption. symmetry; assumption.
Qed.

Lemma equivocating_messages_prop_swap `{CBC_protocol_eq_specific} : forall msg1 msg2,
  equivocating_messages_prop msg1 msg2 <-> equivocating_messages_prop msg2 msg1.
Proof.
  intros msg1 msg2.
  unfold equivocating_messages_prop.
  do 2 rewrite <- equivocating_messages_correct.
  split; intro H_true;
  now rewrite equivocating_messages_comm.
Qed.

Definition equivocating_senders `{CBC_protocol_eq_specific} (sigma : state) : set validators :=
  set_map (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) sender
    (filter (fun msg => equivocating_in_state msg sigma)
      (get_messages sigma)).

Definition equivocating_senders_prop `{CBC_protocol_eq_specific} (s : state) (lv : set validators) :=
  forall v, In v lv <-> exists msg, in_state msg s /\ sender msg = v /\ equivocating_in_state_prop msg s. 

Lemma equivocating_senders_correct`{CBC_protocol_eq_specific} : forall s,
    equivocating_senders_prop s (equivocating_senders s).
Proof.
  rename H into elephant.
  rename H0 into squirrel.
  intros s v; split; intro H. 
  - (* Left direction *)
    apply set_map_exists in H.
    destruct H as [msg [H_in H_sender]].
    exists msg.
    apply filter_In in H_in.
    destruct H_in. repeat split; try assumption.
    apply in_state_correct in H.
    assumption.
    rewrite <- equivocating_in_state_correct.
    assumption.
  - destruct H as [msg [H_in [H_sender H_equiv]]]. 
    unfold equivocating_senders.
    rewrite <- H_sender.
    apply set_map_in.
    rewrite filter_In. split.
    apply in_state_correct. assumption.
    rewrite equivocating_in_state_correct.
    assumption.
Qed.

Lemma equivocating_senders_incl `{CBC_protocol_eq_specific} : forall sigma sigma',
  reach sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl.
  apply incl_tran with (filter (fun msg : message => equivocating_in_state msg sigma) (get_messages sigma')).
  - apply filter_incl.
    intros msg H_msg_in.
    apply in_state_correct.
    apply in_state_correct in H_msg_in.
    now apply in_state_morphism with sigma. 
  - intros v H_in.
    rewrite filter_In in *.
    destruct H_in. split. assumption.
    rewrite equivocating_in_state_correct in *.
    now apply equivocating_in_state_incl with sigma.
Qed.

Lemma non_equivocating_messages_extend `{CBC_protocol_eq_specific} : forall msg sigma1,
    In msg (get_messages sigma1) ->
    forall msg',
      justification msg' = sigma1 -> 
      equivocating_messages msg msg' = false.
Proof.
  intros msg; intros.
  apply equivocating_messages_correct'. 
  intros H_absurd.
  destruct H_absurd as [H_msg [H_sender [H_just_l H_just_r]]].
  subst.
  apply in_state_correct in H1.
  contradiction.
Qed.

Lemma equivocating_senders_extend `{CBC_protocol_eq_specific} :
  forall sigma msg,
    justification msg = sigma ->
    equivocating_senders (add_message msg sigma) = equivocating_senders sigma.
Proof.
  rename H into elephant. rename H0 into squirrel.
  unfold equivocating_senders. intros. 
  (* Why doesn't the suff tactic work *)
  assert (H_suff : 
    (filter (fun msg : message => equivocating_in_state msg (add_message msg sigma))
      (get_messages (add_message msg sigma))) = 
    (filter (fun msg : message => equivocating_in_state msg sigma)
            (get_messages sigma))); try (rewrite H_suff; reflexivity).
  rewrite add_message_get_messages_iff. 
  simpl.
  assert
    (Hequiv : equivocating_in_state msg (add_message msg sigma) = false)
  ; try rewrite Hequiv.
  { apply existsb_forall. intros.
    rewrite equivocating_messages_comm.
    apply in_state_correct in H0.
    rewrite in_state_add_message_iff in H0.
    destruct H0 as [Heq | Hin].
    - subst.
      apply not_true_iff_false.
      intro H_absurd.
      rewrite equivocating_messages_correct in H_absurd.
      destruct H_absurd; tauto. 
    - apply in_state_correct in Hin.
      now apply non_equivocating_messages_extend with sigma. 
  }
  apply filter_eq_fn. intros. unfold equivocating_in_state. split; intros
  ; apply existsb_exists in H1; apply existsb_exists
  ; destruct H1 as [msg' [Hin Hmsg]]; exists msg'; split; try assumption.
  - rewrite add_message_get_messages_iff in Hin.
    destruct Hin as [Heq | Hin]; try assumption.
    exfalso. subst.
    apply equivocating_messages_correct in Hmsg.
    destruct Hmsg as [H_absurd _].
    apply H_absurd. auto. 
  - apply in_state_correct.
    rewrite in_state_add_message_iff.
    right. apply in_state_correct. assumption.
  - f_equal.
    rewrite add_message_get_messages_iff. 
    simpl.
     assert
    (Hequiv : equivocating_in_state msg (add_message msg sigma) = false)
  ; try rewrite Hequiv.
  { apply existsb_forall. intros.
    rewrite equivocating_messages_comm.
    apply in_state_correct in H0.
    rewrite in_state_add_message_iff in H0.
    destruct H0 as [Heq | Hin].
    - subst.
      apply not_true_iff_false.
      intro H_absurd.
      rewrite equivocating_messages_correct in H_absurd.
      destruct H_absurd; tauto. 
    - apply in_state_correct in Hin.
      now apply non_equivocating_messages_extend with sigma. 
  }
    apply filter_eq_fn. intros. unfold equivocating_in_state. split; intros
  ; apply existsb_exists in H1; apply existsb_exists
  ; destruct H1 as [msg' [Hin Hmsg]]; exists msg'; split; try assumption.
  rewrite add_message_get_messages_iff in Hin.
  destruct Hin as [Heq | Hin]; try assumption.
  exfalso. subst.
  assert (H_useful := non_equivocating_messages_extend a (justification msg') H0 msg' eq_refl). 
  rewrite Hmsg in H_useful.
  inversion H_useful.
  apply in_state_correct.
  rewrite in_state_add_message_iff.
  right. apply in_state_correct. assumption. 
Qed.

(* Now let's see if we can define the fault weight of a state parametrically *)
Definition sum_weights `{CBC_protocol_eq_specific} (l : list validators) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l. 

Definition fault_weight_state `{CBC_protocol_eq_specific} (sigma : state) : R :=
  sum_weights (equivocating_senders sigma). 

Lemma sum_weights_in `{CBC_protocol_eq_specific} : forall v vs,
  NoDup vs ->
  In v vs ->
  sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) v vs))%R.
Proof.
  rename H into elephant; rename H0 into squirrel.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    destruct (eq_dec_left (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) v). rewrite H. reflexivity.
  - inversion H; subst; clear H. simpl. assert (Hav := H3). apply (in_not_in _ _ _ _ H1) in Hav.
    destruct (compare_eq_dec v a); try (exfalso; apply Hav; assumption). simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (proj1_sig (weight v)) (proj1_sig (weight a))). rewrite Rplus_assoc. 
    apply Rplus_eq_compat_l. apply IHvs; assumption.
Qed.

Lemma sum_weights_incl `{CBC_protocol_eq_specific} : forall vs vs',
  NoDup vs ->
  NoDup vs' ->
  incl vs vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  rename H into elephant; rename H0 into squirrel.
  intros vs vs'. generalize dependent vs.
  induction vs'; intros.
  - apply incl_empty in H1; subst. apply Rle_refl.
  - inversion H0; subst; clear H0.
    destruct (in_dec (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) a vs).
    + apply sum_weights_in in i. rewrite i. simpl.
      apply Rplus_le_compat_l. apply IHvs'.
      * apply (set_remove_nodup compare_eq_dec a). assumption.
      * assumption.
      * intros x Hrem. apply set_remove_iff in Hrem; try assumption.
        destruct Hrem as [Hin Hxa].
        apply H1 in Hin. destruct Hin; try assumption.
        exfalso; subst. apply Hxa. reflexivity.
      * assumption.
    + simpl. apply Rle_trans with (sum_weights vs').
      * apply IHvs'; try assumption.
        intros x Hin. apply H1 in Hin as Hin'. destruct Hin'; try assumption.
        exfalso; subst. apply n. assumption.
      * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. destruct weight. simpl. auto. 
Qed.

Lemma fault_weight_state_incl `{CBC_protocol_eq_specific} : forall sigma sigma',
  reach sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply set_map_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

Definition incl_messages `{CBC_protocol_eq_specific} (s1 s2 : state) : Prop :=
  incl (get_messages s1) (get_messages s2).

(* Estimator approval condition *) 
Definition valid_estimate `{CBC_protocol_eq_specific} (c : consensus_values) (sigma : state) : Prop :=
  E sigma c.

(* The not overweight condition *)
Definition not_heavy `{CBC_protocol_eq_specific} (sigma : state) : Prop :=
  (fault_weight_state sigma <= proj1_sig t)%R.

(* States following Empty states are never overweight *) 
Lemma not_heavy_single `{CBC_protocol_eq_specific} :
  forall msg, not_heavy (add_message msg state0).
Proof.
  intros msg. 
  unfold not_heavy, fault_weight_state, equivocating_senders.
  simpl. unfold equivocating_in_state. simpl.
  unfold equivocating_messages. 
Abort. 

(* If a state is not overweight, none of its subsets are *) 
Lemma not_heavy_subset `{CBC_protocol_eq_specific} : forall s s',
  reach s s' ->
  not_heavy s' ->
  not_heavy s.
Proof.
  red.
  intros.
  apply Rle_trans with (fault_weight_state s'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

Lemma equivocating_in_state_extend `{CBC_protocol_eq_specific} :
  forall s msg,
    justification msg = s -> 
    ~ equivocating_in_state_prop msg s.
Proof. 
  intros s msg H_just H_absurd.
  destruct H_absurd as [msg' [H_in H_equiv]].
  apply in_state_correct in H_in. 
  assert (H_useful := non_equivocating_messages_extend msg' s H_in). 
  spec H_useful msg H_just.
  rewrite equivocating_messages_correct' in H_useful.
  rewrite equivocating_messages_prop_swap in H_equiv.
  contradiction.
Qed.

Definition pstate_light `{CBC_protocol_eq_specific} : Type := {s : state | prot_state s}. 
Definition pstate_light_proj1 `{CBC_protocol_eq_specific} (p : pstate_light) : state :=
  proj1_sig p. 
Coercion pstate_light_proj1 : pstate_light >-> state.

Definition pstate_light_rel `{CBC_protocol_eq_specific} : pstate_light -> pstate_light -> Prop :=
  fun p1 p2 => reach (pstate_light_proj1 p1) (pstate_light_proj1 p2).

Definition non_trivial_pstate_light `{CBC_protocol_eq_specific} (P : pstate_light -> Prop) :=
  (exists (s1 : pstate_light), forall (s : pstate_light), pstate_light_rel s1 s -> P s)
  /\
  (exists (s2 : pstate_light), forall (s : pstate_light), pstate_light_rel s2 s -> (P s -> False)).

Lemma Rtotal_le_gt : forall x y,
  (x <= y)%R \/ (x > y)%R.
Proof.
  intros.
  destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
  - left. unfold Rle. left. assumption.
  - left. unfold Rle. right. assumption.
  - right. assumption.
Qed.

Lemma next_equivocation_state_keeps_messages `{CBC_protocol_eq_specific} :
  forall (j : state) (v v' : validators) (msg : message),
    In msg (get_messages j) ->
    In msg (get_messages (next_equivocation_state j v v')). 
Proof.
  intros.
  assert (H_useful := next_equivocation_state_incl j v v').
  rewrite <- in_state_correct in *.
  now apply in_state_morphism with j.  
Qed.

Lemma next_equivocation_state_keeps_equivocators `{CBC_protocol_eq_specific} :
  forall (j : state) (v v' v0 : validators),
    In v0 (equivocating_senders j) ->
    In v0 (equivocating_senders (next_equivocation_state j v v')). 
Proof.
  intros.
  assert (H_incl := equivocating_senders_incl).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl. 
Qed.

Lemma next_equivocation_state_keeps_equivocating_messages `{CBC_protocol_eq_specific} :
  forall (j : state) (v v' : validators) (msg : message),
    equivocating_in_state_prop msg j ->
    equivocating_in_state_prop msg (next_equivocation_state j v v'). 
Proof.
  intros.
  assert (H_incl := equivocating_in_state_incl).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl. 
Qed.

(* It just occurred to me that we don't need to be overly specific about how we create this next equivocation state. *) 


Lemma equivocating_senders_sorted_extend `{CBC_protocol_eq_specific} :
  forall s msg,
    justification msg = s -> 
    set_eq (equivocating_senders s)
           (equivocating_senders (add_message msg s)). 
Proof.
  intros.
  assert (H_useful := equivocating_senders_extend s msg).
  rewrite <- H_useful.
  apply set_eq_refl. 
  assumption.
Qed.

Lemma set_eq_nodup_sum_weight_eq `{CBC_protocol_eq_specific} :
  forall (lv1 lv2 : list validators),
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2. 
Proof.
  intros lv1 lv2 H_nodup1 H_nodup2 [H_eq_l H_eq_r].
  assert (H_useful := sum_weights_incl lv1 lv2 H_nodup1 H_nodup2 H_eq_l).
  assert (H_useful' := sum_weights_incl lv2 lv1 H_nodup2 H_nodup1 H_eq_r).
  now apply Rle_antisym. 
Qed.

Lemma equivocating_senders_fault_weight_eq `{CBC_protocol_eq_specific} :
  forall s1 s2,
    set_eq (equivocating_senders s1) (equivocating_senders s2) ->
    fault_weight_state s1 = fault_weight_state s2. 
Proof.
  intros s1 s2 H_eq. 
  apply set_eq_nodup_sum_weight_eq; try apply set_map_nodup.
  assumption.
Qed.

Require Import Classical. 

Lemma add_already_equivocating_sender `{CBC_protocol_eq_specific} :
  forall (s : state),
    prot_state s ->
    forall (msg : message),
      In (sender msg) (equivocating_senders s) ->
        set_eq (equivocating_senders s)
               (equivocating_senders (add_message msg s)). 
Proof.
  intros s about_s msg H_in.
  split; intros v H_v_in.
  - unfold equivocating_senders.
    apply set_map_exists in H_v_in.
    destruct H_v_in as [msg' [H_v_in H_msg'_sender]].
    apply filter_In in H_v_in.
    rewrite <- H_msg'_sender.
    apply set_map_in.
    apply filter_in. 
    rewrite add_message_get_messages_iff. right. 
    tauto.
    rewrite equivocating_in_state_correct.
    destruct H_v_in.
    rewrite equivocating_in_state_correct in H2.
    destruct H2 as [msg'_partner H2].
    red. exists msg'_partner. split.
    destruct H2.
    rewrite in_state_correct.
    rewrite add_message_get_messages_iff.
    apply in_state_correct in H2. right; assumption.
    tauto.
  - destruct (classic (v = sender msg)).
    + subst. assumption. 
    + unfold equivocating_senders in H_v_in.
      apply set_map_exists in H_v_in.
      destruct H_v_in as [msg' [H_v_in H_msg'_sender]].
      apply filter_In in H_v_in.
      destruct H_v_in as [H_v_in H_equiv].
      rewrite equivocating_in_state_correct in H_equiv.
      destruct H_equiv as [msg'_partner [H_msg'_partner_in H_equiv]].
      rewrite <- H_msg'_sender.
      apply set_map_in.
      apply filter_in.
      rewrite add_message_get_messages_iff in H_v_in.
      destruct H_v_in.
      subst.
      contradiction.
      assumption.
      rewrite equivocating_in_state_correct.
      exists msg'_partner.
      split.
      apply in_state_correct in H_msg'_partner_in.
      rewrite add_message_get_messages_iff in H_msg'_partner_in.
      destruct H_msg'_partner_in.
      subst. destruct H_equiv.
      destruct H1. tauto.
      apply in_state_correct. 
      assumption. assumption.
Qed.

Lemma senders_fault_weight_eq `{CBC_protocol_eq_specific} :
  forall lv1 lv2,
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2. 
Proof.
  rename H into elephant.
  rename H0 into squirrel.
  induction lv1 as [|hd tl IHlv1]; intros lv2 H_lv1 H_lv2 H_eq.
  - destruct lv2.
    reflexivity.
    inversion H_eq.
    spec H0 v (in_eq v lv2).
    inversion H0.
  - simpl.
    (* hd must be in duplicate-free lv2 *)
    spec IHlv1 (set_remove (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) hd lv2).
    spec IHlv1.
    apply NoDup_cons_iff in H_lv1. tauto.
    spec IHlv1.
    now apply set_remove_nodup.
    spec IHlv1.
    replace tl with (set_remove (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) hd (hd :: tl)). 
    apply set_eq_remove; try assumption.
    now rewrite set_remove_first.
    (* Now. *) 
    rewrite IHlv1.
    symmetry.
    apply sum_weights_in. assumption.
    destruct H_eq as [H_eq _].
    spec H_eq hd (in_eq hd tl). assumption.
Qed.

Lemma set_add_ignore {X} `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    In x l ->
    set_add compare_eq_dec x l = l. 
Proof.
  induction l as [|hd tl IHl]; intros x H_in. 
  - inversion H_in.
  - inversion H_in.
    + subst. simpl.
      destruct (compare_eq_dec x x). 
      reflexivity.
      contradiction.
    + spec IHl x H0. simpl.
      destruct (compare_eq_dec x hd).
      reflexivity.
      rewrite IHl. reflexivity.
Qed.

Lemma add_equivocating_sender `{CBC_protocol_eq_specific} :
  forall (s : state),
    prot_state s ->
    forall (msg : message),
      (exists msg',
          in_state msg' s /\
          equivocating_messages_prop msg msg') ->
      set_eq (equivocating_senders (add_message msg s))
             (set_add (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) (sender msg) (equivocating_senders s)).
Proof.
  (* Because we're using set_add, we don't need to care about whether (sender msg) is already in (equivocating_senders s) *) 
  intros s about_s msg [msg' [H_in H_equiv]]. 
  destruct (classic (In msg (get_messages s))) as [H_msg_in | H_msg_out].
  - (* In the case that msg is already in s, *)
    (* Adding it does nothing to the state *)
    assert (H_ignore := @set_add_ignore message about_message (get_messages s) msg H_msg_in).
    simpl in *.
    admit. 
(*     replace (add_message msg s) with (msg :: get_messages s). rewrite <- H_ignore.
    (* Adding the sender should do nothing to (equivocating_senders s) *) 
    split.
    + intros v0 H_mem.
      (* The following is winding and painful *) 
      unfold equivocating_senders in H_mem.
      rewrite set_map_exists in H_mem.
      destruct H_mem as [msg0 [H0_in H0_sender]].
      rewrite filter_In in H0_in.
      assert (H_senders := equivocating_senders_correct s). 
      red in H_senders.
      destruct H0_in as [H0_in H0_equiv].
      apply set_add_iff. 
      destruct (classic (msg = msg0)).
      * subst.
        left; reflexivity. 
      * inversion H0_in. contradiction.
        clear H0_in.
        rewrite H_ignore in *.
        rewrite equivocating_in_state_correct in H0_equiv. 
        destruct H0_equiv as [msg0_partner [H0_equivl H0_equivr]].
        inversion H0_equivl.
        subst. left.
        destruct H0_equivr. tauto.
        right.
        subst.
        spec H_senders (sender msg0).
        apply H_senders.
        exists msg0_partner. 
        repeat split. assumption. red in H0_equivr; symmetry; tauto.
        exists msg0. split; try assumption.
        apply equivocating_messages_prop_swap.
        assumption. 
    + intros v0 H_mem.
      (* The following will also be winding and painful *)
      destruct (classic (v0 = sender msg)).
      * subst.
        clear H_mem.
        apply set_map_in.
        apply filter_in.
        apply in_eq. 
        rewrite equivocating_in_state_correct.
        exists msg'. split; try assumption.
        right; rewrite H_ignore; assumption. 
      * rewrite set_add_iff in H_mem.
        destruct H_mem.
        contradiction. rewrite H_ignore in *.
        assert (H_goal := equivocating_senders_incl s (msg :: s)). spec H_goal. right; now apply incl_refl.
        now apply H_goal. 
  - (* In the case that msg is not already in s, *)
    (* For all we know (sender msg) could already be in (equivocating_senders s) *)  
    destruct (classic (In (sender msg) (equivocating_senders s))).
    + (* If (sender msg) is already in there, then adding it again does nothing *)
      assert (H_ignore : set_eq (set_add compare_eq_dec (sender msg) (equivocating_senders s)) (equivocating_senders s)).
      {  split; intros v H_v_in. 
         apply set_add_iff in H_v_in.
         destruct H_v_in.
         subst; assumption.
         assumption.
         apply set_add_iff. right; assumption. }
      apply set_eq_comm in H_ignore. 
      eapply set_eq_tran. 
      2 : exact H_ignore.
      apply set_eq_comm.
      now apply add_already_equivocating_sender.
    + (* If (sender msg) is not already in there *)
      split; intros.  
      * intros v0 H_in0.
        destruct (classic (v0 = sender msg)). 
        ** subst.
           apply set_add_iff.
           tauto.
        ** apply set_add_iff.
           right.
           destruct msg as [[c v] j].
           apply equivocating_sender_add_in_sorted_iff in H_in0. 
           destruct H_in0.
           destruct H1; contradiction.
           assumption.
      * intros v0 H_in0.
        destruct (classic (v0 = sender msg)). 
        ** subst.
           apply set_add_iff in H_in0.
           destruct H_in0.
           apply set_map_in.
           apply filter_in.
           apply in_eq. 
           rewrite equivocating_in_state_correct.
           red. exists msg'.
           split. 
           right; assumption.
           assumption. contradiction. 
        ** apply set_add_iff in H_in0.
           destruct H_in0.
           contradiction.
           apply set_map_exists in H1.
           destruct H1 as [msg0 [H_in0 H_sender0]].
           apply set_map_exists. exists msg0.
           split. 2 : assumption.
           apply filter_in.
           apply filter_In in H_in0.
           destruct H_in0.
           right; assumption.
           apply filter_In in H_in0.
           destruct H_in0.
           rewrite equivocating_in_state_correct.
           red. rewrite equivocating_in_state_correct in H2.
           red in H2.
           destruct H2 as [msg0_partner [H_in0 H_equiv0]].
           exists msg0_partner.
           split.
           right; assumption.
           assumption. *) 
Abort.

(* We need some guarantees that the next equivocation state function actually works as intended, abstracting away all the details of add_weight one/two/three. *) 
Definition add_weight_under `{CBC_protocol_eq_specific} (s : state) (v : validators) :=
  (fault_weight_state s + proj1_sig (weight v) <= proj1_sig t)%R.
Class CBC_protocol_eq_more_specific `{CBC_protocol_eq_specific} :=
  {
    add_comm : forall s msg1 msg2, state_eq (add_message msg1 (add_message msg2 s)) (add_message msg2 (add_message msg1 s));
    (* More details about this next state that depends on its implementation, but that we include here after we have defined all the relevant operations *) 
                           
    prot_state_not_heavy : forall sigma,
      prot_state sigma ->
      not_heavy sigma;
    (* next_equivocation_state_adds_equivocator :
      forall j v v',
        prot_state j -> 
        v <> v' ->
        In v (equivocating_senders (next_equivocation_state j v v')); *)
    next_equivocation_state_adds_equivocators : forall (j : state) (v v' v0 : validators),
        In v0 (equivocating_senders (next_equivocation_state j v v')) <-> 
        In v0 (equivocating_senders j) \/ v0 = v; 

    (* This relies on add_weight_one/two/three *) 
    equivocation_adds_fault_weight :
      
      forall (j : state),
        prot_state j ->
        forall (v v' : validators),
          ~ In v (equivocating_senders j) -> 
          v <> v' ->  
          fault_weight_state (next_equivocation_state j v v') = 
          (fault_weight_state j + proj1_sig (weight v))%R;

    (* This relies on the specific construction of the equivocating messages *) 
    next_equivocation_protocol_state :
      
      forall j,
        prot_state j ->
        forall v v',
          ~ In v (equivocating_senders j) -> 
          v <> v' -> 
          (add_weight_under j v ->
           prot_state (next_equivocation_state j v v'));

    (* This relies on the above and is just cleaner *) 
    next_equivocation_adds_weight :
      
      forall (s : state),
        prot_state s ->
        forall (v : validators),
          (* If the weight is not over *) 
          add_weight_under s v ->
          (* And the sender is not already equivocating *) 
          ~ In v (equivocating_senders s) -> 
          forall (v' : validators),
            v <> v' ->
            (* Then we get a protocol state *) 
            prot_state (next_equivocation_state s v v') /\
            (* With increased weight *) 
            fault_weight_state (next_equivocation_state s v v') =
            (fault_weight_state s + proj1_sig (weight v))%R;

                                                     
  }.

(* Now I think we are ready to define this recursive equivocation function. *)

Fixpoint next_equivocation_rec' `{CBC_protocol_eq_more_specific} (s : state) (vs : list validators) (v0 : validators) : state :=
  match vs with
  | [] => s
  | hd :: tl => next_equivocation_state (next_equivocation_rec' s tl v0) hd v0
  end.

Lemma next_equivocations_keeps_messages `{CBC_protocol_eq_more_specific} :
  forall (s : state) (vs : list validators) (v0 : validators),
  forall (msg : message),
    in_state msg s ->
    in_state msg (next_equivocation_rec' s vs v0). 
Proof.
  intros s vs v0 msg H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    apply in_state_correct.
    apply next_equivocation_state_keeps_messages.
    now apply in_state_correct in IHvs.
Qed.

Lemma next_equivocations_equivocating_senders_right `{CBC_protocol_eq_more_specific} :
  forall (s : state) (vs : list validators) (v0 v : validators),
    (In v vs -> v <> v0) ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)) ->
    In v vs \/ In v (equivocating_senders s). 
Proof.
  rename H into elephant;
    rename H0 into squirrel.
  intros s vs; induction vs as [|hd tl IHvs]; intros v0 v H_neq. 
  - intros. 
    simpl in H. tauto. 
  - intros.
    spec IHvs v0 v.  
    spec IHvs. 
    { intros. 
      spec H_neq. right; assumption.
      assumption. }
    simpl in H.
    apply next_equivocation_state_adds_equivocators in H. 
    destruct H as [? | ?].
    spec IHvs H. destruct IHvs.
    left. right. assumption.
    tauto. subst. left. left. reflexivity.
Qed.

Lemma next_equivocations_equivocating_senders_left_weak `{CBC_protocol_eq_more_specific} :
  forall (s : state) (vs : list validators) (v0 v : validators),
    prot_state (next_equivocation_rec' s vs v0) -> 
    (In v vs -> v <> v0) ->
    In v vs ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)). 
Proof.
  rename H into elephant; rename H0 into squirrel.
  intros s vs; induction vs as [|hd tl IHvs]; intros v0 v H_prot H_neq H_in. 
  - inversion H_in. 
  - assert (H_prot_sub : prot_state (next_equivocation_rec' s tl v0)).
    { apply protocol_state_incl with (next_equivocation_rec' s (hd :: tl) v0).
      assumption.
      apply prot_state_nodup in H_prot.
      simpl in H_prot.
      apply nodup_state_reach with (next_equivocation_state (next_equivocation_rec' s tl v0) hd v0). 
      assumption.
      apply next_equivocation_state_incl.
      simpl. apply next_equivocation_state_incl. }
    spec IHvs v0 v.
    spec IHvs H_prot_sub. 
    spec IHvs. intros. apply H_neq. auto.
    (* Case analysis on where v is *)
    destruct H_in as [H_eq | H_in].
    * (* When we are looking at the hd element, *)
      subst.
      simpl.
      apply next_equivocation_state_adds_equivocators. 
      tauto. 
    * spec IHvs H_in.
      simpl. 
      assert (H_useful := equivocating_senders_incl). 
      spec H_useful (next_equivocation_rec' s tl v0) (next_equivocation_state (next_equivocation_rec' s tl v0) hd v0).
      spec H_useful.
      apply next_equivocation_state_incl.
      apply H_useful. assumption.
Qed.

Lemma next_equivocations_add_weights `{CBC_protocol_eq_more_specific} : 
  forall (s : state),
    prot_state s ->
    forall (vs : list validators) (v0 : validators),
      NoDup vs -> 
      (* The sum weight is not over *)
      (fault_weight_state s + sum_weights vs <= proj1_sig t)%R ->
      (* None of the senders are already equivocating *) 
      (forall (v : validators),
          In v vs -> ~ In v (equivocating_senders s) /\ v <> v0) ->
      (* Then we end up with a protocol state *)
      prot_state (next_equivocation_rec' s vs v0) /\
      (* And s recursively adds the sums of all the weights in vs *) 
      fault_weight_state (next_equivocation_rec' s vs v0) =
      (fault_weight_state s + sum_weights vs)%R.
Proof.
  rename H into elephant; rename H0 into squirrel.
  intros s about_s vs v0 H_nodup H_underweight H_disjoint. 
  induction vs as [|hd tl IHvs].
  - (* Base case : no validators to add *)
    split. assumption. 
    rewrite Rplus_0_r. reflexivity.
  - (* Induction step *)
    (* Discharging first premise *)  
    spec IHvs. 
    rewrite NoDup_cons_iff in H_nodup; tauto.
    (* Discharging second premise *)
    spec IHvs.
    simpl in H_underweight.
    apply (Rplus_le_reg_pos_r (fault_weight_state s + sum_weights tl) (proj1_sig (weight hd)) (proj1_sig t)).
    destruct (weight hd). simpl.
    apply Rge_le.
    apply Rgt_ge. assumption. 
    rewrite Rplus_assoc.
    rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
    rewrite <- Rplus_assoc.
    rewrite <- Rplus_assoc in H_underweight.
    assumption.
    (* Discharging third premise *)
    spec IHvs.
    intros. spec H_disjoint v. spec H_disjoint. 
    right; assumption.
    assumption. 
    (* Now. *)
    destruct IHvs as [H_prot H_weight].
    spec H_disjoint hd (in_eq hd tl).
    assert (H_notin_tl : ~ In hd tl).
    { rewrite NoDup_cons_iff in H_nodup.
      tauto. }
    destruct H_disjoint as [H_disjoint H_neq].
    assert (H_rewrite := next_equivocations_equivocating_senders_right s tl v0 hd).
    spec H_rewrite.
    intros. assumption.
    split.
    + simpl.  
      apply next_equivocation_protocol_state; try assumption.
      intros H_absurd.
      spec H_rewrite H_absurd. 
      tauto.
      (* Need a helper lemma about weight adding here *) 
      unfold add_weight_under.
      rewrite H_weight. simpl in H_underweight.
      rewrite <- Rplus_assoc in H_underweight.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
      rewrite <- Rplus_assoc.
      assumption.
    + simpl.
      rewrite (Rplus_comm (proj1_sig (weight hd)) (sum_weights tl)).
      rewrite <- Rplus_assoc.
      rewrite <- H_weight.
      apply equivocation_adds_fault_weight; try assumption.
      intro H_absurd. spec H_rewrite H_absurd. 
      tauto. 
Qed.

Lemma next_equivocations_keeps_equivocating_senders `{CBC_protocol_eq_more_specific} :
  forall (s : state) (vs : list validators) (v0 : validators),
  forall (v : validators),
    In v (equivocating_senders s) ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)). 
Proof.
  intros s vs v0 v H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    assert (H_useful := next_equivocation_state_keeps_equivocators (next_equivocation_rec' s tl v0) hd v0 v IHvs).
    assumption.
Qed.

Definition get_estimate `{CBC_protocol_eq_more_specific} (s : state) :=
  proj1_sig (choice consensus_values (E s) (estimator_total s)).

Definition get_estimate_correct `{CBC_protocol_eq_more_specific} (s : state) :=
  proj2_sig (choice consensus_values (E s) (estimator_total s)). 

Definition potentially_pivotal_state `{CBC_protocol_eq_more_specific} (v : validators) (s : state) :=
  (* We say that v is a pivotal validator for some state s iff : *)
  (* v is not already equivocating in s *) 
  ~ In v (equivocating_senders s) /\
  (* There is a remaining list of validators *) 
  exists (vs : list validators),
    (* That is duplicate-free *)
    NoDup vs /\
    (* Doesn't contain v *)
    ~ In v vs /\ 
    (* That are all not already equivocating in s *) 
    (forall (v : validators), In v vs -> ~ In v (equivocating_senders s)) /\
    (* That tip over s's fault weight but only with the help of v *) 
    (sum_weights ((equivocating_senders s) ++ vs) <= proj1_sig t)%R /\
    (sum_weights ((equivocating_senders s) ++ vs) >
     proj1_sig t - proj1_sig (weight v))%R. 

Lemma pivotal_validator_extension `{CBC_protocol_eq_more_specific} : forall (vsfix vss : list validators),
  NoDup vsfix ->
  (* and whose added weight does not pass the threshold *)
  (sum_weights vsfix <= proj1_sig t)%R ->
  NoDup (vss ++ vsfix) ->
  (sum_weights (vss ++ vsfix) > proj1_sig t)%R ->
  exists (vs : list validators),
    NoDup vs /\
    incl vs vss /\
    (sum_weights (vs ++ vsfix) > proj1_sig t)%R /\
    exists (v : validators),
      In v vs /\
      (sum_weights ((set_remove  (@compare_eq_dec validators compare (@compare_strictorder validators about_validators)) v vs) ++ vsfix) <= proj1_sig t)%R.
Proof.
  rename H into elephant;
    rename H0 into squirrel;
    rename H1 into bunny.
  destruct t as [t about_t]; simpl in *.
  intro.
  induction vss; intros.
  - simpl in H2. exfalso. apply (Rge_gt_trans t) in H2; try (apply Rle_ge; assumption).
    apply Rgt_not_eq in H2. apply H2. reflexivity.
  - simpl in H2. destruct (Rtotal_le_gt (sum_weights (vss ++ vsfix)) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply append_nodup_left in H1. assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite eq_dec_if_true; try reflexivity. assumption.
    + simpl in H1. apply NoDup_cons_iff in H1. destruct H1 as [Hnin Hvss]. apply IHvss in H3; try assumption.
      destruct H3 as [vs [Hvs [Hincl Hex]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.

Lemma sum_weights_app `{CBC_protocol_eq_more_specific} : forall vs vs',
  sum_weights (vs ++ vs') = (sum_weights vs + sum_weights vs')%R.
Proof.
  induction vs; intros; simpl.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite IHvs. rewrite Rplus_assoc. reflexivity.
Qed.

(* This is a critical lemma *) 
Lemma all_pivotal_validator `{CBC_protocol_eq_more_specific} :
  forall (s : state),
    prot_state s -> 
  exists (v : validators),
    potentially_pivotal_state v s. 
Proof.
  rename H into elephant;
    rename H0 into squirrel;
    rename H1 into bunny.
  intros s about_s.
  destruct suff_val as [vs [Hvs Hweight]].
  remember (equivocating_senders s) as eqv_s.
  remember (set_diff (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) vs eqv_s) as vss.
  assert (sum_weights (vss ++ eqv_s) > proj1_sig t)%R.
  { apply Rge_gt_trans with (sum_weights vs); try assumption.
    apply Rle_ge. apply sum_weights_incl; try assumption.
    - rewrite Heqvss. apply diff_app_nodup; try assumption.
      subst. unfold equivocating_senders. apply set_map_nodup.
    - rewrite Heqvss. intros a Hin. apply in_app_iff.
      rewrite set_diff_iff. apply or_and_distr_left.
      split; try (left; assumption).
      destruct (in_dec (@compare_eq_dec validators (@compare validators about_validators) (@compare_strictorder validators about_validators)) a eqv_s); (left; assumption) || (right; assumption).
  }
  apply pivotal_validator_extension in H. 
  - destruct H as [vs' [Hnodup_vs' [Hincl_vs' [Hgt [v [Hin_v Hlt]]]]]].
    exists v. split.
    + subst. apply Hincl_vs' in Hin_v. apply set_diff_elim2 in Hin_v. assumption.
    + exists (set_remove (@compare_eq_dec validators compare (@compare_strictorder validators about_validators)) v vs').
      assert (NoDup (set_remove (@compare_eq_dec validators compare (@compare_strictorder validators about_validators)) v vs')) as Hnodup_remove
      ; try apply set_remove_nodup; try assumption.
      repeat split.
      * assumption.
      * try apply set_remove_elim; try assumption.
      * intros. apply set_remove_1 in H. apply Hincl_vs' in H. subst.
        apply set_diff_elim2 in H. assumption.
      * subst. rewrite sum_weights_app in *. rewrite Rplus_comm in Hlt.
        assumption.
      * apply Rlt_gt. apply Rplus_lt_reg_r with (proj1_sig (weight v)).
        unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_l.
        rewrite Rplus_0_r. apply Rgt_lt.
        apply Rge_gt_trans with (sum_weights (vs' ++ eqv_s)); try assumption.
        unfold Rge. right. rewrite Rplus_comm.
        rewrite sum_weights_app. rewrite (Rplus_comm (sum_weights (equivocating_senders s))) .
        rewrite <- Rplus_assoc. rewrite sum_weights_app. subst.
        apply Rplus_eq_compat_r.
        symmetry. apply sum_weights_in; try assumption.
  - subst. apply set_map_nodup.
  - subst. apply prot_state_not_heavy. assumption.
  - subst. apply diff_app_nodup; try assumption.
    apply set_map_nodup.
Qed.

(* Defining reachablity in terms of message sending *)
Definition in_future `{CBC_protocol_eq_more_specific} (s1 s2 : state) :=
  reach s1 s2. 

Definition next_future `{CBC_protocol_eq_more_specific} (s1 s2 : state) :=
   exists (msg : message), state_eq (add_message msg s1) s2. 

Definition in_past `{CBC_protocol_eq_more_specific} (s1 s2 : state) :=
  reach s2 s1. 

Definition no_common_future `{CBC_protocol_eq_more_specific} (s1 s2 : pstate_light) :=
  forall (s : pstate_light), in_future s1 s /\ in_future s2 s -> False. 

Definition yes_common_future `{CBC_protocol_eq_more_specific} (s1 s2 : pstate_light) :=
  exists (s : pstate_light), in_future s1 s /\ in_future s2 s. 

Definition strong_nontriviality `{CBC_protocol_eq_more_specific} :=
  (* For every state, there exists a state *) 
  forall (s1 : pstate_light),
  exists (s2 : pstate_light),
    (* That is reachable in one step *) 
    next_future s1 s2 /\
    (* And there exists a third state *)
    exists (s3 : pstate_light),
      (* Such that s1 and s3 share a common future *)
      yes_common_future s1 s3
      /\
      (* But s2 and s3 don't. *) 
      no_common_future s2 s3.

Lemma distinct_sender_total `{CBC_protocol_eq_more_specific} : forall v1 : validators, exists v2 : validators, v1 <> v2.
Proof.
  intros.
  destruct two_senders  as [v1' [v2' Hneq]].
  destruct ((@compare_eq_dec validators compare (@compare_strictorder validators about_validators)) v1 v1') eqn:Heq.
  - subst. exists v2'. assumption.
  - exists v1'. assumption.
Qed.

Definition get_distinct_sender `{CBC_protocol_eq_more_specific} (v : validators) :=
  proj1_sig (choice validators (fun v' => v <> v') (distinct_sender_total v)).

Definition get_distinct_sender_correct `{CBC_protocol_eq_more_specific} (v : validators) :=
  proj2_sig (choice validators (fun v' => v <> v') (distinct_sender_total v)).

Lemma get_distinct_sender_correct' `{CBC_protocol_eq_more_specific} :
  forall v, get_distinct_sender v <> v. 
Proof.
  intros. unfold get_distinct_sender.
  assert (H_useful := get_distinct_sender_correct v).
  simpl in *.
  intro H_absurd.
  apply H_useful; symmetry; assumption.
Qed.

Theorem strong_nontriviality_full `{CBC_protocol_eq_more_specific} : strong_nontriviality.  
Proof.
  rename H into elephant;
    rename H0 into squirrel;
    rename H1 into bunny. 
  intros [s1 about_s1]. 
  destruct (all_pivotal_validator s1 about_s1) as [v [H_v [vs [H_nodup [H_v_notin [H_disjoint [H_under H_over]]]]]]].
  (* Now we need to construct s2 in a smarter way *)
  (* v could potentially equivocate, but we don't want to go so far. *) 
  assert (H_overkill := next_equivocation_state_horn s1 v (get_distinct_sender v)).
  destruct H_overkill as [msg1 [msg2 [msg3 [H_eq [H_equiv [H_sender1 [H_sender2 [H_justi H_prot]]]]]]]]. 
  remember (add_message msg3 s1) as s2.
  assert (about_s2 : prot_state s2) by (subst; tauto).
  (* Book-keeping *)
  assert (H_s1_s2_senders : set_eq (equivocating_senders s1) (equivocating_senders (s2))) by admit. 
  assert (H_s1_s2_weight : fault_weight_state s1 = fault_weight_state (s2)) by admit. 
  exists (exist prot_state s2 about_s2).
  split.
  (* Proving that s2 is a next state is trivial *)
  exists msg3. subst. 
  simpl. apply Equivalence_Reflexive.
  (* Now we need to construct s3. *)
  (* First we add the equivocating partner message *) 
  remember (add_message msg2 (add_message msg1 s1)) as s1'.
  assert (about_s1' : prot_state s1') by (subst; tauto).
  (* Book-keeping step *) 
  assert (H_eq_senders : set_eq (equivocating_senders s1') (equivocating_senders s1)) by admit.
  assert (H_s_inter_weight : fault_weight_state s1' = fault_weight_state s1).
  { apply equivocating_senders_fault_weight_eq; assumption. }
  (* Now we are ready to construct s3 from s1' *)
  (* And if we have set up everything correctly, the premises at this point in the proof are sufficient. *)
  remember (next_equivocation_rec' s1' vs v) as s3.
  assert (about_s3 : prot_state s3).
  { rewrite Heqs3. apply next_equivocations_add_weights.
    { subst.
      tauto. }
    assumption. 
    rewrite H_s_inter_weight. rewrite sum_weights_app in H_under.
    assumption. 
    intros. spec H_disjoint v0 H.
    destruct H_eq_senders as [H_left H_right].
    spec H_right v0.
    split. intro H_absurd. spec H_left v0 H_absurd.
    contradiction. intro H_absurd. subst. contradiction. } 
  exists (exist prot_state s3 about_s3).
  repeat split.
  exists (exist prot_state s3 about_s3). split.
  subst. simpl.
  red.
  admit. 

  apply reach_refl.
  red. intros [s about_s] H.   
  destruct H as [H_in2 H_in3].
  assert (H_in2_copy := H_in2);
    assert (H_in3_copy := H_in3).  
  (* Now we show that two equivocating messages are in s *)
  (* First message *) 
  simpl in *.
  assert (H_in2' := in_state_morphism s2 s H_in2 msg3).
  spec H_in2'. 
  subst.
  apply add_message_in_state. 
  (* Second message *) 
  assert (H_in3' := in_state_morphism s3 s H_in3 msg2).
  spec H_in3'.
  subst.
  admit. 
  (* Now we say that v will be an equivocating sender inside s *)
  assert (H_v_in : In v (equivocating_senders s)).
  { apply equivocating_senders_correct.
    exists msg2. 
    repeat split; try assumption.
    exists msg3.
    split; try tauto.
    apply equivocating_messages_correct.
    assumption. }
  clear H_in2 H_in3 H_equiv. 
  (* Now we say that v's weight will be inside s's fault weight *)
  (* This part is a little tricky *)
  assert (H_equivocators_s : incl ((v :: (equivocating_senders s2) ++ vs)) (equivocating_senders s)). 
  { intros v0 H_in0.
    destruct H_in0 as [H_hd | H_tl].
    + subst. assumption.
    + apply in_app_iff in H_tl.
      destruct H_tl as [H_left | H_right].
      * eapply equivocating_senders_incl.
        apply H_in2_copy.
        assumption.
        * assert (H_in_v0 : In v0 (equivocating_senders (next_equivocation_rec' s1' vs v))).
          { apply next_equivocations_equivocating_senders_left_weak. 
            subst. assumption. intros.
            2 : assumption.
            intro H_absurd; subst; contradiction. } 
          rewrite <- Heqs3 in H_in_v0.
          eapply equivocating_senders_incl.
          exact H_in3_copy. 
          assumption.
    }
    assert (H_s_overweight : (proj1_sig (weight v) + fault_weight_state (s2) + sum_weights vs <= fault_weight_state s)%R). 
    { replace ((proj1_sig (weight v) + fault_weight_state (s2) + sum_weights vs))%R with (sum_weights ([v] ++ (equivocating_senders (s2)) ++ vs)).
      apply sum_weights_incl.
      { (* Proving mutual NoDup *) 
        apply nodup_append.
        apply NoDup_cons. intros; inversion 1.
        constructor.
        apply nodup_append.
        apply set_map_nodup. assumption.
        { intros. intro Habsurd. spec H_disjoint a Habsurd.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a H. contradiction.
        }
        { intros. intro Habsurd. spec H_disjoint a H.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a Habsurd. contradiction. }
        { intros. inversion H. intro Habsurd.
          apply in_app_iff in Habsurd. destruct Habsurd.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H1.
          subst; contradiction. subst; contradiction. inversion H0. } 
        { intros. intro Habsurd.
          inversion Habsurd.
          apply in_app_iff in H. destruct H.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H.
          subst; contradiction. subst; contradiction. inversion H0. } 
      }
      apply set_map_nodup. assumption.
      do 2 rewrite sum_weights_app.
      unfold fault_weight_state.
      simpl. ring. }
    apply prot_state_not_heavy in about_s.
    red in about_s.
    assert (H_finale := Rle_trans _ _ _ H_s_overweight about_s). auto.
    rewrite sum_weights_app in H_over.
    unfold fault_weight_state in H_s1_s2_weight at 1. 
    rewrite H_s1_s2_weight in H_over.
    apply (Rplus_gt_compat_l (proj1_sig (weight v))) in H_over. 
    replace (proj1_sig (weight v) + (proj1_sig t - proj1_sig (weight v)))%R with (proj1_sig t)%R in H_over by ring.
    rewrite <- Rplus_assoc in H_over. 
    apply Rgt_not_le in H_over.
    contradiction.
Admitted. 



Definition next_future `{CBC_protocol_eq_specific} (s1 s2 : state) :=
   exists (msg : message), state_eq (add_message msg s1) s2. 

Definition pstate `{CBC_protocol_eq_specific} : Type :=
  { s : state | prot_state s}.

Definition pstate_proj1 `{CBC_protocol_eq_specific} (ps : pstate) :=
  proj1_sig ps. 

Coercion pstate_proj1 : pstate >-> state. 

Definition no_common_future `{CBC_protocol_eq_specific} (s1 s2 : pstate) :=
  forall (s : pstate), reach s1 s /\ reach s2 s -> False. 

Definition yes_common_future `{CBC_protocol_eq_specific} (s1 s2 : pstate) :=
  exists (s : pstate), reach s1 s /\ reach s2 s. 

Definition strong_nontriviality `{CBC_protocol_eq_specific} :=
  (* For every state, there exists a state *) 
  forall (s1 : pstate),
  exists (s2 : pstate),
    (* That is reachable in one step *) 
    next_future s1 s2 /\
    (* And there exists a third state *)
    exists (s3 : pstate),
      (* Such that s1 and s3 share a common future *)
      yes_common_future s1 s3
      /\
      (* But s2 and s3 don't. *) 
      no_common_future s2 s3.

Theorem strong_nontriviality_full `{CBC_protocol_eq_specific} : strong_nontriviality.  
Proof.
  intros [s1 about_s1]. 
  destruct (all_pivotal_validator s1 about_s1) as [v [H_v [vs [H_nodup [H_v_notin [H_disjoint [H_under H_over]]]]]]].
  remember (exist protocol_state ((get_estimate s1,v,hash_state s1) :: s1) (copy_protocol_state s1 about_s1  v)) as s2. 
  (* Book-keeping *)
  assert (H_s1_s2_senders : set_eq (equivocating_senders s1) (equivocating_senders (proj1_sig s2))) by (subst; apply equivocating_senders_sorted_extend). 
  assert (H_s1_s2_weight : fault_weight_state s1 = fault_weight_state (proj1_sig s2)) by (subst; apply add_weight_one). 
  exists s2.
  (* Proving next-step relation is trivial. *) 
  split.
  exists (get_estimate s1,v,hash_state s1); subst; simpl in *.
  split; intros x H_in.
  rewrite set_add_iff in H_in. destruct H_in. subst. apply in_eq.
  right; tauto.
  inversion H_in; subst; rewrite set_add_iff; tauto.
  (* s3 is the state with equivocations from all the senders in vs recursively added to s1, in addition to (c,v,s1)'s equivocating partner message. *)
  (* First we add the equivocating partner message *)
  remember ((get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v, hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1)) :: ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1)) as s1'.
  (* Book-keeping step *) 
  assert (H_eq_senders : set_eq (equivocating_senders s1') (equivocating_senders s1)).
  { subst. 
    assert (H_useful := equivocating_senders_sorted_extend ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1) v).
    eapply set_eq_tran.
    apply set_eq_comm. exact H_useful.
    apply set_eq_comm. apply equivocating_senders_sorted_extend. }
  assert (H_s_inter_weight : fault_weight_state s1' = fault_weight_state s1).
  { apply equivocating_senders_fault_weight_eq; assumption. }
  (* Now we are ready to construct s3 from s1' *)
  (* And if we have set up everything correctly, the premises at this point in the proof are sufficient. *)
  remember (next_equivocation_rec' s1' vs v) as s3.
  assert (about_s3 : protocol_state s3).
  { rewrite Heqs3. apply next_equivocations_add_weights.
    { subst.
      apply copy_protocol_state; try apply get_estimate_correct; try assumption. 
      apply copy_protocol_state; try apply get_estimate_correct; try assumption. } 
    assumption.
    rewrite H_s_inter_weight. rewrite sum_weights_app in H_under.
    assumption. 
    intros. spec H_disjoint v0 H.
    destruct H_eq_senders as [H_left H_right].
    spec H_right v0.
    split. intro H_absurd. spec H_left v0 H_absurd.
    contradiction. intro H_absurd. subst. contradiction. } 
  exists (exist protocol_state s3 about_s3).
  repeat split.
  - (* Proving that s1 and s3 share a common future *)
    red. exists (exist protocol_state s3 about_s3).
    split. simpl. red.
    red. subst.
    intros m0 H_in.
    (* Need to prove that next_equivocation_rec' doesn't drop messages *) 
    apply next_equivocations_keeps_messages.
    do 2 right. 
    assumption. 
    apply incl_refl.
  - (* Proving that s2 and s3 don't share a common future *)
    (* Arbitrary state in both s2 and s3 leads to a contradiction *) 
    red. intros [s about_s] H.   
    destruct H as [H_in2 H_in3].
    assert (H_in2_copy := H_in2);
      assert (H_in3_copy := H_in3).  
    (* Now we show that two equivocating messages are in s *)
    (* First message *) 
    spec H_in2 (get_estimate s1,v,hash_state s1).
    spec H_in2. 
    subst. 
    apply in_eq. 
    (* Second message *) 
    spec H_in3 (get_estimate
                ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v,
             
               hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) ::  s1)).
    spec H_in3.
    { (* Proving that this message is in s3 *)
      assert (H_obv : In (get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) ::  s1), v, hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) ::  s1)) s1').
      { subst. 
        left. reflexivity. }
      apply (next_equivocations_keeps_messages s1' vs v) in H_obv.
      subst; assumption. }
    (* Now we prove that these two messages are equivocating *) 
    simpl in *.
    assert (H_equiv : equivocating_messages_prop (get_estimate s1,v,hash_state s1)
                                                 (get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v, hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1))).
    apply about_equivocating_messages. 
    assumption. apply get_distinct_sender_correct. 
    (* Now we say that v will be an equivocating sender inside s *)
    assert (H_v_in : In v (equivocating_senders s)).
    { apply equivocating_senders_correct.
      exists (get_estimate s1, v, hash_state s1). 
      repeat split; try assumption.
      exists (get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v, hash_state ( (get_estimate s1, get_distinct_sender v, hash_state s1) :: s1)).
      split. assumption. assumption. }
    clear H_in2 H_in3 H_equiv. 
    (* Now we say that v's weight will be inside s's fault weight *)
    (* This part is a little tricky *)
    assert (H_equivocators_s : incl (v :: (equivocating_senders (proj1_sig s2) ++ vs)) (equivocating_senders s)). 
    { intros v0 H_in0.
      destruct H_in0 as [H_hd | H_tl].
      + subst. assumption.
      + apply in_app_iff in H_tl.
        destruct H_tl as [H_left | H_right].
        * eapply equivocating_senders_incl.
          apply H_in2_copy.
          assumption.
        * assert (H_in_v0 : In v0 (equivocating_senders (next_equivocation_rec' s1' vs v))).
          { apply next_equivocations_equivocating_senders_left_weak. 
            subst; assumption. intros.
            2 : assumption.
            intro H_absurd; subst; contradiction. } 
          rewrite <- Heqs3 in H_in_v0.
          eapply equivocating_senders_incl.
          exact H_in3_copy. 
          assumption.
    }
    assert (H_s_overweight : (proj1_sig (weight v) + fault_weight_state (proj1_sig s2) + sum_weights vs <= fault_weight_state s)%R). 
    { replace ((proj1_sig (weight v) + fault_weight_state (proj1_sig s2) + sum_weights vs))%R with (sum_weights ([v] ++ (equivocating_senders (proj1_sig s2)) ++ vs)).
      apply sum_weights_incl.
      { (* Proving mutual NoDup *) 
        apply nodup_append.
        apply NoDup_cons. intros; inversion 1.
        constructor.
        apply nodup_append.
        apply set_map_nodup. assumption.
        { intros. intro Habsurd. spec H_disjoint a Habsurd.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a H. contradiction.
        }
        { intros. intro Habsurd. spec H_disjoint a H.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a Habsurd. contradiction. }
        { intros. inversion H. intro Habsurd.
          apply in_app_iff in Habsurd. destruct Habsurd.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H1.
          subst; contradiction. subst; contradiction. inversion H0. } 
        { intros. intro Habsurd.
          inversion Habsurd.
          apply in_app_iff in H. destruct H.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H.
          subst; contradiction. subst; contradiction. inversion H0. } 
      }
      apply set_map_nodup. assumption.
      do 2 rewrite sum_weights_app.
      unfold fault_weight_state.
      simpl. ring. }
    apply protocol_state_not_heavy in about_s.
    red in about_s.
    assert (H_finale := Rle_trans _ _ _ H_s_overweight about_s). auto.
    clear -H_finale H_over H_s1_s2_weight.
    rewrite sum_weights_app in H_over.
    unfold fault_weight_state in H_s1_s2_weight at 1. 
    rewrite H_s1_s2_weight in H_over.
    apply (Rplus_gt_compat_l (proj1_sig (weight v))) in H_over. 
    replace (proj1_sig (weight v) + (proj1_sig t_full - proj1_sig (weight v)))%R with (proj1_sig t_full)%R in H_over by ring.
    rewrite <- Rplus_assoc in H_over. 
    apply Rgt_not_le in H_over.
    contradiction.
Qed. 


(*
Class CBC_protocol :=
   {
      (** Consensus values equipped with reflexive transitive comparison **) 
      consensus_values : Type; 
      about_consensus_values : StrictlyComparable consensus_values; 
      (** Validators equipped with reflexive transitive comparison **) 
      validators : Type; 
      about_validators : StrictlyComparable validators; 
      (** Weights are positive reals **) 
      weight : validators -> {r | (r > 0)%R}; 
      (** Threshold is a non-negative real **) 
      t : {r | (r >= 0)%R}; 
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R; 
      (** States with syntactic equality **) 
      state : Type;
      about_state : StrictlyComparable state;
      state0 : state; 
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_union s1 s2 = state_union s2 s1;
      (** Reachability relation **) 
      reach : state -> state -> Prop;
      reach_refl : forall s, reach s s; 
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3; 
      reach_union : forall s1 s2, reach s1 (state_union s1 s2);  
      (** Total estimator **)
      E : state -> consensus_values -> Prop; 
      estimator_total : forall s, exists c, E s c; 
      (** Protocol state definition as predicate **) 
      prot_state : state -> Prop; 
      about_state0 : prot_state state0;
      (** Equivocation weights from states **) 
      equivocation_weight : state -> R; 
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R; 
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2); 
   }.
 *)

Theorem reach_total `{CBC_protocol_eq} :
  forall s, exists s', reach s s'.
Proof. intro s. exists (state_union s s). apply (reach_union s s). Qed.

(** Defining A **) 
Definition pstate `{CBC_protocol_eq} : Type := {s : state | prot_state s}. 
Definition pstate_proj1 `{CBC_protocol_eq} (p : pstate) : state :=
  proj1_sig p. 
Coercion pstate_proj1 : pstate >-> state.

(** Proving A_eq_dec **)
Lemma pstate_eq_dec `{CBC_protocol_eq} : forall (p1 p2 : pstate), {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  assert (H_useful := about_state). 
  now apply sigify_eq_dec. 
Qed.

(** Proving A_inhabited **) 
Lemma pstate_inhabited `{CBC_protocol_eq} : exists (p1 : pstate), True.
Proof. now exists (exist prot_state state0 about_state0). Qed. 

(** Defining A_rel **) 
Definition pstate_rel `{CBC_protocol_eq} : pstate -> pstate -> Prop :=
  fun p1 p2 => reach (pstate_proj1 p1) (pstate_proj1 p2).

(** Proving A_rel_refl **) 
Lemma pstate_rel_refl `{CBC_protocol_eq} : Reflexive pstate_rel.
Proof. red; intro p; now apply reach_refl. Qed.

(** Proving A_rel_trans **) 
Lemma pstate_rel_trans `{CBC_protocol_eq} : Transitive pstate_rel. 
Proof. 
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  now apply reach_trans with p2.
Qed.

Instance level0 `{CBC_protocol_eq} : PartialOrder :=
  { A := pstate;
    A_eq_dec := pstate_eq_dec;
    A_inhabited := pstate_inhabited;
    A_rel := pstate_rel;
    A_rel_refl := pstate_rel_refl;
    A_rel_trans := pstate_rel_trans;
  }.



Section CommonFutures. 

  (* Theorem 1 *) 
  Theorem pair_common_futures `{CBC_protocol_eq}:
    forall s1 s2 : pstate,
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      exists s : pstate, pstate_rel s1 s /\ pstate_rel s2 s.
  Proof.
    intros s1 s2 H_weight. remember s1 as ps1. remember s2 as ps2.
    destruct s1 as [s1 H_s1]. destruct s2 as [s2 H_s2].
    rewrite Heqps1, Heqps2 in H_weight; simpl in H_weight.

    exists (exist _ (state_union s1 s2) (about_prot_state s1 s2 H_s1 H_s2 H_weight)).
    subst. unfold pstate_rel. simpl.
    split. apply reach_union.
    apply (reach_morphism s2 (state_union s2 s1) (state_union s1 s2)). 
    apply reach_union.
    apply state_union_comm. 
  Qed.
  
  Lemma reach_union_iter `{CBC_protocol_eq} :
    forall s ls, In s ls -> reach s (fold_right state_union state0 ls). 
  Proof.
    intros s ls H_in.
    induction ls as [|hd tl IHtl].
    - inversion H_in.
    - destruct H_in as [Heq | Hneq].
      + subst.
        simpl. apply reach_union.
      + spec IHtl Hneq. simpl.
        eapply reach_trans.
        exact IHtl.
        apply (reach_morphism (fold_right state_union state0 tl)
                              (state_union (fold_right state_union state0 tl) hd)
                              (state_union hd (fold_right state_union state0 tl))).
        apply reach_union. apply state_union_comm.
  Qed.

  Lemma prot_state_union_iter `{CBC_protocol_eq} :
    forall ls, Forall prot_state ls ->
          (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
          prot_state (fold_right state_union state0 ls). 
  Proof. 
    intros ls H_ls H_weight.
    induction ls as [|hd tl IHls].
    - simpl. exact about_state0.
    - simpl. apply about_prot_state.
      apply (Forall_inv H_ls).
      spec IHls. 
      apply Forall_forall. intros x H_in.
      rewrite Forall_forall in H_ls. spec H_ls x.
      spec H_ls. right; assumption. assumption. 
      spec IHls.
      simpl in H_weight.
      apply (Rle_trans (equivocation_weight (fold_right state_union state0 tl))
                       (equivocation_weight (state_union hd (fold_right state_union state0 tl)))
                       (proj1_sig t)).  
      apply equivocation_weight_compat.
      assumption. assumption. assumption.
  Qed.

  Lemma pstate_list `{CBC_protocol_eq} :
    forall pls : list pstate,
      Forall prot_state (map (fun ps => proj1_sig ps) pls).
  Proof.
    intros.
    apply Forall_forall.
    induction pls; intros. 
    - inversion H0.
    - destruct H0 as [Heq | Hin].
      + subst. destruct a as [a H_a]. simpl. assumption.
      + apply IHpls. assumption.
  Qed.

  (* Theorem 2 *) 
  Theorem n_common_futures `{CBC_protocol_eq} :
    forall ls : list pstate,
      (equivocation_weight (fold_right state_union state0 (map (fun ps => proj1_sig ps) ls)) <= proj1_sig t)%R ->
      exists ps : pstate, Forall (fun ps' => pstate_rel ps' ps) ls.
  Proof.
    intros pls H_weight.
    remember (map (fun ps => proj1_sig ps) pls) as ls.
    assert (H_ls : Forall prot_state ls) by (subst; apply pstate_list).
    exists (exist _ (fold_right state_union state0 ls) (prot_state_union_iter ls H_ls H_weight)).
    apply Forall_forall. intros. destruct x as [x H_x]. unfold pstate_rel. simpl.
    apply reach_union_iter.
    subst. apply in_map_iff.
    exists (exist (fun s : state => prot_state s) x H_x). simpl.
    split; reflexivity || assumption.
  Qed. 

End CommonFutures.

(* Level Specific -refines-> Level 0 *) 

Definition reach_one `{CBC_protocol_eq} (sigma1 sigma2 : pstate) : Prop :=
  sigma1 <> sigma2 /\ pstate_rel sigma1 sigma2 /\
  forall sigma
    ,  pstate_rel sigma1 sigma
    -> pstate_rel sigma sigma2
    -> sigma = sigma1 \/ sigma = sigma2.


Inductive all_path_eventually `{CBC_protocol_eq} (P : pstate -> Prop) (sigma : pstate) : Prop :=
  | all_path_holds_now
    : P sigma -> all_path_eventually P sigma
  | all_path_holds_next
    :  (exists sigma', reach_one sigma sigma')
    -> (forall sigma', reach_one sigma sigma' -> all_path_eventually P sigma')
    -> all_path_eventually P sigma
  .

Inductive one_path_eventually `{CBC_protocol_eq} (P : pstate -> Prop) (sigma : pstate) : Prop :=
  | one_path_holds_now
    : P sigma -> one_path_eventually P sigma
  | one_path_holds_next
    :  forall sigma'
    ,  reach_one sigma sigma'
    -> one_path_eventually P sigma'
    -> one_path_eventually P sigma
  .



Section Consistency.

  Definition decided `{CBC_protocol_eq} (P : pstate -> Prop) : pstate -> Prop :=
    fun (s : pstate) => forall s', pstate_rel s s' -> P s'. 

  Definition decided_on_predicate `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop
    :=
    fun (future : pstate) => forall c', E (proj1_sig future) c' -> c' = c.

  Definition decided_on `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    decided (decided_on_predicate c).

  Definition locked_on `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    all_path_eventually (decided_on c).

  Definition not_locked_off `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    one_path_eventually (decided_on c).

  Definition not `{CBC_protocol_eq} (P : pstate -> Prop) : pstate -> Prop :=
    fun s => P s -> False.

  Definition locked_off `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    not (not_locked_off c).

  Lemma forward_consistency `{CBC_protocol_eq} :
    forall s P,
      decided P s ->
      forall s',
        pstate_rel s s' ->
        decided P s'.
  Proof.
    intros s P H_dec s' H_rel.
    unfold decided in *.
    intros s'' H_rel'.
    assert (pstate_rel s s'') by (apply (pstate_rel_trans s s' s''); assumption).
    spec H_dec s''; now apply H_dec. 
  Qed.

  Lemma backward_consistency `{CBC_protocol_eq} :
    forall s s',
      pstate_rel s s' ->
      forall P,
      decided P s' ->
      ~ decided (not P) s.
  Proof. 
    intros s s' H_rel P H_dec Hnot.
    unfold decided in *.
    spec Hnot s' H_rel.
    apply Hnot.
    apply H_dec.
    apply pstate_rel_refl.
  Qed. 

  (* Theorem 3 *) 
  Theorem pair_consistency_prot `{CBC_protocol_eq} :
    forall s1 s2 : pstate,
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      forall P, 
        ~ (decided P s1 /\ decided (not P) s2).
  Proof.
    intros s1 s2 H_weight P [H_dec H_dec_not].
    destruct (pair_common_futures s1 s2 H_weight) as [s [H_r1 H_r2]].
    spec H_dec s H_r1.
    spec H_dec_not s H_r2. contradiction.
  Qed. 

  (* Consistency on state properties *) 
  Definition state_consistency `{CBC_protocol_eq} (ls : list pstate) : Prop :=
    exists s : pstate,
      forall (P : pstate -> Prop),
        Exists (fun s => decided P s) ls ->
        P s.

  (* Theorem 4 *) 
  Theorem n_consistency_prot `{CBC_protocol_eq} :
    forall ls : list pstate,
      (equivocation_weight (fold_right state_union state0 (map (fun ps => proj1_sig ps) ls)) <= proj1_sig t)%R ->
      state_consistency ls.
  Proof.
    intros ls H_weight. 
    destruct (n_common_futures ls H_weight) as [s' H_reach].
    exists s'. 
    intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s'' [H_in'' H_dec'']].
    rewrite Forall_forall in H_reach. 
    spec H_reach s'' H_in''.
    spec H_dec'' s' H_reach.
    assumption.
  Qed.

  (* Consistency on consensus values *) 
  Definition lift `{CBC_protocol_eq} (P : consensus_values -> Prop) : pstate -> Prop :=
    fun s => forall c : consensus_values, E (proj1_sig s) c -> P c.

  Definition consensus_value_consistency `{CBC_protocol_eq} (ls : list pstate) : Prop :=
    exists c,
      forall (P : consensus_values -> Prop),
        Exists (fun s => decided (lift P) s) ls ->
        P c. 

  (* Theorem 5 *)
  Theorem n_consistency_consensus `{CBC_protocol_eq} :
    forall ls : list pstate,
      (equivocation_weight (fold_right state_union state0 (map (fun ps => proj1_sig ps) ls)) <= proj1_sig t)%R ->
      consensus_value_consistency ls. 
  Proof.
    intros ls H_weight. 
    destruct (n_consistency_prot ls H_weight) as [s H_dec].
    destruct (estimator_total s) as [c about_c].
    exists c. intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s' [H_in' H_dec']].
    spec H_dec (lift P).
    spec H_dec. apply Exists_exists.
    exists s'. split; assumption.
    unfold lift in H_dec.
    spec H_dec c about_c; assumption.
  Qed.

End Consistency.

(* We can either start with PartialOrderNonLCish or CBC_protocol_eq - let's do the latter for now *)

(* Level Specific-plus : *)
Class CBC_protocol_eq_plus `{CBC_protocol_eq} :=
  {
    two_validators : exists (v1 v2 : validators), v1 <> v2;
    equivocating_senders : state -> list validators;
    next_equivocation : state -> validators -> validators -> state;
    about_next_equivocation1 : forall s v v', reach s (next_equivocation s v v');
    about_next_equivocation2 : forall s, prot_state s -> forall v v', ~ In v (equivocating_senders s) -> equivocation_weight (next_equivocation s v v') = (equivocation_weight s + proj1_sig (weight v))%R;
    about_next_equivocation3 : forall s, prot_state s -> forall v v', ~ In v (equivocating_senders s) -> (equivocation_weight s + proj1_sig (weight v) <= proj1_sig t)%R -> prot_state (next_equivocation s v v') /\ (equivocation_weight (next_equivocation s v v') = equivocation_weight s + proj1_sig (weight v))%R;
  }.

(*
Section Triviality.
  Lemma distinct_sender_total `{CBC_protocol_eq_plus} : forall v1 : validators, exists v2 : validators, v1 <> v2.
  Proof.
    intros.
    destruct two_validators  as [v1' [v2' Hneq]].
    remember about_validators as Hv. 
    destruct (compare_eq_dec v1 v1') eqn:Heq.
    - subst. exists v2'. assumption.
    - exists v1'. assumption.
  Qed.

  Definition get_distinct_sender `{CBC_protocol_eq_plus} (v : validators) :=
    proj1_sig (choice validators (fun v' => v <> v') (distinct_sender_total v)).

  Definition get_distinct_sender_correct `{CBC_protocol_eq_plus} (v : validators) :=
    proj2_sig (choice validators (fun v' => v <> v') (distinct_sender_total v)).

  Lemma get_distinct_sender_correct' `{CBC_protocol_eq_plus} :
    forall v, get_distinct_sender v <> v. 
  Proof.
    intros. unfold get_distinct_sender.
    assert (H_useful := get_distinct_sender_correct v).
    simpl in *.
    intro H_absurd.
    apply H_useful; symmetry; assumption.
  Qed.
  
  Definition pstate `{CBC_protocol_eq} : Type := {s : state | prot_state s}. 

  Definition pstate_proj1 `{CBC_protocol_eq} (p : pstate) : state :=
    proj1_sig p. 

  Coercion pstate_proj1 : pstate >-> state.

  Definition pstate_rel `{CBC_protocol_eq} : pstate -> pstate -> Prop :=
    fun p1 p2 => reach (pstate_proj1 p1) (pstate_proj1 p2).

  Definition non_trivial_pstate `{CBC_protocol_eq} (P : pstate -> Prop) :=
    (exists (s1 : pstate), forall (s : pstate), pstate_rel s1 s -> P s)
    /\
    (exists (s2 : pstate), forall (s : pstate), pstate_rel s2 s -> (P s -> False)).

  Definition in_future `{CBC_protocol_eq} (s1 s2 : state) :=
    reach s1 s2. 

  (* Here we can't use messages, so we must explicitly describe a minimal transition in terms of general transitions *) 
  Definition next_future `{CBC_protocol_eq} (s1 s2 : state) :=
    (* exists (msg : message), add_in_sorted_fn msg s1 = s2.  *)
    reach s1 s2 /\
    forall s, reach s1 s /\ reach s s2 -> False. 

  Definition in_past `{CBC_protocol_eq} (s1 s2 : state) :=
    reach s2 s1. 

  Definition no_common_future `{CBC_protocol_eq} (s1 s2 : pstate) :=
    forall (s : pstate), in_future s1 s /\ in_future s2 s -> False. 

  Definition yes_common_future `{CBC_protocol_eq} (s1 s2 : pstate) :=
    exists (s : pstate), in_future s1 s /\ in_future s2 s. 

  Definition strong_nontriviality `{CBC_protocol_eq} :=
    (* For every state, there exists a state *) 
    forall (s1 : pstate),
    exists (s2 : pstate),
      (* That is reachable in one step *) 
      next_future s1 s2 /\
      (* And there exists a third state *)
      exists (s3 : pstate),
        (* Such that s1 and s3 share a common future *)
        yes_common_future s1 s3
        /\
        (* But s2 and s3 don't. *) 
        no_common_future s2 s3. 

  Fixpoint next_equivocation_rec' `{CBC_protocol_eq_plus} (s : state) (vs : list validators) (v0 : validators) : state :=
  match vs with
  | [] => s
  | hd :: tl => next_equivocation (next_equivocation_rec' s tl v0) hd v0
  end.

End Triviality. 
 *)


