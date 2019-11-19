Require Import List Streams.
Import ListNotations.

From Casper
Require Import ListExtras vlsm.


(* Trace segments *)

Inductive trace_from_to
  {message}
  `{V : VLSM message}
  : protocol_state -> list protocol_state -> protocol_state -> Prop
  :=
  | trace_from_to_one
    (s1 s2 : protocol_state)
    (Hv12 : valid_transition s1 s2)
    : trace_from_to s1 [] s2
  | trace_from_to_more
    (s1 s2 : protocol_state)
    (ts : list protocol_state)
    (s3 : protocol_state)
    (Hv12 : valid_transition s1 s2)
    (Ht23 : trace_from_to s2 ts s3)
    : trace_from_to s1 (s2 :: ts) s3
  .

Lemma extend_trace_from_to_right
  {message}
  `{V : VLSM message}
  (s1 : protocol_state)
  (ls : list protocol_state)
  (s2 s3 : protocol_state)
  (Ht12 : trace_from_to s1 ls s2)
  (Hv23 : valid_transition s2 s3)
  : trace_from_to s1 (ls ++ [s2]) s3.
Proof.
  intros.
  induction Ht12.
  - simpl. apply trace_from_to_more; try assumption.
    apply trace_from_to_one. assumption.
  - specialize (IHHt12 Hv23).
    rewrite <- app_comm_cons.
    apply trace_from_to_more; assumption.
Qed.


(* Labeled trace segments *)

Inductive labeled_trace_from_to
  {message}
  `{V : VLSM message}
  : protocol_state -> list (label * option protocol_message) -> protocol_state -> Prop
  :=
  | lebeled_empty_trace
    : forall s,
      labeled_trace_from_to s [] s
  | labeled_trace_from_to_more
    : forall s1 l opm s2 ts s3
     (Hv12 : labeled_valid_transition opm l s1 s2)
     (Ht23 : labeled_trace_from_to s2 ts s3),
    labeled_trace_from_to s1 ((l, opm) :: ts) s3
  .


Notation "s1 '==' ts '=>' s2" :=
  (labeled_trace_from_to s1 ts s2)
  (at level 20).


Lemma labeled_extend_trace_from_to_right
  {message}
  `{V : VLSM message}
  : forall s1 ls s2 l opm s3
  (Ht12 : s1 ==(ls)=> s2)
  (Hv23 : labeled_valid_transition opm l s2 s3),
  s1 ==(ls ++ [(l, opm)])=> s3.
Proof.
  intros.
  induction Ht12.
  - simpl. apply labeled_trace_from_to_more with s3; try assumption. constructor.
  - specialize (IHHt12 Hv23).
    rewrite <- app_comm_cons.
    apply labeled_trace_from_to_more with s2; assumption.
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
    infinite_trace_from s1 (Cons s2 ts)
  .

(* Infinite labeled trace from state *)

CoInductive labeled_infinite_trace_from
  {message}
  `{V : VLSM message}
  : protocol_state -> Stream (label * option protocol_message) -> Prop
  :=
  | labeled_infinite_trace_first
    : forall s1 l opm s2 ts,
    labeled_valid_transition opm l s1 s2 ->
    labeled_infinite_trace_from s2 ts ->
    labeled_infinite_trace_from s1 (Cons (l, opm) ts)
  .


(* A trace is either finite or infinite *)

Inductive Trace `{VLSM} : Type :=
  | Finite : list protocol_state -> Trace
  | Infinite : Stream protocol_state -> Trace
  .

Inductive LabeledTrace `{VLSM} : Type :=
  | LabeledFinite
  : protocol_state -> list (label * option protocol_message) -> protocol_state -> LabeledTrace
  | LabeledInfinite
  : protocol_state -> Stream (label * option protocol_message) -> LabeledTrace
  .

Lemma unlabel_finite_trace `{VLSM}
  (s1 : protocol_state)
  (t : list (label * option protocol_message))
  (Hnet : t <> [])
  (s2 : protocol_state)
  (Hlt : s1 == t => s2)
  : exists t' : list protocol_state,
  trace_from_to s1 t' s2 /\ length t' = length t + 1 /\
  forall (i : nat) (Hi : i < length t) (si si' : protocol_state)
    (Hsi : nth_error (s1 :: t' ++ [s2]) i = Some si)
    (Hsi' : nth_error (s1 :: t' ++ [s2]) (i + 1) = Some si')
    (li : label) (opmi : option protocol_message)
    (Hmi : nth_error t i = Some (li, opmi)),
    labeled_transition
    
    
    .
Proof.
  induction Hlt.
  - contradiction.
  - destruct ts.
    + inversion Hlt; subst; clear Hlt.  exists []. apply trace_from_to_one. exists opm.  exists l. assumption.
    + exists [s2]. apply trace_from_to_more.
      * exists  opm. exists l. assumption.
      * 
Admitted.

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
      assert (Hvt' : valid_transition ps ps')
        by (apply valid_transition_proof_irrelevance with s; assumption).
      apply (extend_protocol_trace pt ps ps') in Hvt'; try assumption.
      destruct Hvt' as [pt' Hlast].
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
