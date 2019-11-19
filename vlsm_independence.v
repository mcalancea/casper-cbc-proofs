From Casper
Require Import vlsm.

Class LSM_bisim (message : Type) {S : LSM_sig message } `{L : @LSM message S}
  :=
  { lsm_bisim : state -> state -> Prop
  ; lsm_sim_prop
    : forall
      (p q : state)
      (Hb : lsm_bisim p q)
      (l : label)
      (om : option proto_message),
      let (p', _) := transition l (p, om) in
      let (q', _) := transition l (q, om) in
      lsm_bisim p' q'
  }.


Class LSM_independence (message : Type) {S : LSM_sig message } `{L : @LSM message S}
  :=
  { lsm_independence
    : forall
      (s1 : state)
      (l1 l2 : label)
      (m1 m2 : proto_message),
      let (s2, _) := transition l1 (s1, Some m1) in
      let (s3, _) := transition l2 (s2, Some m2) in
      let (s2', _) := transition l2 (s1, Some m2) in
      let (s3', _) := transition l1 (s2', Some m1) in
      s3 = s3'
  ; lsm_independence_no_message
    : forall
      (s1 : state)
      (l1 l2 : label)
      (m2 : proto_message),
      let (s2, _) := transition l1 (s1, None) in
      let (s3, _) := transition l2 (s2, Some m2) in
      let (s3', _) := transition l2 (s1, Some m2) in
      s3 = s3'
  }.

Class VLSM_independence 
  (message : Type) {S : LSM_sig message } {L : @LSM message S}
  `{LI : @LSM_independence message S L} `{V : @VLSM message S L}
  :=
  { vlsm_independence
    : forall
      (s1 : state)
      (l1 l2 : label)
      (m1 m2 : proto_message),
      let (s2, _) := transition l1 (s1, Some m1) in
      let (s2', _) := transition l2 (s1, Some m2) in
      valid l1 (s1, Some m1) /\ valid l2 (s2, Some m2) ->
      valid l2 (s1, Some m2) /\ valid l1 (s2', Some m1)
  ; vlsm_independence_no_message
    : forall
      (s1 : state)
      (l1 l2 : label)
      (m2 : proto_message),
      let (s2, _) := transition l1 (s1, None) in
      valid l1 (s1, None) -> valid l2 (s2, Some m2) <-> valid l2 (s1, Some m2)
  }.