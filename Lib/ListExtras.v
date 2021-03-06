Require Import Coq.Bool.Bool Coq.Arith.Lt.
Require Import List.
Import ListNotations.

Require Import Coq.Logic.FinFun.

Require Import Casper.Lib.Preamble.


Definition last_error {S} (l : list S) : option S :=
  match l with
  | [] => None
  | a :: t => Some (last t a)
  end.

Lemma unfold_last_hd {S} : forall (random a b : S) (l : list S),
  last (a :: (b :: l)) random = last (b :: l) random.
Proof.
  intros random h1 h2 tl. 
  unfold last. reflexivity.
Qed.

Lemma swap_head_last {S} : forall (random a b c : S) (l : list S),
    last (a :: b :: c :: l) random = last (b :: a :: c :: l) random. 
Proof.
  intros random h1 h2 s tl.
  induction tl as [| hd tl IHl].
  - reflexivity. 
  - simpl. reflexivity.
Qed.

Lemma remove_hd_last {X} :
  forall (hd1 hd2 d1 d2 : X) (tl : list X),
    last (hd1 :: hd2 :: tl) d1 = last (hd2 :: tl) d2.
Proof. 
  intros. induction tl.
  simpl. reflexivity.
  rewrite unfold_last_hd. 
  rewrite unfold_last_hd in IHtl.
  rewrite unfold_last_hd.
  rewrite unfold_last_hd.
  destruct tl. 
  reflexivity.
  do 2 rewrite unfold_last_hd in IHtl.
  do 2 rewrite unfold_last_hd.
  assumption.
Qed.

Lemma unroll_last {S} : forall (random a : S) (l : list S),
  last (a :: l) random = last l a.
Proof.
  induction l; try reflexivity.
  destruct l; try reflexivity.
  rewrite swap_head_last. rewrite unfold_last_hd. rewrite IHl.
  rewrite unfold_last_hd. reflexivity.
Qed.

Lemma incl_empty : forall A (l : list A),
  incl l nil -> l = nil.
Proof.
  intros. destruct l; try reflexivity.
  exfalso. destruct (H a). left. reflexivity.
Qed.

Lemma incl_singleton {A} : forall (l : list A) (a : A),
  incl l [a] ->
  forall b, In b l -> b = a.
Proof.
  intros. induction l; inversion H0; subst.
  - clear H0. destruct (H b); try (left; reflexivity); subst; try reflexivity.
    inversion H0.
  - apply IHl; try assumption.
    apply incl_tran with (a0 :: l); try assumption.
    apply incl_tl. apply incl_refl.
Qed.

Lemma filter_in : forall A (f : A -> bool) x s,
  In x s ->
  f x = true ->
  In x (filter f s).
Proof.
  induction s; intros; inversion H; subst; clear H; simpl.
  - rewrite H0. left. reflexivity.
  - apply IHs in H1; try assumption.
    destruct (f a); try assumption.
    right. assumption.
Qed.

Lemma filter_incl {A} (f : A -> bool) : forall s1 s2,
  incl s1 s2 ->
  incl (filter f s1) (filter f s2).
Proof.
  induction s1; intros; intro x; intros. 
  - inversion H0.
  - simpl in H0. destruct (f a) eqn:Hfa.
    + destruct H0.
      * subst. apply filter_in; try assumption. apply H. left. reflexivity.
      * apply IHs1; try assumption. intro y; intro. apply H. right. assumption.
    + apply IHs1; try assumption. intro y; intro. apply H. right. assumption.
Qed.

Lemma filter_incl_fn {A} : forall (f : A -> bool) (g : A -> bool),
  (forall a, f a = true -> g a = true) ->
  forall s, incl (filter f s) (filter g s).
Proof.
  induction s; simpl.
  - apply incl_refl.
  - intro x; intros. destruct (f a) eqn:Hfa.
    + apply H in Hfa. rewrite Hfa. destruct H0.
      * subst. left. reflexivity.
      * right. apply IHs. assumption.
    + apply IHs in H0. destruct (g a).
      * right; assumption.
      * assumption.
Qed.

Lemma filter_eq_fn {A} : forall (f : A -> bool) (g : A -> bool) s,
  (forall a, In a s -> f a = true <-> g a = true) ->
  filter f s = filter g s.
Proof.
  induction s; intros; try reflexivity. simpl.
  assert (IHs' : forall a : A, In a s -> f a = true <-> g a = true).
  { intros. apply H. right. assumption. }
  apply IHs in IHs'. clear IHs.
  destruct (f a) eqn:Hf.
  - apply H in Hf as Hg; try (left; reflexivity). rewrite Hg. rewrite IHs'. reflexivity.
  - assert (Hg : g a = false).
    {  destruct (g a) eqn:Hg; try reflexivity. apply H in Hg; try (left; reflexivity).
      rewrite <- Hg. assumption.
    }
    rewrite Hg. assumption.
Qed.

Lemma in_not_in : forall A (x y : A) l,
  In x l ->
  ~ In y l ->
  x <> y.
Proof.
  intros. intro; subst. apply H0. assumption.
Qed.

Fixpoint inb {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (x : A) (xs : list A) :=
  match xs with 
  | [] => false
  | h::t => if Aeq_dec x h then true else inb Aeq_dec x t
  end.

Lemma in_function {A}  (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  PredicateFunction2 (@In A) (inb Aeq_dec).
Proof.
  intros x xs. induction xs; split; intros.
  - inversion H.
  - inversion H.
  - simpl. destruct H as [Heq | Hin].
    + subst. apply eq_dec_if_true. reflexivity.
    + apply IHxs  in Hin. rewrite Hin. destruct (Aeq_dec x a); reflexivity.
  - simpl in H. destruct (Aeq_dec x a).
    + subst. left. reflexivity.
    + right. apply IHxs. assumption.
Qed.

Lemma in_correct {X} `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    In x l <-> inb compare_eq_dec x l = true. 
Proof.
  intros s msg.
  apply in_function.
Qed.

Lemma in_correct' {X} `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    ~ In x l <-> inb compare_eq_dec x l = false. 
Proof.
  intros s msg.
  symmetry. apply mirror_reflect_curry. 
  symmetry; now apply in_correct. 
Qed.

Lemma map_injective : forall A B (f : A -> B),
  Injective f -> Injective (map f).
Proof.
  intros. intros xs ys. generalize dependent ys.
  induction xs; intros; destruct ys; split; intros; try reflexivity; try discriminate.
  - simpl in H0. inversion H0 . apply H in H2; subst. apply IHxs in H3; subst. reflexivity.
  - rewrite H0. reflexivity.
Qed.

Lemma map_incl {A B} (f : B -> A) : forall s s',
  incl s s' ->
  incl (map f s) (map f s').
Proof.
  intros s s' Hincl fx Hin.
  apply in_map_iff .
  apply in_map_iff in Hin.
  destruct Hin as [x [Heq Hin]].
  exists x. split; try assumption. apply Hincl. assumption.
Qed.

Lemma existsb_forall {A} (f : A -> bool):
  forall l, existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  induction l; split; intros.
  - inversion H0. 
  - reflexivity.
  - inversion H. apply orb_false_iff in  H2. destruct H2 as [Hfa Hex]. rewrite Hfa.
    rewrite Hex. simpl. destruct H0 as [Heq | Hin]; subst; try assumption.
    apply IHl; try assumption.
  - simpl. rewrite H; try (left; reflexivity). rewrite IHl; try reflexivity.
    intros. apply H. right. assumption.
Qed.

Definition app_cons {A}
  (a : A)
  (l : list A)
  : [a] ++ l = a :: l
  := eq_refl.

Lemma append_nodup_left {A}:
  forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  induction l1; intros.
  - constructor.
  - inversion H. apply IHl1 in H3. constructor; try assumption. intro. apply H2.
    apply in_app_iff. left. assumption.
Qed.

Lemma append_nodup_right {A}:
  forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  induction l1; intros.
  - simpl in H. assumption.
  - simpl in H. inversion H. apply IHl1 in H3. assumption.
Qed.

Lemma nodup_append {A} : forall (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall a, In a l1 -> ~ In a l2) ->
  (forall a, In a l2 -> ~ In a l1) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1; simpl; intros; try assumption.
  inversion H; subst; clear H. constructor.
  - intro. apply in_app_iff in H. destruct H as [Inl1 | InL2].
    + apply H5. assumption.
    + apply (H1 a); try assumption.
      left. reflexivity.
  - apply IHl1; try assumption; intros.
    + apply H1. right. assumption.
    + apply H2 in H. intro. apply H. right. assumption.
Qed.

Lemma last_is_last {A} : forall (l : list A) (x dummy: A),
  last (l ++ [x]) dummy = x.
Proof.
  induction l; try reflexivity; intros.
  rewrite <- app_comm_cons. specialize (IHl x dummy). rewrite <- IHl at 2. simpl.
  destruct l; simpl; reflexivity.
Qed.

Lemma last_error_is_last {A} : forall (l : list A) (x : A),
  last_error (l ++ [x]) = Some x.
Proof.
  destruct l; try reflexivity; intros; simpl. apply f_equal. apply last_is_last.
Qed.

(** Polymorphic list library **)

Fixpoint is_member {W} `{StrictlyComparable W} (w : W) (l : list W) : bool :=
  match l with
  | [] => false
  | hd :: tl => match compare w hd with
              | Eq => true
              | _ => is_member w tl
              end
  end.

Definition compareb {A} `{StrictlyComparable A} (a1 a2 : A) : bool :=
  match compare a1 a2 with
  | Eq => true
  | _ => false
  end.

Lemma is_member_correct {W} `{StrictlyComparable W} : forall l w, is_member w l = true <-> In w l. 
Proof. 
  intros l w.
  induction l as [|hd tl IHl].
  - split; intro H'. 
    + unfold is_member in H'; inversion H'.  
    + inversion H'.
  - split; intro H'.
    + simpl in H'.
      destruct (compare w hd) eqn:Hcmp;
        try (right; apply IHl; assumption ). 
      apply StrictOrder_Reflexive in Hcmp.
      left. symmetry; assumption.
    + apply in_inv in H'.
      destruct H' as [eq | neq]. 
      rewrite eq.
      simpl.
      rewrite compare_eq_refl. 
      reflexivity.
      rewrite <- IHl in neq.
      simpl. assert (H_dec := compare_eq_dec w hd).
      destruct H_dec as [Heq | Hneq].
      rewrite Heq. rewrite compare_eq_refl. reflexivity.
      destruct (compare w hd); try reflexivity;
        assumption.
Qed.

Lemma is_member_correct' {W} `{StrictlyComparable W} : forall l w, is_member w l = false <-> ~ In w l. 
Proof.
  intros. 
  apply mirror_reflect.
  intros; apply is_member_correct.
Qed.

Lemma In_app_comm {X} : forall l1 l2 (x : X), In x (l1 ++ l2) <-> In x (l2 ++ l1). 
Proof.
  intros l1 l2 x; split; intro H_in;
  apply in_or_app; apply in_app_or in H_in;
    destruct H_in as [cat | dog];
    tauto.
Qed.

Require Import Streams.

Definition stream_app
  {A : Type}
  (prefix : list A)
  (suffix : Stream A)
  : Stream A
  :=
  fold_right (@Cons A) suffix prefix.


Definition stream_app_cons {A}
  (a : A)
  (l : Stream A)
  : stream_app [a] l = Cons a l
  := eq_refl.

Lemma stream_app_assoc
  {A : Type}
  (l m : list A)
  (n : Stream A)
  : stream_app l (stream_app m n) = stream_app (l ++ m) n.
Proof.
  induction l; try reflexivity.
  simpl. apply f_equal. assumption.
Qed.

Lemma stream_app_f_equal
  {A : Type}
  (l1 l2 : list A)
  (s1 s2 : Stream A)
  (Hl : l1 = l2)
  (Hs : EqSt s1 s2)
  : EqSt (stream_app l1 s1) (stream_app l2 s2)
  .
Proof.
  subst. induction l2; try assumption.
  simpl. constructor; try reflexivity. assumption.
Qed.

Fixpoint stream_prefix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : list A
  := match n,l with
  | 0,_ => []
  | S n, Cons a l => a :: stream_prefix l n
  end.

Lemma stream_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : Stream A)
  (n : nat)
  : List.map f (stream_prefix l n) = stream_prefix (Streams.map f l) n
  .
Proof.
  generalize dependent l. induction n; intros [a l]; try reflexivity.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma stream_prefix_length
  {A : Type}
  (l : Stream A)
  (n : nat)
  : length (stream_prefix l n) = n
  .
Proof.
  generalize dependent l. induction n; intros [a l]; try reflexivity.
  simpl in *. f_equal.
  apply IHn.
Qed.

Definition stream_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : Stream A
  := Str_nth_tl n l.

Lemma stream_prefix_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_app (stream_prefix l n) (stream_suffix l n) = l
  .
Proof.
  generalize dependent l. unfold stream_suffix.
  induction n; try reflexivity; intros [a l]; simpl.
  f_equal. apply IHn.
Qed.

Lemma nth_error_last
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlast: S n = length l)
  (_last : A)
  : nth_error l n = Some (last l _last)
  .
Proof.
  generalize dependent _last.
  generalize dependent l.
  induction n; intros.
  - destruct l; inversion Hlast. symmetry in H0.
    apply length_zero_iff_nil in H0. subst. reflexivity.
  - destruct l; inversion Hlast.
    specialize (IHn l H0 _last). rewrite unroll_last.
    simpl. rewrite IHn. f_equal.
    destruct l; inversion H0.
    repeat rewrite unroll_last.
    reflexivity.
Qed.

Fixpoint list_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  : list A
  := match n,l with
    | 0,_ => l
    | _,[] => []
    | S n, a :: l => list_suffix l n
    end.

Lemma list_suffix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_suffix l n) = list_suffix (List.map f l) n
  .
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl.
  apply IHn.
Qed.

Fixpoint list_prefix
  {A : Type}
  (l : list A)
  (n : nat)
  : list A
  := match n,l with
    | 0,_ => []
    | _,[] => []
    | S n, a :: l => a :: list_prefix l n
    end.

Lemma list_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_prefix l n) = list_prefix (List.map f l) n
  .
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma list_prefix_length
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlen : n <= length l)
  : length (list_prefix l n) = n
  .
Proof.
  generalize dependent l. induction n; intros [|a l] Hlen; try reflexivity.
  - inversion Hlen.
  - simpl in *. f_equal. apply le_S_n in Hlen.
    apply IHn; assumption.
Qed.

Lemma list_prefix_prefix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn: n1 <= n2)
  : list_prefix (list_prefix l n2) n1 = list_prefix l n1
  .
Proof.
  generalize dependent n1. generalize dependent n2.
  induction l; intros [|n2] [|n1] Hn; try reflexivity.
  - inversion Hn.
  - simpl. f_equal. apply IHl. apply le_S_n.  assumption.
Qed.

Lemma list_prefix_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  : list_prefix l n ++ list_suffix l n = l
  .
  Proof.
   generalize dependent n. induction l; intros [|n]; try reflexivity.
   simpl.
   f_equal. apply IHl.
  Qed.

Definition list_segment
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  := list_suffix (list_prefix l n2) n1.

Lemma list_prefix_segment_suffix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : list_prefix l n1 ++ list_segment l n1 n2 ++ list_suffix l n2 = l
  .
Proof.
  rewrite <- (list_prefix_suffix l n2) at 4.
  rewrite app_assoc.
  f_equal.
  unfold list_segment.
  rewrite <- (list_prefix_suffix (list_prefix l n2) n1) at 2.
  f_equal.
  symmetry.
  apply list_prefix_prefix.
  assumption.
Qed.

Lemma stream_prefix_prefix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn: n1 <= n2)
  : list_prefix (stream_prefix l n2) n1 = stream_prefix l n1
  .
Proof.
  generalize dependent n2.
  generalize dependent l.
  induction n1; intros [a l]; intros [|n2] Hn; try reflexivity.
  - inversion Hn.
  - simpl. f_equal. apply IHn1. apply le_S_n.  assumption.
Qed.

Definition stream_segment
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : list A
  := list_suffix (stream_prefix l n2) n1
  .

Lemma stream_prefix_segment_suffix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : EqSt
   (stream_app
   ((stream_prefix l n1)
     ++
    (stream_segment l n1 n2)
   )
    (stream_suffix l n2)
    )
    l
  .
Proof.
  rewrite <- (stream_prefix_suffix l n2) at 4.
  apply stream_app_f_equal; try apply EqSt_reflex.
  unfold stream_segment.
  rewrite <- (list_prefix_suffix (stream_prefix l n2) n1) at 2.
  f_equal.
  symmetry.
  apply stream_prefix_prefix.
  assumption.
Qed.

Lemma stream_prefix_nth
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  (Hi : i < n)  
  : nth_error (stream_prefix s n) i = Some (Str_nth i s)
  .
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - inversion Hi.
  - simpl.
    apply lt_S_n in Hi.
    specialize (IHi s n Hi).
    rewrite IHi.
    reflexivity.
Qed.

Lemma list_prefix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : i < n)  
  : nth_error (list_prefix s n) i = nth_error s i
  .
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [|a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - inversion Hi.
  - simpl.
    apply lt_S_n in Hi.
    specialize (IHi s n Hi).
    rewrite IHi.
    reflexivity.
Qed.

Lemma nth_error_length
  {A : Type}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error l n = Some a)
  : S n <= length l
  .
Proof.
  generalize dependent a. generalize dependent l.
  induction n; intros [|a l] b Hnth; simpl.
  - inversion Hnth.
  - apply le_n_S. apply le_0_n.
  - inversion Hnth. 
  - simpl in Hnth. apply le_n_S.
    specialize (IHn l b Hnth). assumption.
Qed.

Lemma list_prefix_nth_last
  {A : Type}
  (l : list A)
  (n : nat)
  (nth : A)
  (Hnth : nth_error l n = Some nth)
  (_last : A)
  : nth = last (list_prefix l (S n)) _last
  .
Proof.
  specialize (nth_error_length l n nth Hnth); intro Hlen.
  specialize (list_prefix_length l (S n) Hlen); intro Hpref_len.
  symmetry in Hpref_len.
  specialize (list_prefix_nth l (S n) n); intro Hpref.
  rewrite <- Hpref in Hnth.
  - specialize (nth_error_last (list_prefix l (S n)) n Hpref_len _last); intro Hlast.
    rewrite Hlast in Hnth. inversion Hnth.
    reflexivity.
  - constructor.
Qed.

Lemma stream_prefix_nth_last
  {A : Type}
  (l : Stream A)
  (n : nat)
  (_last : A)
  : last (stream_prefix l (S n)) _last = Str_nth n l
  .
Proof.
  specialize (nth_error_last (stream_prefix l (S n)) n); intro Hlast.
  specialize (stream_prefix_length l (S n)); intro Hpref_len.
  symmetry in Hpref_len.
  specialize (Hlast Hpref_len _last).
  specialize (stream_prefix_nth l (S n) n); intro Hnth.
  assert (Hlt : n < S n) by constructor.
  specialize (Hnth Hlt).
  rewrite Hnth in Hlast.
  simpl.
  inversion Hlast.
  reflexivity.
Qed.
  
Lemma list_suffix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : n <= i)  
  : nth_error (list_suffix s n) (i - n) = nth_error s i
  .
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [|a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - simpl. apply nth_error_None. apply le_0_n.
  - apply le_S_n in Hi.
    simpl.
    apply IHi.
    assumption.
Qed.

Lemma list_suffix_last
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlt : i < length l)
  (_default : A)
  : last (list_suffix l i) _default  = last l _default
  .
Proof.
  generalize dependent l. induction i; intros [|a l] Hlt
  ; try reflexivity.
  simpl in Hlt. apply lt_S_n in Hlt.
  specialize (IHi l Hlt).
  rewrite unroll_last. simpl.
  rewrite IHi.
  destruct l.
  - inversion Hlt.
  - rewrite unroll_last. rewrite unroll_last. reflexivity.
Qed.

Lemma list_suffix_last_default
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlast : i = length l)
  (_default : A)
  : last (list_suffix l i) _default  = _default
  .
Proof.
  generalize dependent l. induction i; intros [|a l] Hlast
  ; try reflexivity.
  - inversion Hlast.
  - simpl in Hlast. inversion Hlast.
  specialize (IHi l H0).
  simpl. subst.
  assumption.
Qed.

Lemma list_segment_nth
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  (i : nat)
  (Hi1 : n1 <= i)
  (Hi2 : i < n2)
  : nth_error (list_segment l n1 n2) (i - n1) = nth_error l i.
Proof.
  unfold list_segment.
  rewrite list_suffix_nth; try assumption.
  apply list_prefix_nth.
  assumption.
Qed.

Lemma stream_segment_nth
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  (i : nat)
  (Hi1 : n1 <= i)
  (Hi2 : i < n2)
  : nth_error (stream_segment l n1 n2) (i - n1) = Some (Str_nth i l).
Proof.
  unfold stream_segment.
  rewrite list_suffix_nth; try assumption.
  apply stream_prefix_nth.
  assumption.
Qed.

Lemma nth_error_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  generalize dependent n.
  induction l; intros [|n]; try reflexivity; simpl.
  apply IHl.
Qed.
  
Lemma forall_finite
  {index : Type}
  {index_listing : list index}
  (Hfinite_index : Full index_listing)
  (P : index -> Prop)
  : (forall n : index, P n) <-> Forall P index_listing.
Proof.
  split; intros.
  - apply Forall_forall; intros. apply H.
  - rewrite Forall_forall in H.
    apply H. apply Hfinite_index.
Qed.

Lemma exists_finite
  {index : Type}
  {index_listing : list index}
  (Hfinite_index : Full index_listing)
  (P : index -> Prop)
  : (exists n : index, P n) <-> List.Exists P index_listing.
Proof.
  split; intros.
  - apply Exists_exists; intros.
    destruct H as [n H].
    exists n.
    split; try assumption.
    apply Hfinite_index.  
  - rewrite Exists_exists in H.
    destruct H as [n [_ H]].
    exists n. assumption.
Qed.

Lemma Exists_dec
  {A : Type}
  (P : A -> Prop)
  (l : list A)
  (P_dec : forall a : A, {P a} + {~ P a})
  : {List.Exists P l} + {~ List.Exists P l}
  .
Proof.
  induction l.
  - right. intro. inversion H.
  - specialize (P_dec a).
    destruct P_dec as [Pa | Pna].
    + left. left. assumption.
    + destruct IHl as [Pl | Pnl] .
      * left. right. assumption.
      * right. intro. inversion H; subst; contradiction.
Qed.

Lemma Forall_dec
  {A : Type}
  (P : A -> Prop)
  (l : list A)
  (P_dec : forall a : A, {P a} + {~ P a})
  : {List.Forall P l} + {~ List.Forall P l}
  .
Proof.
  induction l.
  - left. constructor.
  - specialize (P_dec a).
    destruct P_dec as [Pa | Pna].
    + destruct IHl as [Pl | Pnl] .
      * left. constructor;  assumption.
      * right. intro. inversion H; subst; contradiction.
    + right. intro. inversion H; contradiction.
Qed.

Definition map_option
  {A B : Type}
  (f : A -> option B)
  : list A -> list B
  := fold_right
      (fun x lb =>
        match f x with
        | None => lb
        | Some b => b :: lb
        end
      )
      []
  .

Lemma in_map_option
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (b : B)
  : In b (map_option f l) <-> exists a : A, In a l /\ f a = Some b.
Proof.
  split.
  - intro Hin.
    induction l; try inversion Hin.
    simpl in Hin. destruct (f a) eqn:Hfa.
    + destruct Hin as [Heq | Hin]; subst.
      * exists a.
        split; try assumption.
        left. reflexivity.
      * specialize (IHl Hin). destruct IHl as [a' [Hin' Hfa']].
        exists a'. split; try assumption.
        right. assumption.
    + specialize (IHl Hin). destruct IHl as [a' [Hin' Hfa']].
      exists a'. split; try assumption.
      right. assumption.
  - induction l; intros [a' [Hin' Hfa']]; try inversion Hin'; subst; clear Hin'.
    + simpl. rewrite Hfa'. left. reflexivity.
    + simpl. destruct (f a) eqn:Hfa.
      * right. apply IHl. exists a'. split; try assumption.
      * apply IHl. exists a'. split; try assumption.
Qed.
