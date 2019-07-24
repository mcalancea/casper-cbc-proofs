Require Import Reals Bool Relations RelationClasses List ListSet.
Import ListNotations.

Tactic Notation "spec" hyp(H) := 
  match type of H with ?a -> _ => 
  let H1 := fresh in (assert (H1: a); 
  [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) := 
  (generalize (H a); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) := 
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) := 
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) := 
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) := 
  (generalize (H a b c d e); clear H; intro H).

(** Logic library **)
Lemma mirror_reflect: forall X (f : X -> bool) (P : X -> Prop),
  (forall x : X, f x = true <-> P x) ->
  (forall x : X, f x = false <-> ~P x).
Proof.
  split; repeat intro.
  + rewrite <- H in H1. rewrite H0 in H1. discriminate.
  + specialize (H x). destruct (f x). 
    exfalso. apply H0. rewrite <- H. reflexivity.
    reflexivity.
Qed.

Lemma eq_dec_if_true {A B: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall (x y : A) (t e : B),
  x = y -> (if eq_dec x y then t else e) = t.
Proof.
  intros. destruct (eq_dec x y) eqn:Hcmp; try reflexivity.
  exfalso. apply n; apply H.
Qed.


Lemma eq_dec_if_false {A B: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall (x y : A) (t e : B),
  x <> y -> (if eq_dec x y then t else e) = e.
Proof.
  intros. destruct (eq_dec x y) eqn:Hcmp; try reflexivity.
  exfalso. apply H; assumption.
Qed.

Class TotalOrder {A} (lt : relation A) : Prop :=
   totality : forall c1 c2, c1 = c2 \/ lt c1 c2 \/ lt c2 c1.

Class Injective {A B} (f : A -> B) : Prop :=
  injective : forall x y, f x = f y <-> x = y.

Class Commutative {A B : Type} (f : A -> A -> B) :=
  commutative : forall a1 a2, f a1 a2 = f a2 a1. 

Class Decidable {A} (r : A -> Prop) :=
  dec : forall (a : A), r a \/ ~ r a. 

Class PredicateFunction {A} (r : A -> Prop) (r_fn : A -> bool) : Prop :=
  {
    equiv : forall a, r a <-> r_fn a = true;
    predicate_function_dec :> Decidable r;
  }.

Definition predicate_not {A} (p : A -> Prop) : A -> Prop :=
  fun a => ~ p a.

Lemma predicate_function_neg {A} `{PredicateFunction A} : 
  forall a, ~ r a <-> r_fn a = false.
Proof.
  intro a; split; intros.
  apply not_true_iff_false. intro Hnot.
  apply equiv in Hnot. contradiction.
  intro Hnot. apply not_true_iff_false in H0.
  apply H0. apply (equiv a). assumption.
Qed.

Class PredicateFunction2 {A B} (r : A -> B -> Prop) (r_fn : A -> B -> bool) : Prop :=
  predicate_function2 : forall a b, r a b <-> r_fn a b = true.

Lemma predicate_function2_neg : forall A B (r : A -> B -> Prop) (r_fn : A -> B -> bool),
  PredicateFunction2 r r_fn ->
  forall a b, ~ r a b <-> r_fn a b = false.
Proof.  intros. rewrite (H a b).   apply not_true_iff_false. Qed.

Lemma predicate_function2_decidable : forall A B (r : A -> B -> Prop) (r_fn : A -> B -> bool),
  PredicateFunction2 r r_fn ->
  forall a b, r a b \/ ~r a b.
Proof.
  intros. destruct (r_fn a b) eqn:Hr.
  - left. apply H. assumption.
  - right. apply (predicate_function2_neg _ _ _ _ H). assumption.
Qed.

(* Reflexivity of comparison operators *) 
Class CompareReflexive {A} (compare : A -> A -> comparison) : Prop :=
    compare_eq : forall x y, compare x y = Eq <-> x = y.

(* About reflexive comparison operators *) 
Lemma compare_eq_refl {A} `{CompareReflexive A} : 
  forall x, compare x x = Eq.
Proof. intros; now apply H. Qed. 

Lemma compare_eq_lt {A} `{CompareReflexive A} : 
  forall x, ~ compare x x = Lt.
Proof. 
  intros x Hnot. 
  assert (compare x x = Eq) by apply compare_eq_refl.
  rewrite Hnot in H0; discriminate. 
Qed.

Lemma compare_lt_neq {A} `{CompareReflexive A} :
  forall x y, compare x y = Lt -> x <> y.
Proof. 
  intros x y Hcomp Hnot.
  subst. now apply (compare_eq_lt y).  
Qed.

Lemma compare_eq_gt {A} `{CompareReflexive A} :
  forall x, ~ compare x x = Gt.
Proof. 
  intros x Hnot. 
  assert (compare x x = Eq) by apply compare_eq_refl.
  rewrite Hnot in H0; discriminate.
Qed. 

Lemma compare_gt_neq {A} `{CompareReflexive A} :
  forall x y, compare x y = Gt -> x <> y.
Proof. 
  intros x y H_comp H_not.
  subst. now apply compare_eq_gt in H_comp.
Qed.

(* Transitivity of comparison operators *)
Class CompareTransitive {A} (compare : A -> A -> comparison) : Prop :=
    compare_transitive : forall x y z comp, compare x y = comp ->
                                       compare y z = comp ->
                                       compare x z = comp.

(* Strict-orderedness of comparison operators *) 
Class CompareStrictOrder {A} (compare : A -> A -> comparison) : Prop :=
  {
    StrictOrder_Reflexive :> CompareReflexive compare;
    StrictOrder_Transitive :> CompareTransitive compare;
  }.

(* Strictly-ordered comparisons give decidable equality *)
Lemma compare_eq_dec {A} `{CompareStrictOrder A} :
  forall x y : A, {x = y} + {x <> y}.
Proof.
  intros;
  destruct (compare x y) eqn:Hxy;  
    (left; apply StrictOrder_Reflexive; assumption)
    || (right; intro; subst; [now apply compare_eq_lt in Hxy || now apply compare_eq_gt in Hxy]).
Qed.

Definition eq_bool {X} `{CompareStrictOrder X} (x y : X) : bool :=
  match compare_eq_dec x y with
  | left _ => true
  | right _ => false
  end.

(* Asymmetry of comparison operators *)
Class CompareAsymmetric {A} (compare : A -> A -> comparison) : Prop :=
    compare_asymmetric : forall x y, compare x y = Lt <-> compare y x = Gt.

(* Strictly-ordered comparisons give asymmetry *)
Lemma compare_asymmetric_intro {A} `{CompareStrictOrder A} :
  CompareAsymmetric compare.
Proof.
  intros. destruct H as [R TR]. intros; split; intros.
  - destruct (compare y x) eqn:Hyx; try reflexivity; exfalso.
    + apply R in Hyx; subst. now apply compare_eq_lt in H.
    + apply (TR _ _ _ _ Hyx) in H. now apply compare_eq_lt in H. 
  - destruct (compare x y) eqn:Hyx; try reflexivity; exfalso.
    + apply R in Hyx; subst. now apply compare_eq_gt in H.  
    + apply (TR _ _ _ _ Hyx) in H. now apply compare_eq_gt in H.  
Qed.

Instance CompareStrictOrder_Asymmetric {A} (compare : A -> A -> comparison) `{CompareStrictOrder A compare} : CompareAsymmetric compare.
apply compare_asymmetric_intro. 
Defined.

(* Defining a compare_lt predicate from a compare operator *) 
Definition compare_lt {A} (compare : A -> A -> comparison) (x y : A) : Prop :=
  compare x y = Lt.

(* A series of properties about compare_lt *) 
Lemma compare_lt_irreflexive {A} `{CompareReflexive A} :
  Irreflexive (compare_lt compare). 
Proof.
  intros x Hlt. 
  assert (compare x x = Eq) by apply compare_eq_refl.
  rewrite Hlt in H0; discriminate. 
Qed.

Lemma compare_lt_transitive {A} `{CompareTransitive A} :
  Transitive (compare_lt compare).
Proof.
  intros x y z Hxy Hyz; now apply (H _ _ _ _ Hxy Hyz). 
Qed.

Lemma compare_lt_strict_order {A} `{CompareStrictOrder A} :
  StrictOrder (compare_lt compare).
Proof.
  destruct H as [R T].
  split.
  - now apply compare_lt_irreflexive.
  - now apply compare_lt_transitive.
Qed.

Lemma compare_lt_asymmetric {A} `{CompareStrictOrder A} :
  Asymmetric (compare_lt compare).
Proof.
  intros.
  destruct H as [IR TR].
  intros x y Hxy Hyx. apply (TR _ _ _ _ Hxy) in Hyx.
  assert (compare x x = Eq) by (apply compare_eq; reflexivity).
  rewrite Hyx in H; discriminate. 
Qed.

Lemma compare_lt_total_order {A} `{CompareStrictOrder A} :
  TotalOrder (compare_lt compare).
Proof.
  intros x y.
  assert (CSO := H).
  destruct H as [R TR].
  destruct (compare x y) eqn:Hcmp.
  - apply R in Hcmp. left. assumption.
  - right. left. assumption. 
  - right. right. now apply compare_asymmetric_intro.
Qed.

(* We can easily obtain inhabitants of above Typeclasses using Program Definitions, for instance : *) 
Program Definition make_compare_lt_asymmetric {A} `{CompareStrictOrder A} : Asymmetric (compare_lt compare).
exact compare_lt_asymmetric. 
Defined.

(* A generic type class for inhabited types with a strictly ordered comparison operator *) 
Class StrictlyComparable (X : Type) : Type :=
   {
     inhabited : exists (x : X), True;
     compare : X -> X -> comparison;
     compare_strictorder :> CompareStrictOrder compare;
    }.

(* Composing StrictlyComparable types *)
(* Constructing the compare function *)
Definition compare_compose (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y} : (X * Y) -> (X * Y) -> comparison :=
  fun p1 p2 =>
    match p1, p2 with
    | (x1, y1), (x2, y2) => match compare x1 x2 with
                           | Eq => match compare y1 y2 with
                                  | Eq => Eq
                                  | _ => compare y1 y2
                                  end
                           | _ => compare x1 x2
                           end
    end.

(* Constructing the inhabited proof *) 
Lemma inhabited_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} :
  exists (p : X * Y), True.
Proof.
  destruct (@inhabited X) as [x _]. assumption. 
  destruct (@inhabited Y) as [y _]. assumption.
  exists (x, y). 
  auto.
Qed.

(* Constructing the strictorder proof *)
Lemma reflexive_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : CompareReflexive (compare_compose X Y). 
Proof.
  intros (x1, y1) (x2, y2). 
  split; intros.
  simpl in H1.
  destruct (compare x1 x2) eqn:H_x;
    destruct (compare y1 y2) eqn: H_y;
    try discriminate.
  apply StrictOrder_Reflexive in H_x;
    apply StrictOrder_Reflexive in H_y.
  subst; reflexivity.
  inversion H1; subst.
  simpl; do 2 rewrite compare_eq_refl; reflexivity.
Qed. 

Lemma compare_compose_lt {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : forall (x1 x2 : X) (y1 y2 : Y) (c : comparison), 
  compare_compose X Y (x1, y1) (x2, y2) = c ->
  compare x1 x2 = c \/
  x1 = x2 /\ compare y1 y2 = c. 
Proof.             
  intros x1 x2 y1 y2 c H_12. 
  simpl in H_12.
  destruct (compare x1 x2) eqn:H_x; try (left; assumption). 
  right. split. now apply StrictOrder_Reflexive in H_x.
  destruct (compare y1 y2) eqn:H_y; try discriminate; assumption.
Qed.

Lemma transitive_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : CompareTransitive (compare_compose X Y).
Proof.
  intros (x1, y1) (x2, y2) (x3, y3) comp H12 H23.
  destruct comp eqn:H_comp; try  
  (apply reflexive_compose;
   apply reflexive_compose in H12;
     apply reflexive_compose in H23;
     inversion H12; inversion H23; subst; reflexivity).
  - rewrite <- H_comp in *;
    assert (H_useful := compare_compose_lt x1 x2 y1 y2 comp H12);
    assert (H_useful' := compare_compose_lt x2 x3 y2 y3 comp H23).
    destruct H_useful as [left | right]; 
    destruct H_useful' as [left' | right'].
    assert (compare x1 x3 = comp) by (apply (StrictOrder_Transitive x1 x2 x3 comp left left'); assumption).
    simpl; rewrite H1; subst; reflexivity.
    destruct right'; subst.
    simpl; rewrite left; reflexivity.
    destruct right; subst.
    simpl; rewrite left'; reflexivity.
    destruct right; destruct right'; subst.
    assert (compare y1 y3 = Lt) by (apply (StrictOrder_Transitive y1 y2 y3 Lt); assumption). 
    simpl; rewrite compare_eq_refl; simpl in H12; rewrite H1; reflexivity.
  - rewrite <- H_comp in *;
    assert (H_useful := compare_compose_lt x1 x2 y1 y2 comp H12);
    assert (H_useful' := compare_compose_lt x2 x3 y2 y3 comp H23).
    destruct H_useful as [left | right]; 
    destruct H_useful' as [left' | right'].
    assert (compare x1 x3 = comp) by (apply (StrictOrder_Transitive x1 x2 x3 comp left left'); assumption).
    simpl; rewrite H1; subst; reflexivity.
    destruct right'; subst.
    simpl; rewrite left; reflexivity.
    destruct right; subst.
    simpl; rewrite left'; reflexivity.
    destruct right; destruct right'; subst.
    assert (compare y1 y3 = Gt) by (apply (StrictOrder_Transitive y1 y2 y3 Gt); assumption). 
    simpl; rewrite compare_eq_refl; simpl in H12; rewrite H1; reflexivity.
Qed.

Lemma strictorder_compose {X Y : Type} `{StrictlyComparable X} `{StrictlyComparable Y} : CompareStrictOrder (compare_compose X Y).
Proof.
  split; exact reflexive_compose || exact transitive_compose.
Qed.

(* Now we can have the following for free : *) 
Instance ComposeStrictlyComparable (X Y : Type) `{StrictlyComparable X} `{StrictlyComparable Y} : StrictlyComparable (X * Y) :=
  { inhabited := inhabited_compose;
    compare := compare_compose X Y;
    compare_strictorder := strictorder_compose;
  }.

Instance TripleStrictlyComparable (X Y Z : Type) `{StrictlyComparable X} `{StrictlyComparable Y} `{StrictlyComparable Z} : StrictlyComparable (X * Y * Z) :=
  { inhabited := inhabited_compose;
    compare := compare_compose (X * Y) Z;
    compare_strictorder := strictorder_compose;
  }.

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



