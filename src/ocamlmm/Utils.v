Require Import Classical Peano_dec.
From PromisingLib Require Import Basic Loc.
From hahn Require Import Hahn.
Set Implicit Arguments.


Lemma inclusion_minus {A: Type} (s u m: A -> Prop):
  s ⊆₁ u \₁ m <-> s ⊆₁ u /\ s ∩₁ m ⊆₁ ∅.
Proof.
  (*link to similar lemma here*)
Admitted. 

Lemma OPT_VAL: forall {A: Type} (opt: option A), opt <> None <-> exists o, Some o = opt.
Proof. 
  intros. destruct opt eqn:v. 
  - red. split; intros. 
    + eexists. eauto.
    + discriminate.
  - red. split; intros.
    + intuition.
    + destruct H. discriminate H.  
Qed.  


Lemma empty_inter_minus_same {A: Type} (X Y: A -> Prop):
  X ∩₁ Y ≡₁ ∅ -> X \₁ Y ≡₁ X.
Proof. 
  ins. red. split; [basic_solver| ].
  red. ins.
  red in H. desc.
  red. split; auto.
  red in H. specialize (H x).
  red. ins. apply H. basic_solver. 
Qed.

Lemma same_relation_exp_iff {A: Type} (r r': relation A):
  r ≡ r' <-> (forall x y, r x y <-> r' x y).
Proof.
  red. split.
  { apply same_relation_exp. }
  ins. red. split.
  all: red; ins; apply H; auto.
Qed.  

Lemma set_equiv_exp_iff {A : Type} (s s' : A -> Prop):
  s ≡₁ s' <-> forall x : A, s x <-> s' x.
Proof.
  red. split; [apply set_equiv_exp| ].
  ins. red. split.
  all: red; ins; apply H; auto.
Qed. 

Lemma seq_eqv_lr_l {A: Type} (d1 d2: A -> Prop) r:
  r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘ -> r ≡ ⦗d1⦘ ⨾ r.
Proof. ins. rewrite H. basic_solver. Qed. 

Lemma seq_eqv_lr_r {A: Type} (d1 d2: A -> Prop) r:
  r ≡ ⦗d1⦘ ⨾ r ⨾ ⦗d2⦘ -> r ≡ r ⨾ ⦗d2⦘.
Proof. ins. rewrite H. basic_solver. Qed.

Lemma inter_subset_helper {A: Type} (S S1 S2: A -> Prop):
  (forall x (Sx: S x), S1 x <-> S2 x) -> S ∩₁ S1 ≡₁ S ∩₁ S2.
Proof.
  ins. apply set_equiv_exp_iff. ins. specialize (H x).
  unfold set_inter. 
  split; ins; desc; split; intuition.
Qed.

Lemma set_finite_alt {A: Type} (S: A -> Prop) (FIN: set_finite S):
  exists findom, forall x, S x <-> In x findom.
Proof.
  destruct FIN as [lst FIN].
  exists (filterP S lst). ins. split.
  { ins. apply in_filterP_iff. split; auto. }
  ins. apply in_filterP_iff in H. desc. auto. 
Qed.

Lemma bunion_more_alt: forall {A B : Type} (x y : A -> Prop),
    x ≡₁ y ->
    forall (x0 y0 : A -> relation B), (forall a, x0 a ≡ y0 a) -> (⋃x ∈ x, x0 x) ≡ (⋃x ∈ y, y0 x).
Proof.
  ins. apply same_relation_exp_iff. ins. red. splits.
  { unfold bunion. ins. desc. exists a. splits.
    { apply H. auto. }
    apply H0. auto. }
  { unfold bunion. ins. desc. exists a. splits. 
    { apply H. auto. }
    apply H0. auto. }
Qed.

    
Lemma IN_SET_UNION {A: Type} (l1 l2: list A):
  (fun x => In x (l1 ++ l2)) ≡₁ (fun x => In x l1) ∪₁ (fun x => In x l2).
Proof. 
  ins. apply set_equiv_exp_iff. ins. split.
  { ins. red. apply in_app_or. auto. }
  ins. red in H. apply in_or_app. auto.
Qed.

Lemma eqv_rel_more_inv {A: Type} (S1 S2: A -> Prop) (EQV_REL: ⦗S1⦘ ≡ ⦗S2⦘):
  S1 ≡₁ S2.
Proof. 
  apply set_equiv_exp_iff. ins.
  apply (same_relation_exp) with (x := x) (y := x) in EQV_REL.
  unfold eqv_rel in EQV_REL. red in EQV_REL. desc. 
  red. splits; desc; intuition.
Qed.

Lemma unique_restr {A: Type} x y (r: relation A) (Rxy: r x y):
  ⦗eq x⦘ ⨾ r ⨾ ⦗eq y⦘ ≡ singl_rel x y.
Proof.
  ins. rewrite seq_eqv_lr. split.
  { red. ins. desc. red. splits; auto. }
  red. ins. red in H. desc. splits; vauto.
Qed.

Lemma singl_rel_restr {A: Type} (x y: A):
  singl_rel x y ≡ ⦗eq x⦘ ⨾ singl_rel x y ⨾ ⦗eq y⦘. 
Proof. ins. basic_solver. Qed. 

Lemma rel_endpoints_dom {A: Type} (D C EL ER : A -> Prop) r (DOM: r ≡ ⦗D⦘ ⨾ r ⨾ ⦗C⦘):
  ⦗EL⦘ ⨾ r ⨾ ⦗ER⦘ ≡ ⦗EL ∩₁ D⦘ ⨾ r ⨾ ⦗ER ∩₁ C⦘.
Proof.
  rewrite set_interC with (s' := C). 
  do 2 rewrite id_inter. rewrite !seqA.
  seq_rewrite <- DOM. basic_solver.
Qed.

Lemma seq_compl_helper {A: Type} (r: relation A) (S: A -> Prop):
  r ⨾ ⦗set_compl S⦘ ≡ r \ set_full × S.
Proof.
  rewrite <- (seq_id_l r) at 1.
  rewrite seqA. 
  pose proof (seq_eqv_lr r (fun _ : A => True) (set_compl S)).
  seq_rewrite H. 
  apply same_relation_exp_iff. ins.
  split.
  { ins. desc. red. splits; auto. red. basic_solver. }
  ins. red in H0. desc. splits; auto.
  red. red. red in H1. 
  ins. apply H1. unfold cross_rel. split; basic_solver. 
Qed. 

Lemma MINUS_DISTR_L {A: Type} (r: relation A) (S1 S2: A -> Prop):
  ⦗S1 \₁ S2⦘ ⨾ r ≡ ⦗S1⦘ ⨾ r \ ⦗S2⦘ ⨾ r.
Proof. 
  ins. red. split; [| basic_solver].
  red. ins. red. apply seq_eqv_l in H. desc.
  red in H. desc.
  split; [basic_solver |].
  red. ins. apply seq_eqv_l in H2. basic_solver.
Qed. 

Lemma MINUS_DISTR_R {A: Type} (r: relation A) (S1 S2: A -> Prop):
  r ⨾ ⦗S1 \₁ S2⦘ ≡ r ⨾ ⦗S1⦘ \ r ⨾ ⦗S2⦘.
Proof. 
  ins. red. split; [| basic_solver].            
  red. ins. red. apply seq_eqv_r in H. desc.
  red in H0. desc.
  split; [basic_solver |].
  red. ins. apply seq_eqv_r in H2. basic_solver.
Qed. 

Lemma MINUS_GROUP {A: Type} (r1 r2 r3: relation A):
  (r1 \ r2) \ r3 ≡ r1 \ (r2 ∪ r3).
Proof. 
  ins. red. split; [| basic_solver].
  red. ins. red. red in H. desc. red in H. desc.
  split; auto. red. ins. red in H2. basic_solver.
Qed.

Lemma SUPSET_RESTR {A: Type} (r1 r2: relation A) S (INCL: r1 ⊆ r2) (RESTR: r2 ≡ ⦗S⦘ ⨾ r2 ⨾ ⦗S⦘):
  r1 ≡ ⦗S⦘ ⨾ r1 ⨾ ⦗S⦘. 
Proof.
  ins. split; [| basic_solver].
  red. ins. apply seq_eqv_lr.
  red in RESTR. desc. red in RESTR.
  red in INCL. 
  pose proof (INCL x y H) as R2.
  specialize (RESTR x y R2). apply seq_eqv_lr in RESTR. desc.
  splits; auto.
Qed.

Lemma RESTR_SEQ  {A: Type} (r1 r2: relation A) (D: A -> Prop):
  restr_rel D r1 ⨾ restr_rel D r2 ⊆ restr_rel D (r1 ⨾ r2). 
Proof. ins. basic_solver. Qed.


Lemma find_iff_in {A: Type} (M: IdentMap.t A) k: 
  IdentMap.In k M <-> exists elt, Some elt = IdentMap.find k M. 
Proof.
  pose proof (@UsualFMapPositive.UsualPositiveMap.Facts.in_find_iff _ M k).
  pose proof OPT_VAL (IdentMap.find k M).
  eapply iff_stepl; [eapply H0 | symmetry; eauto]. 
Qed.

Ltac remove_emptiness :=
  repeat (rewrite set_inter_empty_r || rewrite set_inter_empty_l ||
          rewrite set_union_empty_r || rewrite set_union_empty_l ||
          rewrite union_false_r || rewrite union_false_l ||
          rewrite inter_false_r || rewrite inter_false_l ||
          rewrite seq_false_r || rewrite seq_false_l || rewrite eqv_empty). 