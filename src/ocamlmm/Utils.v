Require Import Classical Peano_dec.
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

Ltac remove_emptiness :=
  repeat (rewrite set_inter_empty_r || rewrite set_inter_empty_l ||
          rewrite set_union_empty_r || rewrite set_union_empty_l). 
