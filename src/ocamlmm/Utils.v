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

