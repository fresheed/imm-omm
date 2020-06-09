Require Import List.
From hahn Require Import Hahn.
Require Import Omega.
Require Import Utils.
From PromisingLib Require Import Basic Loc.
Set Implicit Arguments.


Section ListHelpersTemp.
  (******************************************************************************)
  (** The following lemmas are proved in Coq 8.10 **)
  (** Proofs have been (partially) copied from it **)
  (******************************************************************************)
  
  Variable A : Type.

  Lemma skipn_firstn_comm : forall m n (l: list A),
      skipn m (firstn n l) = firstn (n - m) (skipn m l).
  Proof.
    now induction m; intros [] []; simpl; rewrite ?firstn_nil.
  Qed.


  Lemma firstn_skipn_comm : forall m n (l: list A),
      firstn m (skipn n l) = skipn n (firstn (n + m) l).
  Proof.
    now intros m; induction n; intros []; simpl; destruct m.
  Qed.

  Lemma skipn_app n : forall {A: Type} (l1 l2: list A),
      skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof.
    induction n; auto; intros.
    destruct l1; auto.
    rewrite <- app_comm_cons. simpl.
    auto.
  Qed.

  Lemma skipn_all2 n: forall (l: list A), length l <= n -> skipn n l = nil.
  Proof.
    intros l L%PeanoNat.Nat.sub_0_le; rewrite <- (firstn_all l).
    now rewrite skipn_firstn_comm, L.
  Qed.

End ListHelpersTemp.


Section ListHelpers.
  Variable A: Type. 

  Lemma firstn_ge_incl (l: list A) i j (LE: i <= j):
    firstn j l = firstn i l ++ skipn i (firstn j l).
  Proof. 
    destruct (lt_dec j (length l)) as [LTj | GEj]. 
    2: { rewrite firstn_all2 with (n := j); [| omega].
         symmetry. eapply firstn_skipn. }
    rewrite <- firstn_skipn with (n := i) at 1.
    rewrite firstn_firstn.
    rewrite (NPeano.Nat.min_l _ _ LE). 
    eauto.
  Qed. 
  
  Lemma skipn_firstn_nil (l: list A) i:
    skipn i (firstn i l) = nil.
  Proof.
    generalize dependent l. induction i; vauto. ins. destruct l; auto.
  Qed.     
End ListHelpers. 

Section ListList.
  Variable A: Type. 

  Definition same_struct (ll1 ll2: list (list A)) :=
    Forall2 (fun l1 l2 => length l1 = length l2) ll1 ll2.
  
  Lemma SAME_STRUCT_PREF (ll1 ll2: list (list A)) (SS: same_struct ll1 ll2) i: 
    length (flatten (firstn i ll1)) = length (flatten (firstn i ll2)).
  Proof.
    generalize dependent ll2. generalize dependent i.
    induction ll1.
    { ins. inversion SS. subst. auto. }
    ins. inversion SS. subst.
    destruct i.
    { simpl. auto. }
    simpl. do 2 rewrite length_app. f_equal; auto.  
  Qed. 
    
  Lemma same_struct_refl (ll: list (list A)): same_struct ll ll.
  Proof.
    induction ll.
    { vauto. }
    econstructor; vauto.
  Qed.
  
  Lemma NONEMPTY_PREF (ll: list (list A)) (NE: Forall (fun l => l <> nil) ll)
        i j (SAME_LEN: length (flatten (firstn i ll)) =
                       length (flatten (firstn j ll)))
        (INDEXI: i <= length ll) (INDEXJ: j <= length ll ): 
    i = j.
  Proof.
    generalize dependent i. generalize dependent j.
    induction ll.
    { ins. omega. }
    ins. destruct i, j; [auto | | |]. 
    { simpl in SAME_LEN. rewrite length_app in SAME_LEN.
      inversion NE. subst. destruct a; vauto. }
    { simpl in SAME_LEN. rewrite length_app in SAME_LEN.
      inversion NE. subst. destruct a; vauto. }
    f_equal.
    apply IHll.
    { inversion NE. auto. }
    { apply le_S_n. auto. }
    2: { apply le_S_n. auto. }
    simpl in SAME_LEN. do 2 rewrite length_app in SAME_LEN.
    omega.
  Qed. 
  
  Lemma flatten_split (ll: list (list A)) bi (INDEX: bi < length ll):
    flatten ll = flatten (firstn bi ll) ++ flatten (skipn bi ll).
  Proof. ins. rewrite <- flatten_app. rewrite firstn_skipn. auto. Qed.
   
  Lemma ll_index_shift (ll: list (list A)) i j block
        (ITH: Some block = nth_error ll i) (NE: Forall (fun l => l <> nil) ll)
        (J_BOUND: j <= length ll):
    length (flatten (firstn j ll)) = length (flatten (firstn i ll)) + length block
    <-> j = i + 1.
  Proof.
    split. 
    2: { ins; subst. erewrite first_end; eauto.
         rewrite flatten_app, length_app. simpl. rewrite app_nil_r. auto. }
    intros FLT_SHIFT. 
    destruct (dec_le j i) as [LE | GT].
     { rewrite (firstn_ge_incl ll LE) in FLT_SHIFT.  
       rewrite flatten_app, length_app in FLT_SHIFT.
       cut (length block > 0); [ins; omega |]. 
       apply (proj1 (Forall_forall (fun l => l <> nil) ll)) with (x := block) in NE. 
       { destruct block; vauto. simpl. omega. } 
       eapply nth_error_In. eauto. }
     apply not_le in GT.
     rewrite (@firstn_ge_incl _ ll i j) in FLT_SHIFT; [| omega].
     assert (exists d, j = i + S d). 
     { ins. destruct (j - i) eqn:DIFF. 
       { exists 0. omega. }
       exists n. omega. }
     desc. subst.
     cut (d = 0); [ins; omega|].
     destruct d; auto.
     exfalso. 
     rewrite flatten_app, length_app in FLT_SHIFT.
     apply plus_reg_l in FLT_SHIFT.
     replace (i + S (S d)) with ((i + 1 + d) + 1) in FLT_SHIFT by omega.
     assert (exists block', Some block' = nth_error ll (i + 1 + d)) as [block' BLOCK'].
     { apply OPT_VAL, nth_error_Some. omega. }
     erewrite first_end in FLT_SHIFT; eauto.
     rewrite skipn_app in FLT_SHIFT.
     replace (i - length (firstn (i + 1 + d) ll)) with 0 in FLT_SHIFT.
     2: { rewrite firstn_length_le; omega. }
     rewrite <- firstn_skipn with (l := ll) (n := i + 1) in FLT_SHIFT.
     erewrite first_end in FLT_SHIFT; eauto.
     rewrite <- app_assoc in FLT_SHIFT.
     replace i with (length (firstn i ll)) in FLT_SHIFT at 2.
     2: { apply firstn_length_le. omega. }
     rewrite <- plus_assoc in FLT_SHIFT. 
     rewrite firstn_app_2 in FLT_SHIFT.
     simpl in FLT_SHIFT.
     rewrite skipn_app in FLT_SHIFT.
     replace (length (firstn i ll)) with i in FLT_SHIFT. 
     2: { symmetry. apply firstn_length_le. omega. }
     rewrite skipn_firstn_nil in FLT_SHIFT. 
     rewrite Nat.sub_diag in FLT_SHIFT. simpl in FLT_SHIFT.
     rewrite !flatten_app, !length_app in FLT_SHIFT. simpl in FLT_SHIFT.
     rewrite app_nil_r in FLT_SHIFT.
     cut (length block' <> 0); [ins; omega| ]. 
     pose proof (Forall_forall (fun l : list A => l <> nil) ll).
     cut (block' <> nil).
     { ins. destruct block'; vauto. }
     apply H; auto.  
     eapply nth_error_In. eauto.
  Qed.
     
End ListList. 


Section Forall2Helpers.
  Variable A B: Type.
  
  Lemma Forall2_index (l1: list A) (l2: list B) P
        (FORALL2: Forall2 P l1 l2)
        x y i (XI: Some x = nth_error l1 i) (YI: Some y = nth_error l2 i):
    P x y.
  Proof.
    generalize dependent l2. generalize dependent l1.
    set (T := fun i => forall l1 : list A,
                  Some x = nth_error l1 i ->
                  forall l2 : list B, Forall2 P l1 l2 -> Some y = nth_error l2 i -> P x y).
    eapply (strong_induction T).
    ins. red. ins. unfold T in IH.
    destruct l1; [destruct n; vauto |]. destruct l2; [destruct n; vauto |]. 
    destruct n eqn:N.
    { subst. simpl in *. inversion H. inversion H1. subst.
      inversion H0. auto. }
    subst. simpl in *. eapply IH; eauto.
    inversion H0. auto.
  Qed.

  Lemma Forall2_length (l1: list A) (l2: list B) P
        (FORALL2: Forall2 P l1 l2):
    length l1 = length l2.
  Proof.
    generalize dependent l2. induction l1.
    { ins. inversion FORALL2. auto. }
    ins. inversion FORALL2. subst. simpl. f_equal.
    apply IHl1. auto.
  Qed. 
      
End Forall2Helpers.


Section ForallHelpers.
  Variable A: Type. 
  
  Lemma Forall_index (l: list A) P:
    Forall P l <-> forall x i (XI: Some x = nth_error l i), P x.
  Proof.
    split.
    { intros FORALL x i XI.
      forward eapply (@Forall2_index _ _ l l (fun x _ => P x)); eauto. 
      clear XI. generalize dependent l. intros l. induction l.
      { ins. }
      ins. inversion FORALL. subst. apply Forall2_cons; auto. }
    ins. induction l; auto.    
    apply Forall_cons. split.
    { apply H with (i := 0). auto. }
    apply IHl. ins.
    apply H with (i := S i). simpl. auto. 
  Qed.

End ForallHelpers.   
