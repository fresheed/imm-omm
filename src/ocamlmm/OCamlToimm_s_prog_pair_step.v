(******************************************************************************)
(** * ocaml MM is weaker than IMM_S   *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Omega.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCaml.
Require Import OCamlToimm_s.
Require Import OCamlToimm_s_prog. 
Require Import OCamlToimm_s_prog_compilation. 
Require Import OCamlToimm_s_prog_bounded_properties. 
Require Import Utils.
Require Import ClosuresProperties. 
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import Logic.Decidable. 
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.

Section PairStep.
  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  Notation "'F' G" := (fun a => is_true (is_f G.(lab) a)) (at level 1).
  Notation "'ORlx' G" := (fun a => is_true (is_only_rlx G.(lab) a)) (at level 1).
  Notation "'Sc' G" := (fun a => is_true (is_sc G.(lab) a)) (at level 1). 
  Notation "'Acq' G" := (fun a => is_true (is_acq G.(lab) a)) (at level 1). 
  Notation "'Acqrel' G" := (fun a => is_true (is_acqrel G.(lab) a)) (at level 1). 
  Notation "'R_ex' G" := (fun a => is_true (R_ex G.(lab) a)) (at level 1).
  Notation "'hbo'" := (OCaml.hb). 
  Notation "'same_loc' G" := (same_loc G.(lab)) (at level 1).
  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

  Lemma blockstep_implies_steps bst1 bst2 tid
        (BLOCK_STEPS: (block_step tid)＊ bst1 bst2): 
    (step tid)＊ (bst2st bst1) (bst2st bst2). 
  Proof.
    apply crt_num_steps. apply crt_num_steps in BLOCK_STEPS. desc.
    generalize dependent bst1. generalize dependent bst2. induction n.
    { ins. red in BLOCK_STEPS. desc.
      exists 0. apply steps0. congruence. }
    ins. red in BLOCK_STEPS. destruct BLOCK_STEPS as [bst' [BLOCK_STEPS1 BLOCK_STEPS2]].
    specialize (IHn _ _ BLOCK_STEPS1). destruct IHn as [n' STEPS1].
    red in BLOCK_STEPS2. desc. red in BLOCK_STEPS2. desc. 
    exists (n' + length block).
    forward eapply (steps_split (step tid) n' (length block) _ (bst2st bst1) (bst2st bst2)) as SPLIT; auto. 
    apply SPLIT. exists (bst2st bst'). split; auto.
    Unshelve. auto.
  Qed. 

  Lemma flatten_split {A: Type} (ll: list (list A)) bi (INDEX: bi < length ll):
    flatten ll = flatten (firstn bi ll) ++ flatten (skipn bi ll).
  Proof. ins. rewrite <- flatten_app. rewrite firstn_skipn. auto. Qed.
   
  Lemma near_pc b block d (BLOCK_POS: Some b = nth_error block d)
        bst st (BST2ST: st = bst2st bst)
        (AT_BLOCK: Some block = nth_error (binstrs bst) (bpc bst))
        (BST_NONTERM: bpc bst < length (binstrs bst)):
    Some b = nth_error (instrs st) (pc st + d).
  Proof.
    replace (instrs st) with (flatten (binstrs bst)).
    2: { unfold bst2st in BST2ST. subst. auto. }
    replace (pc st) with (length (flatten (firstn (bpc bst) (binstrs bst)))).
    2: { unfold bst2st in BST2ST. subst. auto. }
    rewrite <- (firstn_skipn (bpc bst) (binstrs bst)) in AT_BLOCK. 
    rewrite nth_error_app2 in AT_BLOCK.
    2: { apply firstn_le_length. }
    rewrite firstn_length_le in AT_BLOCK; [| omega]. 
    rewrite Nat.sub_diag in AT_BLOCK.
    rewrite (@flatten_split _ (binstrs bst) (bpc bst)); [| auto]. 
    rewrite nth_error_app2; [| omega].
    rewrite minus_plus.
    remember (skipn (bpc bst) (binstrs bst)) as ll. 
    assert (forall {A: Type} l (x: A), Some x = nth_error l 0 -> exists l', l = x :: l'). 
    { ins. destruct l; vauto. }
    apply H in AT_BLOCK. desc.
    rewrite AT_BLOCK. simpl.
    rewrite nth_error_app1.
    { cut (exists b, Some b = nth_error block d); auto. 
      apply OPT_VAL. congruence. }
    apply nth_error_Some. congruence. 
  Qed. 

  Lemma reach_with_blocks bst st tid (BST2ST: st = bst2st bst)
        (BLOCK_REACH: (block_step tid)＊ (binit (binstrs bst)) bst):
    exists n_steps, (step tid) ^^ n_steps (init (instrs st)) st.
  Proof. 
    apply crt_num_steps. 
    subst st. 
    replace (init (instrs (bst2st bst))) with (bst2st (binit (binstrs bst))). 
    { apply blockstep_implies_steps. auto. }
    unfold bst2st, init. simpl. auto.
  Qed. 
  
  Definition sim_lab GO GI := forall x : actid, E GO x -> lab GO x = lab GI x.

  Definition extends_with tid d new_lbl st st' :=
    (exists ddata daddr dctrl drmw_dep,
        G st' = add (G st) tid (eindex st + d) new_lbl ddata daddr dctrl drmw_dep) /\
      eindex st' = eindex st + d + 1. 

  Definition extends tid d st st' := exists new_lbl, extends_with tid d new_lbl st st'.       

  Lemma sim_lab_extension k tid sto sti (SBL: same_behavior_local (G sto) (G sti))
        (EI_BOUND: E (G sti) ⊆₁ (fun x : actid => index x < eindex sti))
        (INDEX_EQ: eindex sto = eindex sti)
        sto' sti' (new_lbl: label)
        (OEXTENDS: extends_with tid k new_lbl sto sto')
        (IEXTENDS: (extends tid 0) ^^ (k + 1) sti sti')
        (LAST_LBL: lab (G sti') (ThreadEvent tid (eindex sto + k)) = new_lbl):
    sim_lab (G sto') (G sti').
  Proof.
    unfold sim_lab in *. intros x EGO'x. red in SBL. desc.  
    assert (x = ThreadEvent tid (eindex sto + k) \/ E (G sto) x) as EGOx.
    { red in OEXTENDS. desc. rewrite OEXTENDS in EGO'x.
      unfold add, acts_set in EGO'x. simpl in EGO'x.
      unfold acts_set. intuition. }
    destruct EGOx.
    + rewrite H. 
      red in OEXTENDS. desc. rewrite OEXTENDS.
      unfold add. simpl. rewrite upds. congruence.
    + assert (index x < eindex sto) as NEQ.
      { destruct (Const.lt_decidable (index x) (eindex sto)); auto.
        exfalso. 
        assert (E (G sti) x) as EGIx.
        { red in RESTR_EVENTS. desc.
          red in RESTR_EVENTS. forward eapply (RESTR_EVENTS x); vauto.
          basic_solver. }
        red in EI_BOUND. specialize (EI_BOUND x EGIx).
        omega. }
      red in OEXTENDS. desc. rewrite OEXTENDS. unfold add. simpl.
      rewrite updo.
      2: { red; ins; rewrite H0 in NEQ; simpl in NEQ; omega. }
      assert (forall j (LT: j <= k + 1) stj (EXTI: (extends tid 0) ^^ j sti stj),
                 lab (G stj) x = lab (G sti) x
                 /\ eindex stj = eindex sto + j) as EXT_SAME_LAB. 
      { intros j. induction j.
        { ins. rewrite Nat.add_0_r. red in EXTI. desc. split; congruence. }
        ins. rename stj into stj'.
        red in EXTI. destruct EXTI as [stj [EXT EXT']].
        specialize (IHj (le_Sn_le j (k + 1) LT) stj EXT). desc.  
        replace (lab (G stj') x) with (lab (G stj) x).
        2: { red in EXT'. desc. red in EXT'. desc.
             rewrite EXT'. unfold add. simpl.
             rewrite updo; auto.
             red. ins. rewrite H0 in NEQ. simpl in NEQ.
             omega. }
        rewrite IHj. split; auto.
        red in EXT'. desc. red in EXT'. desc. 
        omega. }
      pose proof (EXT_SAME_LAB (k + 1) (Nat.le_refl (k + 1)) sti' IEXTENDS). desc.
      specialize (SAME_LAB x H). congruence.  
  Qed.    

  Definition same_struct {A: Type} (ll1 ll2: list (list A)) :=
    Forall2 (fun l1 l2 => length l1 = length l2) ll1 ll2.
  
  Lemma SAME_STRUCT_PREF {A: Type} (ll1 ll2: list (list A)) (SS: same_struct ll1 ll2) i: 
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
    
  Lemma NONEMPTY_PREF {A: Type} (ll: list (list A)) (NE: Forall (fun l => l <> []) ll)
        i j (SAME_LEN: length (flatten (firstn i ll)) = length (flatten (firstn j ll))) (INDEXI: i <= length ll) (INDEXJ: j <= length ll ): 
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
  
  Lemma COMPILED_NONEMPTY_weak  PO BPI (COMP: itbc_weak PO BPI):
    Forall (fun l : list Instr.t => l <> []) BPI.
  Proof.
    apply ForallE. intros block BLOCK.
    apply In_nth_error in BLOCK. desc. symmetry in BLOCK. 
    red in COMP. desc.
    assert (exists block0, Some block0 = nth_error BPI0 n) as [block0 BLOCK0].
    { apply OPT_VAL, nth_error_Some.
      replace (length BPI0) with (length BPI).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length. eauto. }
    cut (block0 <> []).
    2: { assert (exists instr, Some instr = nth_error PO n) as [instr INSTR].
         { apply OPT_VAL, nth_error_Some.
           replace (length PO) with (length BPI0).
           { apply nth_error_Some, OPT_VAL. eauto. }
           symmetry. eapply Forall2_length. eauto. }
         pose proof (Forall2_index COMP _ INSTR BLOCK0).
         inversion H; simpl; vauto. }
    ins. red. ins. red in H. apply H.
    apply length_zero_iff_nil. apply length_zero_iff_nil in H0.
    rewrite <- H0.
    pose proof (Forall2_index COMP0 _ BLOCK0 BLOCK). red in H1.
    eapply Forall2_length; eauto.  
  Qed. 
  
  Lemma COMPILED_NONEMPTY  PO BPI (COMP: is_thread_block_compiled PO BPI):
    Forall (fun l : list Instr.t => l <> []) BPI.
  Proof.
    eapply COMPILED_NONEMPTY_weak. eapply itbc_implies_itbcw. eauto.  
  Qed. 
    
  Lemma INSTR_LEXPR_HELPER sto bsti (MM_SIM: mm_similar_states sto bsti)
        sti (BST2ST: sti = bst2st bsti) instr n (INSTR: Some instr = nth_error (instrs sti) n) lexpr (EXPR_OF: lexpr_of lexpr instr):
    RegFile.eval_lexpr (regf sto) lexpr = RegFile.eval_lexpr (regf sti) lexpr.
  Proof. 
    red in MM_SIM. desc.
    eapply eval_instr_lexpr; eauto. 
    { exists (instrs sto). red. unfold is_thread_compiled_with.
      eexists. eauto. }
    { replace (regf sti) with (bregf bsti); vauto. }
    eapply nth_error_In. replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto.
  Qed. 

  Lemma INSTR_EXPR_HELPER sto bsti (MM_SIM: mm_similar_states sto bsti)
        sti (BST2ST: sti = bst2st bsti) instr n (INSTR: Some instr = nth_error (instrs sti) n) expr (EXPR_OF: expr_of expr instr):
    RegFile.eval_expr (regf sto) expr = RegFile.eval_expr (regf sti) expr.
  Proof. 
    red in MM_SIM. desc.
    eapply eval_instr_expr; eauto. 
    { exists (instrs sto). red. unfold is_thread_compiled_with.
      eexists. eauto. }
    { replace (regf sti) with (bregf bsti); vauto. }
    eapply nth_error_In. replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto.
  Qed.
  
  Lemma INSTR_LEXPR_DEPS_HELPER sto bsti (MM_SIM: mm_similar_states sto bsti)
        sti (BST2ST: sti = bst2st bsti) instr n (INSTR: Some instr = nth_error (instrs sti) n) lexpr (EXPR_OF: lexpr_of lexpr instr):
    DepsFile.lexpr_deps (depf sto) lexpr = DepsFile.lexpr_deps (depf sti) lexpr.
  Proof. 
    red in MM_SIM. desc.
    eapply eval_instr_lexpr_deps; eauto. 
    { exists (instrs sto). red. unfold is_thread_compiled_with.
      eexists. eauto. }
    { replace (regf sti) with (bregf bsti); vauto. }
    eapply nth_error_In. replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto.
  Qed.
  
  Lemma INSTR_EXPR_DEPS_HELPER sto bsti (MM_SIM: mm_similar_states sto bsti)
        sti (BST2ST: sti = bst2st bsti) instr n (INSTR: Some instr = nth_error (instrs sti) n) expr (EXPR_OF: expr_of expr instr):
    DepsFile.expr_deps (depf sto) expr = DepsFile.expr_deps (depf sti) expr.
  Proof. 
    red in MM_SIM. desc.
    eapply eval_instr_expr_deps; eauto. 
    { exists (instrs sto). red. unfold is_thread_compiled_with.
      eexists. eauto. }
    { replace (regf sti) with (bregf bsti); vauto. }
    eapply nth_error_In. replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto.
  Qed.
  
  Lemma DIFF_LE x y (LT: x <= y): exists d, y = x + d. 
  Proof.
    ins. destruct (y - x) eqn:DIFF.
    { exists 0. omega. }
    exists (S n). omega. 
  Qed. 

  Lemma firstn_ge_incl {A: Type} (l: list A) i j (LE: i <= j):
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

  Lemma skipn_app n : forall {A: Type} (l1 l2: list A),
      skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. Admitted.
  
  Lemma skipn_firstn_comm : forall {A: Type} m n (l: list A),
      skipn m (firstn n l) = firstn (n - m) (skipn m l).
  Proof. Admitted.

  Lemma skipn_firstn_nil {A: Type} (l: list A) i:
    skipn i (firstn i l) = [].
  Proof.
    generalize dependent l. induction i; vauto. ins. destruct l; auto.
  Qed. 
    
  Lemma firstn_skipn_comm : forall {A: Type} m n (l: list A),
      firstn m (skipn n l) = skipn n (firstn (n + m) l).
  Proof. Admitted. 

  Lemma ll_index_shift {A: Type} (ll: list (list A)) i j
         block (ITH: Some block = nth_error ll i) (NE: Forall (fun l => l <> []) ll)
         (J_BOUND: j <= length ll)
         (FLT_SHIFT: length (flatten (firstn j ll)) = length (flatten (firstn i ll)) + length block):
    j = i + 1.
   Proof.
     destruct (dec_le j i) as [LE | GT].
     { rewrite (firstn_ge_incl ll LE) in FLT_SHIFT.  
       rewrite flatten_app, length_app in FLT_SHIFT.
       cut (length block > 0); [ins; omega |]. 
       eapply Forall_forall in NE; vauto.
       eapply nth_error_In. eauto. }
     apply not_le in GT.
     rewrite (@firstn_ge_incl _ ll i j) in FLT_SHIFT; [| omega].
     assert (exists d, j = i + S d).
     { forward eapply (@DIFF_LE i j); [omega |]. 
       ins. desc. subst. destruct d; vauto. omega. }
     desc. subst.
     cut (d = 0); [ins; omega|].
     destruct d; auto. 
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
     pose proof (Forall_forall (fun l : list A => l <> []) ll).
     cut (block' <> []).
     { ins. destruct block'; vauto. }
     apply H; auto.  
     eapply nth_error_In. eauto.
     (* ??? Proof General successfully goes there but Qed fails *)
     (* Qed.  *)     
   Admitted.

   (* Lemma compilation_injective PO PO' BPI (COMP: is_thread_block_compiled PO BPI) *)
   (*       (COMP': is_thread_block_compiled PO' BPI): PO = PO'. *)
   (* Proof. *)
   (*   generalize dependent PO. generalize dependent PO'. *)
   (*   induction BPI as [| block BPI_].  *)
   (*   { ins. *)
   (*     apply compilation_same_length in COMP.  *)
   (*     apply compilation_same_length in COMP'. *)
   (*     simpl in *. destruct PO; destruct PO'; vauto. } *)
   (*   ins. *)
   (*   (* destruct PO as [| oinstr PO_]. *) *)
   (*   (* { apply compilation_same_length in COMP. vauto. } *) *)
   (*   (* destruct PO' as [| oinstr' PO'_]. *) *)
   (*   (* { apply compilation_same_length in COMP'. vauto. } *) *)
     
   (*   inversion COMP as [BPI0 [CMP CORR]]. inversion COMP' as [BPI0' [CMP' CORR']]. desc. *)
   (*   inversion CMP as [| oinstr block0 PO_ BPI0_]; subst.  *)
   (*   { apply compilation_same_length in COMP. vauto. } *)
   (*   inversion H; subst; vauto.  *)
     
   (*   inversion CORR as [| block0 BPI0_]. subst. *)
   (*   inversion CORR' as [| block0' BPI0_']. subst. *)
   (*   assert (block0 = block0'). *)
   (*   { red in H.  *)

   (*   inversion CORR'. subst. *)
     
   (*   f_equal. *)
   (*   { inversion COMP as [BPI0 [COMP0 CORR]]. *)
   (*     inversion COMP0. subst.  *)
   (*     inversion COMP' as [BPI0' [COMP0' CORR']].  *)
   (*     inversion COMP0'. subst.  *)
     
     
   (*   inversion CMP. subst. inversion CMP'. subst. *)
   (*   f_equal. *)
   (*   {  *)

   (*     apply IHBPI.  *)
     
   Lemma correction_same_struct BPI0 BPI ref
         (CORR: Forall2 (block_corrected ref) BPI0 BPI):
     same_struct BPI0 BPI.
   Proof.
     generalize dependent BPI0.
     induction BPI.
     { ins. inversion CORR. red. auto. }
     ins. inversion CORR. subst.
     red. apply Forall2_cons.
     { red in H2. eapply Forall2_length; eauto. }
     apply IHBPI; auto.
   Qed. 

   Definition mm_similar_states_ext sto bsti :=
     is_thread_block_compiled (instrs sto) (binstrs bsti) /\
     pc sto = bpc bsti /\
     same_behavior_local_ext (G sto) (bG bsti) /\
     (forall reg, reg <> exchange_reg -> regf sto reg = bregf bsti reg) /\
     (forall reg, reg <> exchange_reg -> depf sto reg = bdepf bsti reg) /\
     ectrl sto = bectrl bsti /\ eindex sto = beindex bsti.

   Lemma sbl_ext_stronger GO GI
         (SBL_EXT: same_behavior_local_ext GO GI):
     same_behavior_local GO GI.
   Proof.
     red in SBL_EXT. desc. red. splits; auto.
   Qed.
   Hint Resolve sbl_ext_stronger. 
     
   Lemma mm_sim_ext_stronger sto bsti
         (MM_SIM_EXT: mm_similar_states_ext sto bsti):
     mm_similar_states sto bsti.
   Proof.
     red in MM_SIM_EXT. red. desc. splits; vauto. auto. 
   Qed.
   Hint Resolve mm_sim_ext_stronger. 
   
  Lemma comm_helper tid index S:
    eq (ThreadEvent tid index) ∩₁ S ≡₁ S ∩₁ eq (ThreadEvent tid index).
  Proof. by ins; apply set_interC. Qed. 
        
  Lemma RESTR_EXPAND  {A: Type} (S1 S2: A -> Prop) (r: relation A):
    restr_rel (S1 ∪₁ S2) r ≡ ⦗S1⦘ ⨾ r ⨾ ⦗S1⦘ ∪ ⦗S1⦘ ⨾ r ⨾ ⦗S2⦘ ∪ ⦗S2⦘ ⨾ r ⨾ ⦗S1⦘ ∪ ⦗S2⦘ ⨾ r ⨾ ⦗S2⦘.
  Proof.  by (ins; basic_solver 10). Qed.

  Ltac discr_new_body := rewrite label_set_bound_inter; [| by eauto | by omega | by (eauto with label_ext) | by vauto].
  Ltac discr_new := discr_new_body || (rewrite comm_helper; discr_new_body). 
  Ltac discr_E_body := rewrite E_bound_inter; [| by eauto | by omega]. 
  Ltac discr_E := discr_E_body || (rewrite comm_helper; discr_E_body).
  Ltac discr_RWO_body := rewrite RWO_bound_inter; [| by eauto | by omega].
  Ltac discr_RWO := discr_RWO_body || (rewrite comm_helper; discr_RWO_body).
  Ltac discr_events := rewrite diff_events_empty; [| by omega].
  Ltac same_events := rewrite set_interK.
  Ltac simplify_updated_sets := repeat (discr_new || discr_E || discr_RWO || discr_events || same_events); remove_emptiness.

  Ltac unfold_clear_updated := repeat match goal with
                            | H: ?eset ≡₁ ?eset' |- _ => try rewrite H; clear H
                            | H: ?erel ≡ ?erel' |- _ => try rewrite H; clear H
                                         end.
  Ltac expand_sets_only := try rewrite !set_inter_union_r; remove_emptiness; try rewrite !set_inter_union_l; remove_emptiness. 
  Ltac expand_rels := try rewrite !seq_union_l; remove_emptiness; try rewrite !seq_union_r; try expand_sets_only. 
  Ltac by_IH IH := red in IH; desc; vauto. 

  (* E is folded because many lemmas use 'In e acts_set' instead of E*)
  Ltac discr_dom DOM st := rewrite DOM; fold (E (G st));
                           rewrite !seqA; repeat seq_rewrite <- id_inter;
                           simplify_updated_sets;
                           repeat seq_rewrite id_inter;
                           rewrite !seqA; seq_rewrite <- DOM.
  
  Lemma pair_step sto bsti (MM_SIM: mm_similar_states_ext sto bsti)
        tid bsti' (OSEQ_STEP: omm_block_step tid bsti bsti')
        (BPC'_BOUND: bpc bsti' <= length (binstrs bsti))
        (BLOCK_REACH: (block_step tid)＊ (binit (binstrs bsti)) bsti):
    exists sto', Ostep tid sto sto' /\ mm_similar_states_ext sto' bsti'.
  Proof.
    pose proof (block_step_nonterminal (bs_extract OSEQ_STEP)) as BST_NONTERM.
    red in OSEQ_STEP. desc. 
    (* assert (PO = instrs sto) as PO_sto. *)
    (* { red in MM_SIM.  *)
    (*   pose proof compilation_injective.  *)
    pose proof (@reach_with_blocks bsti (bst2st bsti) tid eq_refl BLOCK_REACH) as [n_steps REACH]. 
    assert (wf_thread_state tid (bst2st bsti)) as WFT.
    { apply wf_thread_state_steps with (s := (init (instrs (bst2st bsti))));
        [apply wf_thread_state_init| ].
      apply crt_num_steps. eauto. } 
    
    pose proof MM_SIM as MM_SIM_. 
    red in MM_SIM. desc. pose proof MM_SIM as TBC. red in MM_SIM. desc. 
    assert (exists oinstr, Some oinstr = nth_error (instrs sto) (bpc bsti)) as [oinstr OINSTR]. 
    { apply OPT_VAL. apply nth_error_Some.
      replace (length (instrs sto)) with (length (binstrs bsti)); [omega|].
      symmetry. apply compilation_same_length. red. eauto. }    
    red in BLOCK_STEP. desc. rename BLOCK_STEP0 into BLOCK_STEP.
    assert (exists block0, Some block0 = nth_error BPI0 (bpc bsti)) as [block0 BLOCK0].
    { apply OPT_VAL. apply nth_error_Some.
      replace (length BPI0) with (length (binstrs bsti)).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length. eauto. }
    assert (is_instruction_compiled oinstr block0) as COMP_BLOCK.
    { eapply Forall2_index; eauto. } 
    assert (block_corrected BPI0 block0 block) as CORR_BLOCK.
    { eapply Forall2_index; eauto. } 
    (* forward eapply (@BPC_CHANGE bsti bsti') as BPC'; eauto. *)
    (* { red. splits; eauto. } *)
      (* { eexists. red. splits; eauto. } *)
      (* exists PO. vauto. }  *)
    inversion COMP_BLOCK; subst; simpl in *. 
    - replace block with [ld] in *.
      2: { subst ld. inversion CORR_BLOCK. inversion H3. subst.
           inversion H1. auto. }
      simpl in *. 
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some ld = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc ld [ld] 0 _ bsti sti); eauto.
        Unshelve. 2: { eauto. }
        rewrite Nat.add_0_r. auto. }
      red in BLOCK_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto)
                         (Aload false ord (RegFile.eval_lexpr (regf sti) lexpr) val) ∅
                         (DepsFile.lexpr_deps (depf sti) lexpr) (ectrl sti) ∅;
                         eindex := eindex sto + 1;
                regf := RegFun.add reg val (regf sto);
                depf := RegFun.add reg (eq (ThreadEvent tid (eindex sti))) (depf sto);
                ectrl := ectrl sto |}).
      (* assert (REGF_EQ: regf sto = regf sti).  *)
      (* { rewrite MM_SIM2. vauto. } *)
      (* assert (DEPF_EQ: depf sto = depf sti).  *)
      (* { rewrite MM_SIM3. vauto. } *)
      forward eapply (@E_ADD (G sto) (G sto')) as EGO'; [repeat eexists; eauto| ].
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      assert (Instr.load Orlx lhs loc = Instr.load ord reg lexpr).
      { subst ld. congruence. }
      inversion H. subst ord. subst lhs. subst loc. clear H. 
      exists sto'. splits.
      { red. exists lbls. red. splits; [subst; simpl; auto| ].
        exists ld. exists 0. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled TBC (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (ld = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP; vauto. }
          desc. inversion COMP0. }
        pose proof (@Oload tid lbls sto sto' ld 0 Orlx reg lexpr val l) as OMM_STEP.
        rewrite (* ORD_RLX, *) (* REGF_EQ, *) (* DEPF_EQ, *) EINDEX_EQ, ECTRL_EQ in *.

        assert (RegFile.eval_lexpr (regf sto) lexpr = RegFile.eval_lexpr (regf sti) lexpr) as LEXPR_SAME.
        { eapply INSTR_LEXPR_HELPER; eauto. vauto. }
        assert (DepsFile.lexpr_deps (depf sto) lexpr = DepsFile.lexpr_deps (depf sti) lexpr) as LEXPR_DEPS_SAME.
        { eapply INSTR_LEXPR_DEPS_HELPER; eauto; vauto. }

        forward eapply OMM_STEP; eauto.
        { subst sto'. simpl. rewrite LEXPR_SAME. auto. }
        { rewrite LABELS. do 2 f_equal. auto. }
        { rewrite Nat.add_0_r. rewrite LEXPR_DEPS_SAME, LEXPR_SAME.
          subst sto'. simpl. congruence. }
        { subst sto'. simpl. omega. }
        subst sto'. simpl. rewrite Nat.add_0_r. congruence. }
      replace (flatten (binstrs bsti)) with (instrs sti) in * by vauto. 
      forward eapply (@E_ADD (G sti) (G sti')) as E_SPLITS;
        [repeat eexists; eauto| ].          
      forward eapply (@RWO_ADD sti sti') as RWO_SPLITS; eauto.
      red. splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto'. simpl. 
        forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti') _ AT_BLOCK); eauto. 
        { eapply COMPILED_NONEMPTY; eauto. }
        { subst sti. subst sti'. simpl in UPC. simpl. congruence. }
        ins. congruence. }
      { red.        
        splits.
        { replace (bG bsti') with (G sti') by vauto.
          unfold_clear_updated. simpl. expand_rels.           
          simplify_updated_sets. rewrite EINDEX_EQ.
          apply set_equiv_union; [by_IH MM_SIM1 | basic_solver]. }
        { replace (bG bsti') with (G sti'); [| vauto ]. 
          forward eapply (@sim_lab_extension 0 tid sto sti); eauto.
          { subst sti. auto. }
          { apply (@E_bounded n_steps tid sti); eauto. }
          { red. split. 
            2: { subst sto'. simpl. omega. }
            rewrite Nat.add_0_r.
            replace (lab (G sti') (ThreadEvent tid (eindex sto))) with (Aload false Orlx (RegFile.eval_lexpr (regf sti) lexpr) val).
            { repeat eexists. }
            unfold add. rewrite UG, EINDEX_EQ. simpl.
            rewrite upds. auto. }
          replace (0 + 1) with 1 by omega. rewrite (same_relation_exp (pow_unit _)).
          red. eexists. red. split.
          2: { cut (eindex sti' = eindex sti + 1); [omega |].
               vauto. }
          rewrite Nat.add_0_r. repeat eexists. eauto. }        
        { subst sto'. replace (bG bsti') with (G sti'); [| vauto ]. simpl.
          unfold_clear_updated. rewrite UG. unfold add. simpl.
          remove_emptiness. rewrite RESTR_EXPAND.
          discr_dom (wft_rmwE WFT) sti.
          rewrite <- restr_relE. by_IH MM_SIM1. }
        { subst sto'. replace (bG bsti') with (G sti'); [| vauto ]. simpl.
          unfold_clear_updated. simpl. 
          rewrite UG. unfold add. simpl. remove_emptiness.
          rewrite RESTR_EXPAND.
          discr_dom (wft_dataE WFT) sti.
          rewrite <- restr_relE. by_IH MM_SIM1. }
        { subst sto'. replace (bG bsti') with (G sti'); [| vauto ]. simpl.
          unfold_clear_updated. simpl. 
          rewrite UG. unfold add. simpl. remove_emptiness.
          rewrite RESTR_EXPAND. expand_rels. 
          discr_dom (wft_ctrlE WFT) sti.
          assert (forall {A: Type} (S1 S2 S3 S4: A -> Prop),
                     ⦗S1⦘ ⨾ (S2 × S3) ⨾ ⦗S4⦘ ≡ (S1 ∩₁ S2) × (S3 ∩₁ S4)) as SEQ_EQV_CROSS. 
          { ins. basic_solver. }
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets. 
          assert (eq (ThreadEvent tid (eindex sti)) ∩₁ ectrl sti ≡₁ ∅).
          { split; [| basic_solver]. rewrite (wft_ectrlE WFT).
            simplify_updated_sets. auto. }
          rewrite H. remove_emptiness.
          foobar. 
          rewrite <- restr_relE. by_IH MM_SIM1. }        (* **** *)
        

      }
      { ins. replace (bregf bsti') with (regf sti'); [| vauto ].
        rewrite UREGS.
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg); auto.
        unfold RegFun.find. subst sti. simpl. apply MM_SIM2. auto. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. rewrite UDEPS.
        ins. unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg); vauto.
        unfold RegFun.find. simpl. auto. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
    - replace block with [f; st] in *.
      2: { subst f. subst st. inversion CORR_BLOCK.
           inversion H3. inversion H1. inversion H6. inversion H8.
           subst. auto. }
      simpl in *. 
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc f [f; st] 0 _ bsti sti); eauto.
        Unshelve. 2: { eauto. }
        rewrite Nat.add_0_r. auto. }
      assert (AT_PC': Some st = nth_error (instrs sti) (pc sti + 1)).
      { forward eapply (@near_pc st [f; st] 1 _ bsti sti).
        Unshelve. all: eauto. }
      
      red in STEP'. desc. red in STEP'. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto;
                G := G sto;
                eindex := eindex sto;
                regf := regf sto;
                depf := depf sto;
                ectrl := ectrl sto |}).

      red in STEP''. desc. red in STEP''. desc.
      rewrite <- INSTRS, UPC, <- AT_PC' in ISTEP. inversion ISTEP as [EQ']. clear ISTEP. 
      inversion ISTEP1.
      all: rewrite II in EQ'.
      all: try discriminate.
      rewrite EQ' in *. subst instr.
      rename x into xmd. 
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto' + 1;
                (* G := add (G sto') tid (eindex sto') (Astore x ord0 l v) *)
                G := add (G sto') tid (eindex sto' + 1) (Astore xmd ord0 l v)
                         (DepsFile.expr_deps (depf sto') expr)
                         (DepsFile.lexpr_deps (depf sto') lexpr) (ectrl sto') ∅;
                eindex := eindex sto' + 2;
                regf := regf sto';
                depf := depf sto';
                ectrl := ectrl sto' |}).

      (* assert (REGF_EQ: regf sto = regf sti).  *)
      (* { rewrite MM_SIM2. vauto. } *)
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      
      assert (Instr.store Orlx lexpr expr = Instr.store Orlx loc val).
      { subst st. congruence. }
      inversion H. subst loc. subst val. clear H. 
      
      assert (RegFile.eval_lexpr (regf sto) lexpr = RegFile.eval_lexpr (regf sti) lexpr) as LEXPR_SAME.
      { eapply INSTR_LEXPR_HELPER; eauto. vauto. }
      assert (DepsFile.lexpr_deps (depf sto) lexpr = DepsFile.lexpr_deps (depf sti) lexpr) as LEXPR_DEPS_SAME.
      { eapply INSTR_LEXPR_DEPS_HELPER; eauto. vauto. }
      assert (RegFile.eval_expr (regf sto) expr = RegFile.eval_expr (regf sti) expr) as EXPR_SAME.
      { eapply INSTR_EXPR_HELPER; eauto. vauto. }
        
      exists sto''. splits.
      { red. exists lbls0. red. splits; [subst; simpl; auto| ].
        exists st. exists 1. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled TBC (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (st = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        assert (ORD_RLX: ord0 = Orlx). 
        { subst st. congruence. }
        rewrite ORD_RLX in *. 

        pose proof (@Ostore tid lbls0 sto sto'' st 1 Orlx lexpr expr l v) as OMM_STEP.        
        
        forward eapply OMM_STEP; eauto.
        (* TODO: modify equalities above to operate with sti' ? *)
        { rewrite LEXPR_SAME, <- UREGS. auto. }
        { rewrite EXPR_SAME, <- UREGS. auto. }
        { subst sto''. subst sto'. simpl. rewrite ORD_RLX, EINDEX_EQ.
          unfold add at 1. simpl. basic_solver.  }
        subst sto''. subst sto'. simpl. omega. }
      red.
      pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH]. 
      
      splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl.
        forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti'') _ AT_BLOCK); eauto. 
        { eapply COMPILED_NONEMPTY; eauto. }
        { subst sti''. rewrite UPC in UPC0.
          subst sti. simpl in UPC0. simpl.
          rewrite BINSTRS_SAME at 1. omega. }
        ins. congruence. }
      { red.
        assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
        { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
          exists sti. split.
          { rewrite <- INSTRS. auto. }
          red. exists lbls. red. splits; auto.
          eexists. eauto. }
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.
          forward eapply (@E_ADD (G sti') (G sti'')) as E_SPLITS'; eauto.
          { repeat eexists. eauto. }
          forward eapply (@RWO_ADD sti' sti'') as RWO_SPLITS'; eauto.
          forward eapply (@E_ADD (G sti) (G sti')) as E_SPLITS; eauto.
          { repeat eexists. eauto. }
          forward eapply (@RWO_ADD sti sti') as RWO_SPLITS; eauto.
          simpl in RWO_SPLITS', RWO_SPLITS. 
          rewrite E_SPLITS', RWO_SPLITS', E_SPLITS, RWO_SPLITS. 
          rewrite !set_inter_union_l, !set_inter_union_r.
          rewrite UINDEX.
          rewrite E_bound_inter; [| eauto | omega]. 
          rewrite set_interC with (s := eq (ThreadEvent tid (eindex sti))).
          rewrite set_interC with (s := eq (ThreadEvent tid (eindex sti + 1))).
          repeat (rewrite RWO_bound_inter; [| eauto | omega]).
          rewrite diff_events_empty; [| omega]. 
          remove_emptiness. 
          rewrite set_interK. 
          red in MM_SIM1. desc.
          simpl. rewrite (@E_ADD (G sto')); [| repeat eexists]. 
          simpl.
          rewrite RESTR_EVENTS. rewrite MM_SIM5.
          replace (G sti) with (bG bsti) by vauto.
          basic_solver 100. }
        
        replace (bG bsti'') with (G sti''); [| vauto ]. 
        forward eapply (@sim_lab_extension 1 tid sto sti); eauto.
        { vauto. }
        { apply (@E_bounded n_steps tid sti); eauto. }
        { red. split. 
          2: { subst sto''. simpl. omega. } 
          replace (lab (G sti'') (ThreadEvent tid (eindex sto + 1)))  with (Astore xmd ord0 l v).
          2: { rewrite UG0, UG. simpl.
               replace (eindex sti') with (eindex sto + 1) by congruence. 
               rewrite upds. auto. }
          repeat eexists. }
        simpl. red. exists sti'. split.
        { red. exists sti. split; [red; auto|]. red. eexists. red.
          rewrite Nat.add_0_r. split; auto. repeat eexists. eauto. }
        red. eexists. red. rewrite Nat.add_0_r. split; auto.
        repeat eexists. eauto. }
      (* { subst sto'. replace (bregf bsti'') with (regf sti''); [| vauto ]. *)
      (*   simpl. congruence. } *)
      { ins. replace (bregf bsti'') with (regf sti''); [| vauto ].
        rewrite UREGS0, UREGS.
        replace (regf sti reg) with (bregf bsti reg); [| vauto]. 
        apply MM_SIM2. auto. }
      { subst sto''. replace (bdepf bsti'') with (depf sti''); [| vauto ].
        simpl. rewrite UDEPS0, UDEPS. vauto. }
      { subst sto'. replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
    - replace block with [f; ld] in *.
      2: { subst f. subst ld. inversion CORR_BLOCK.
           inversion H3. inversion H1. inversion H6. inversion H8.
           subst. auto. }
      simpl in *. 
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc f [f; ld] 0 _ bsti sti); eauto.
        Unshelve. 2: eauto. 
        rewrite Nat.add_0_r. auto. }
      assert (AT_PC': Some ld = nth_error (instrs sti) (pc sti + 1)).
      { forward eapply (@near_pc ld [f; ld] 1 _ bsti sti).
        Unshelve. all: eauto. }

      red in STEP'. desc. red in STEP'. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 
      
      red in STEP''. desc. red in STEP''. desc.
      rewrite <- INSTRS, UPC, <- AT_PC' in ISTEP. inversion ISTEP as [EQ']. clear ISTEP. 
      inversion ISTEP1.
      all: rewrite II in EQ'.
      all: try discriminate.
      rewrite EQ' in *. subst instr.
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto + 1) (Aload false ord0 (RegFile.eval_lexpr (regf sto) lexpr) val)
                         ∅
                         (DepsFile.lexpr_deps (depf sto) lexpr) (ectrl sto) ∅;
                eindex := eindex sto + 2;
                regf := RegFun.add reg val (regf sto);
                depf := RegFun.add reg (eq (ThreadEvent tid (eindex sto + 1))) (depf sto);
                ectrl := ectrl sto |}).

      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      
      assert (Instr.load Osc reg lexpr = Instr.load Osc lhs loc).
      { subst ld. congruence. }
      inversion H. subst lhs. subst loc. clear H.
      
      assert (RegFile.eval_lexpr (regf sto) lexpr = RegFile.eval_lexpr (regf sti) lexpr) as LEXPR_SAME.
      { eapply INSTR_LEXPR_HELPER; eauto. vauto. }
      assert (DepsFile.lexpr_deps (depf sto) lexpr = DepsFile.lexpr_deps (depf sti) lexpr) as LEXPR_DEPS_SAME.
      { eapply INSTR_LEXPR_DEPS_HELPER; eauto. vauto. }
      (* assert (RegFile.eval_expr (regf sto) expr = RegFile.eval_expr (regf sti) expr) as EXPR_SAME. *)
      (* { eapply INSTR_EXPR_HELPER; eauto; [red; splits; vauto| vauto]. } *)

      exists sto''. splits.
      { red. exists lbls0. red. splits; [subst; simpl; auto| ].
        exists ld. exists 1. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled TBC (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (ld = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        assert (ORD_SC: ord0 = Osc). 
        { subst ld. congruence. }
        rewrite ORD_SC in *.
        
        pose proof (@Oload tid lbls0 sto sto'' ld 1 Osc reg lexpr val l) as OMM_STEP.

        forward eapply OMM_STEP; eauto.
        (* TODO: modify equalities above to operate with sti' ? *)
        { rewrite LEXPR_SAME, <- UREGS. auto. }
        { rewrite LEXPR_SAME, <- UREGS. auto. }
        { subst sto''. simpl. rewrite ORD_SC, EINDEX_EQ.
          unfold add at 1. simpl. basic_solver. }
        subst sto''. simpl. omega. }
      red.
      pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH]. 
      
      splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl.
        forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti'') _ AT_BLOCK); eauto. 
        { eapply COMPILED_NONEMPTY; eauto. }
        { subst sti''. rewrite UPC in UPC0.
          subst sti. simpl in UPC0. simpl.
          rewrite BINSTRS_SAME at 1. omega. }
        ins. congruence. }
      { red.
        assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
        { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
          exists sti. split.
          { rewrite <- INSTRS. auto. }
          red. exists lbls. red. splits; auto.
          eexists. eauto. }
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.
          forward eapply (@E_ADD (G sti') (G sti'')) as E_SPLITS'; eauto.
          { repeat eexists. eauto. }
          forward eapply (@RWO_ADD sti' sti'') as RWO_SPLITS'; eauto.
          forward eapply (@E_ADD (G sti) (G sti')) as E_SPLITS; eauto.
          { repeat eexists. eauto. }
          forward eapply (@RWO_ADD sti sti') as RWO_SPLITS; eauto.
          simpl in RWO_SPLITS', RWO_SPLITS. 
          rewrite E_SPLITS', RWO_SPLITS', E_SPLITS, RWO_SPLITS. 
          rewrite !set_inter_union_l, !set_inter_union_r.
          rewrite UINDEX.
          rewrite E_bound_inter; [| eauto | omega]. 
          rewrite set_interC with (s := eq (ThreadEvent tid (eindex sti))).
          rewrite set_interC with (s := eq (ThreadEvent tid (eindex sti + 1))).
          repeat (rewrite RWO_bound_inter; [| eauto | omega]).
          rewrite diff_events_empty; [| omega]. 
          remove_emptiness. 
          rewrite set_interK. 
          red in MM_SIM1. desc.
          simpl. rewrite (@E_ADD (G sto)); [| repeat eexists]. 
          simpl.
          rewrite RESTR_EVENTS. rewrite MM_SIM5.
          replace (G sti) with (bG bsti) by vauto.
          basic_solver 100. }
        
        replace (bG bsti'') with (G sti''); [| vauto ]. 
        forward eapply (@sim_lab_extension 1 tid sto sti); eauto.
        { vauto. }
        { apply (@E_bounded n_steps tid sti); eauto. }
        { red. split. 
          2: { subst sto''. simpl. omega. } 
          replace (lab (G sti'') (ThreadEvent tid (eindex sto + 1))) with (Aload false ord0 (RegFile.eval_lexpr (regf sto) lexpr) val).
          2: { rewrite UG0, UG. rewrite UREGS, LEXPR_SAME. simpl.
               replace (eindex sti') with (eindex sto + 1) by congruence. 
               rewrite upds. auto. }
          repeat eexists. }
        simpl. red. exists sti'. split.
        { red. exists sti. split; [red; auto|]. red. eexists. red.
          rewrite Nat.add_0_r. split; auto. repeat eexists. eauto. }
        red. eexists. red. rewrite Nat.add_0_r. split; auto.
        repeat eexists. eauto. }
      { ins. replace (bregf bsti'') with (regf sti''); [| vauto ].
        rewrite UREGS0, UREGS.
        replace (regf sti reg) with (bregf bsti reg); [| vauto].
        unfold RegFun.add.
        destruct (LocSet.Facts.eq_dec reg0 reg); vauto. 
        apply MM_SIM2. auto. }      
      { replace (bdepf bsti'') with (depf sti''); [| vauto ].
        subst sto''. simpl. rewrite UDEPS0, UDEPS. rewrite UINDEX, EINDEX_EQ.         
        ins. unfold RegFun.add.
        destruct (LocSet.Facts.eq_dec reg0 reg); vauto.
        unfold RegFun.find. simpl. auto. }
      { replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
    - replace block with [f; exc] in *.
      2: { subst f. subst exc. inversion CORR_BLOCK.
           inversion H3. inversion H1. inversion H6. inversion H8.
           subst. auto. }
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc f [f; exc] 0 _ bsti sti); eauto.
        Unshelve. 2: eauto. 
        rewrite Nat.add_0_r. auto. }
      assert (AT_PC': Some exc = nth_error (instrs sti) (pc sti + 1)).
      { forward eapply (@near_pc exc [f; exc] 1 _ bsti sti).
        Unshelve. all: eauto. }
      red in STEP'. desc. red in STEP'. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 

      red in STEP''. desc. red in STEP''. desc.
      rewrite <- INSTRS, UPC, <- AT_PC' in ISTEP. inversion ISTEP as [EQ']. clear ISTEP. 
      inversion ISTEP1.
      all: rewrite II in EQ'.
      all: try discriminate.
      rewrite EQ' in *. subst instr.
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto + 2) (Astore xmod ordw loc0 new_value)
                         (DepsFile.expr_deps (depf sto) new_expr)
                         (DepsFile.lexpr_deps (depf sto) loc_expr) 
                         (ectrl sti') ∅;
                eindex := eindex sto + 3;
                regf := regf sto;
                depf := depf sto; (* TODO: deal with changed depf after rmw *)
                ectrl := ectrl sto |}).

      assert (EINDEX_EQ: eindex sto = eindex sti).
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti).
      { rewrite MM_SIM4. vauto. }
      assert (forall A B, (~ ~ A <-> ~ ~ B) -> A <-> B) as NN_IFF. 
      { intros A B [IMP1 IMP2]. split; ins; apply NNPP; auto. }
      
      assert (Instr.update (Instr.exchange new_expr) xmod ordr ordw reg loc_expr = Instr.update (Instr.exchange val) Xpln Osc Osc exchange_reg loc).
      { subst exc. congruence. }
      inversion H. subst new_expr. subst xmod. subst ordr.
      subst ordw. subst reg. subst loc_expr. clear H.
      
      assert (RegFile.eval_lexpr (regf sto) loc = RegFile.eval_lexpr (regf sti) loc) as LEXPR_SAME.
      { eapply INSTR_LEXPR_HELPER; eauto. vauto. }
      assert (DepsFile.lexpr_deps (depf sto) loc = DepsFile.lexpr_deps (depf sti) loc) as LEXPR_DEPS_SAME.
      { eapply INSTR_LEXPR_DEPS_HELPER; eauto. vauto. }
      assert (RegFile.eval_expr (regf sto) val = RegFile.eval_expr (regf sti) val) as EXPR_SAME.
      { eapply eval_rmw_expr; eauto. 
        { exists (instrs sto). red.
          unfold is_thread_compiled_with.
          eexists. eauto. }
        { replace (regf sti) with (bregf bsti); vauto. }
        2: { Unshelve. 2: exact (Instr.exchange val). vauto. }
        repeat eexists. 
        eapply nth_error_In. replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto. }
        
      exists sto''. splits.
      { red. exists [Astore Xpln Osc loc0 new_value]. red. splits; [subst; simpl; auto| ].
        exists st. exists 2. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto.
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled TBC (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (st = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        
        pose proof (@Ostore tid [Astore Xpln Osc loc0 new_value] sto sto'' st 2 Osc loc val loc0 new_value) as OMM_STEP.

        forward eapply OMM_STEP; eauto.
        { rewrite LEXPR_SAME, <- UREGS. auto. }
        { rewrite EXPR_SAME , <- UREGS. auto. }
        { subst sto''. simpl. congruence. }
        subst sto''. simpl. omega. }
      red.
      pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH].
      
      splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl.
        forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti'') _ AT_BLOCK); eauto. 
        { eapply COMPILED_NONEMPTY; eauto. }
        { subst sti''. rewrite UPC in UPC0.
          subst sti. simpl in UPC0. simpl.
          rewrite BINSTRS_SAME at 1. omega. }
        ins. congruence. }
      { red.
        assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
        { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
          exists sti. split.
          { rewrite <- INSTRS. auto. }
          red. exists lbls. red. splits; auto.
          eexists. eauto. }
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.          
          forward eapply (@E_ADD_RMW (G sti') (G sti'')) as E_SPLITS'; eauto.
          { repeat eexists. eauto. }
          forward eapply (@RWO_ADD_rmw sti' sti'') as RWO_SPLITS'; eauto.
          forward eapply (@E_ADD (G sti) (G sti')) as E_SPLITS; eauto.
          { repeat eexists. eauto. }
          forward eapply (@RWO_ADD sti sti') as RWO_SPLITS; eauto.
          simpl in RWO_SPLITS', RWO_SPLITS. 
          rewrite E_SPLITS', RWO_SPLITS', E_SPLITS, RWO_SPLITS. 
          rewrite !set_inter_union_l, !set_inter_union_r.
          rewrite UINDEX.
          rewrite E_bound_inter; [| eauto | omega]. 
          rewrite set_interC with (s := eq (ThreadEvent tid (eindex sti))).
          rewrite set_interC with (s := eq (ThreadEvent tid (eindex sti + 1))).
          repeat (rewrite RWO_bound_inter; [| eauto | omega]).
          repeat (rewrite diff_events_empty; [| omega]). 
          remove_emptiness. 
          rewrite set_interK. 
          red in MM_SIM1. desc.
          simpl. rewrite (@E_ADD (G sto)); [| repeat eexists]. 
          simpl.
          rewrite RESTR_EVENTS. rewrite MM_SIM5.
          replace (G sti) with (bG bsti) by vauto.
          replace (eindex sti + 1 + 1) with (eindex sti + 2) by omega. 
          basic_solver 100. }
                
        replace (bG bsti'') with (G sti''); [| vauto ].
        ins. rewrite UG0, UG, UINDEX, EINDEX_EQ. simpl.
        unfold add, acts_set in EGOx. simpl in EGOx. destruct EGOx.
        - replace (eindex sti + 1 + 1) with (eindex sti + 2) by omega.
          rewrite <- H. rewrite EINDEX_EQ. repeat rewrite upds. auto.
        - assert (E (G sti) x).
          { red in MM_SIM1. desc. red in RESTR_EVENTS. desc.
            red in RESTR_EVENTS. unfold acts_set in RESTR_EVENTS.
            apply RESTR_EVENTS in H. red in H. desc. vauto. }
          apply (hahn_subset_exp (@E_bounded n_steps tid sti REACH)) in H0. 
          repeat rewrite updo.
          2-5: red; ins; subst; simpl in H0; omega.
          replace (G sti) with (bG bsti); [| vauto ].
          red in MM_SIM1. desc. apply SAME_LAB. auto. }
      { subst sto''. replace (bregf bsti'') with (regf sti''); [| vauto ].
        rewrite UREGS0, UREGS. simpl.
        ins. unfold RegFun.add.
        destruct (LocSet.Facts.eq_dec reg exchange_reg); vauto.
        unfold RegFun.find. unfold bst2st. simpl. auto. }
      { replace (bdepf bsti'') with (depf sti''); [| vauto ].
        subst sto''. simpl.
        ins. rewrite UDEPS0, UDEPS.
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg exchange_reg); vauto.
        unfold RegFun.find. simpl. auto. }
      { replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
    - replace block with [asn] in *.
      2: { subst asn. inversion CORR_BLOCK.
           inversion H0. inversion H3. inversion H1. 
           subst. auto. }
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some asn = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc asn [asn] 0 _ bsti sti); eauto.
        Unshelve. 2: eauto. 
        rewrite Nat.add_0_r. auto. }
      red in BLOCK_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := G sto;
                regf := RegFun.add reg (RegFile.eval_expr (regf sto) expr) (regf sto);
                depf := RegFun.add reg (DepsFile.expr_deps (depf sto) expr) (depf sto);
                ectrl := ectrl sto;
                eindex := eindex sto |}).
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      assert (Instr.assign lhs rhs = Instr.assign reg expr).
      { subst asn. congruence. }
      inversion H. subst lhs. subst rhs. clear H. 
      
      assert (RegFile.eval_expr (regf sto) expr = RegFile.eval_expr (regf sti) expr) as EXPR_SAME.
      { eapply INSTR_EXPR_HELPER; eauto. vauto. }
      assert (DepsFile.expr_deps (depf sto) expr = DepsFile.expr_deps (depf sti) expr) as EXPR_DEPS_SAME.
      { eapply INSTR_EXPR_DEPS_HELPER; eauto. vauto. }

      exists sto'. splits.
      { red. exists []. red. splits; [subst; simpl; auto| ].
        exists asn. exists 0. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled TBC (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (asn = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        pose proof (@Oassign tid [] sto sto' asn 0 reg expr) as OMM_STEP.
        rewrite EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto. }
      red. splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto'. simpl.
        forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti') _ AT_BLOCK); eauto. 
        { eapply COMPILED_NONEMPTY; eauto. }
        { subst sti'. subst sti. simpl.
          simpl in UPC. congruence. }
        ins. congruence. }
      { subst sto'. simpl. replace (bG bsti') with (G sti'); [| vauto ].
        rewrite UG. vauto. }
      { subst sto'. replace (bregf bsti') with (regf sti'); [| vauto ].
        simpl.
        ins. rewrite UREGS. unfold RegFun.add.
        destruct (LocSet.Facts.eq_dec reg0 reg); vauto.
        unfold RegFun.find. unfold bst2st. simpl. auto. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. ins. rewrite UDEPS. rewrite EXPR_DEPS_SAME. 
        unfold RegFun.add.
        destruct (LocSet.Facts.eq_dec reg0 reg); vauto.
        unfold RegFun.find. simpl. auto. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
    - replace block with [Instr.ifgoto e (length (flatten (firstn n (binstrs bsti))))] in *.
      2: { inversion CORR_BLOCK. subst. inversion H3. subst.
           subst igt. inversion H1; vauto. 
           subst. subst addr. f_equal. f_equal.
           symmetry. apply SAME_STRUCT_PREF.
           eapply correction_same_struct; eauto. }
      rename igt into igt0. remember (Instr.ifgoto e (length (flatten (firstn n (binstrs bsti))))) as igt. 
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some igt = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc igt [igt] 0 _ bsti sti); eauto.
        Unshelve. 2, 3: eauto. 
        rewrite Nat.add_0_r. auto. }
      red in BLOCK_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try (subst igt; discriminate). 
      rewrite EQ in *. subst instr. 
      
      forward eapply (@every_instruction_compiled (instrs sto) (binstrs bsti)) as COMP; eauto. 
      destruct COMP as [[COMP NOT_IGT]| COMP]. 
      { subst igt0. vauto. }
      desc. inversion COMP. inversion COMP0. subst. clear COMP. 
      (* desc. inversion COMP0. subst. *)
      replace expr with cond in * by congruence. replace shift with addr in * by congruence. clear EQ.  
      set (sto' :=
             {| instrs := instrs sto;
                pc := if Const.eq_dec (RegFile.eval_expr (regf sto) cond) 0 then pc sto + 1 else addr0;
                G := G sto;
                regf := regf sto;
                depf := depf sto;
                ectrl := DepsFile.expr_deps (depf sto) cond ∪₁ ectrl sto;
                eindex := eindex sto |}).
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }

      (* assert (RegFile.eval_lexpr (regf sto) loc = RegFile.eval_lexpr (regf sti) loc) as LEXPR_SAME. *)
      (* { eapply INSTR_LEXPR_HELPER; eauto; [red; splits; vauto| vauto]. } *)
      (* assert (DepsFile.lexpr_deps (depf sto) loc = DepsFile.lexpr_deps (depf sti) loc) as LEXPR_DEPS_SAME. *)
      (* { eapply INSTR_LEXPR_DEPS_HELPER; eauto; [red; splits; vauto| vauto]. } *)
      assert (RegFile.eval_expr (regf sto) cond = RegFile.eval_expr (regf sti) cond) as EXPR_SAME.
      { eapply INSTR_EXPR_HELPER; eauto. vauto. }

      assert (DepsFile.expr_deps (depf sto) cond = DepsFile.expr_deps (depf sti) cond) as EXPR_DEPS_SAME.
      { eapply INSTR_EXPR_DEPS_HELPER; eauto. vauto. }
      (* assert (RegFile.eval_expr (regf sto) cond = RegFile.eval_expr (regf sti) cond) as VAL_SAME. *)
      (* { apply eval_expr_same; [subst sti; simpl; auto| ]. *)
      (*   forward eapply exchange_reg_dedicated as ERD.  *)
      (*   { exists (instrs sto). red. eexists. split; eauto. *)
      (*     red. eauto. } *)
      (*   { Unshelve. 2: exact igt. eapply nth_error_In. *)
      (*     replace (flatten (binstrs bsti)) with (instrs sti); eauto. *)
      (*     subst sti. vauto. } *)
      (*   simpl in ERD. intuition. } *)

      exists sto'. splits.
      { red. exists []. red. splits; [subst; simpl; auto| ].
                
        exists (Instr.ifgoto cond addr0). exists 0. splits; eauto.
        {  subst igt0. congruence. } 
        pose proof (@Oif_ tid [] sto sto' (Instr.ifgoto cond addr0) 0 cond addr0) as OMM_STEP.
        rewrite EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto.
        2: { subst sto'. simpl. congruence. }
        destruct (Const.eq_dec (RegFile.eval_expr (regf sti) cond)) eqn:ICOND.
        { subst sto'. simpl. rewrite EXPR_SAME.  rewrite ICOND. auto. }
        subst sto'. simpl. rewrite EXPR_SAME, ICOND. auto. }
      red. 
      splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME.
        red. eexists. eauto. }
      { subst sto'. simpl.
        rewrite EXPR_SAME.
        destruct (Const.eq_dec (RegFile.eval_expr (regf sti) cond) 0) eqn:OCOND.
        { cut (bpc bsti' = bpc bsti + 1); [ congruence| auto].
          subst sti'. subst sti. simpl in UPC.
          forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti') _ AT_BLOCK); eauto. 
          { eapply COMPILED_NONEMPTY. red. eexists; eauto. }
          simpl. simpl in UPC. congruence. }
        subst sti'. simpl in UPC. inversion H2.
        rewrite <- UPC in H0. eapply NONEMPTY_PREF.
        { eapply COMPILED_NONEMPTY. red. eexists; eauto. }
        { congruence. }
        { replace (length (binstrs bsti)) with (length (instrs sto)).  
          { eapply compilation_addresses_restricted; eauto. }
          apply compilation_same_length. auto. }
        omega. } 
      { subst sto'. simpl. replace (bG bsti') with (G sti'); [| vauto ].
        rewrite UG. replace (G sti) with (bG bsti); [| vauto ]. auto. }
      { subst sto'. simpl. replace (bregf bsti') with (regf sti'); [| vauto ].
        ins. rewrite UREGS. subst sti. simpl. apply MM_SIM2. auto. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. rewrite UDEPS. ins.
        subst sti. simpl. auto. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. rewrite UECTRL. rewrite EXPR_DEPS_SAME. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
  Qed. 


End PairStep.  