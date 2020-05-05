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

  Ltac unfold_clear_updated :=
    repeat
      match goal with
      | H1: ?S1 ≡₁ ?S2 ∪₁ ?S', H2: ?S2 ≡₁ ?S'' ∪₁ ?S''' |- _
        => rewrite H2 in H1; try rewrite H1; clear H1
      | H1: ?R1 ≡ ?R2 ∪ ?R', H2: ?R2 ≡ ?R'' ∪ ?R''' |- _
        => rewrite H2 in H1; try rewrite H1; clear H1
      | H: ?eset ≡₁ ?eset' |- _ => try rewrite H; clear H
      | H: ?erel ≡ ?erel' |- _ => try rewrite H; clear H
      end.
  
  Ltac expand_sets_only := try rewrite !set_inter_union_r; remove_emptiness; try rewrite !set_inter_union_l; remove_emptiness. 
  Ltac expand_rels := try rewrite !seq_union_l; remove_emptiness; try rewrite !seq_union_r; try expand_sets_only. 
  Ltac by_IH IH := red in IH; desc; vauto. 


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

  Lemma sim_lab_extension k tid sto sti sto' sti' (new_lbl: label)
        (SBL: same_behavior_local (G sto) (G sti))
        (EI_BOUND: E (G sti) ⊆₁ (fun x : actid => index x < eindex sti))
        (INDEX_EQ: eindex sto = eindex sti)        
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
    DepsFile.lexpr_deps (depf sto) lexpr ≡₁ DepsFile.lexpr_deps (depf sti) lexpr ∩₁ (RWO (bG bsti)).
  Proof. 
    red in MM_SIM. desc.
    replace (bG bsti) with (G sti) by vauto. 
    eapply eval_instr_lexpr_deps; eauto. 
    { exists (instrs sto). red. unfold is_thread_compiled_with.
      eexists. eauto. }
    { replace (regf sti) with (bregf bsti); vauto. }
    eapply nth_error_In. replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto.
  Qed.
  
  Lemma INSTR_EXPR_DEPS_HELPER sto bsti (MM_SIM: mm_similar_states sto bsti)
        sti (BST2ST: sti = bst2st bsti) instr n (INSTR: Some instr = nth_error (instrs sti) n) expr (EXPR_OF: expr_of expr instr):
    DepsFile.expr_deps (depf sto) expr ≡₁ DepsFile.expr_deps (depf sti) expr ∩₁ RWO (bG bsti).
  Proof. 
    red in MM_SIM. desc.
    replace (bG bsti) with (G sti) by vauto. 
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

   
  Lemma ectrl_bound_inter st tid ind
        (WFT: wf_thread_state tid st) (IND: ind >= eindex st):
     ectrl st ∩₁ eq (ThreadEvent tid ind) ≡₁ ∅.
  Proof. 
    split; [| basic_solver]. rewrite (wft_ectrlE WFT).
    (* TODO: generalize E_bound_inter *)
    red. ins. red in H. desc. 
    destruct WFT. specialize (acts_rep _ H). desc.
    subst. inversion H0. omega. 
  Qed.

  Lemma deps_bound_inter_reg st tid reg ind
        (WFT: wf_thread_state tid st) (IND: ind >= eindex st):
    depf st reg ∩₁ eq (ThreadEvent tid ind) ≡₁ ∅.
  Proof. 
    (* TODO: generalize E_bound_inter *)
    split; [| basic_solver]. 
    rewrite (wft_depfE WFT).
    red. ins. red in H. desc. 
    destruct WFT. specialize (acts_rep _ H). desc.
    subst. inversion H0. omega.
  Qed. 

  Lemma lexpr_deps_bound_inter st tid lexpr ind
        (WFT: wf_thread_state tid st) (IND: ind >= eindex st):
     DepsFile.lexpr_deps (depf st) lexpr ∩₁ eq (ThreadEvent tid ind) ≡₁ ∅.
  Proof.
    split; [| basic_solver].
    unfold DepsFile.lexpr_deps. destruct lexpr; [basic_solver| ].
    unfold DepsFile.val_deps. destruct r; [basic_solver| ].
    unfold RegFun.find. rewrite deps_bound_inter_reg; auto. 
  Qed.

  Lemma expr_deps_bound_inter st tid expr ind (WFT: wf_thread_state tid st)
        (IND: ind >= eindex st):
     DepsFile.expr_deps (depf st) expr ∩₁ eq (ThreadEvent tid ind) ≡₁ ∅.
  Proof.
    split; [| basic_solver].
    unfold DepsFile.expr_deps. destruct expr.
    - unfold DepsFile.val_deps. destruct val; [basic_solver| ].
      unfold RegFun.find. rewrite deps_bound_inter_reg; auto.
    - unfold DepsFile.val_deps. destruct op0; [basic_solver| ].
      unfold RegFun.find. rewrite deps_bound_inter_reg; auto.
    - rewrite set_inter_union_l.
      unfold DepsFile.val_deps. destruct op1, op2.
      + basic_solver.
      + unfold RegFun.find. rewrite deps_bound_inter_reg; auto. basic_solver. 
      + unfold RegFun.find. rewrite deps_bound_inter_reg; auto. basic_solver.
      + unfold RegFun.find. rewrite !deps_bound_inter_reg; auto. basic_solver.  
  Qed.

  
  Ltac discr_intra_body := (erewrite ectrl_bound_inter; [| vauto | omega]) || (erewrite deps_bound_inter_reg; [| vauto | omega]) || (erewrite lexpr_deps_bound_inter; [| vauto | omega]) || (erewrite expr_deps_bound_inter; [| vauto | omega]). 
  Ltac discr_intra := discr_intra_body || (rewrite comm_helper; discr_intra_body). 

  
  (* E is folded because many lemmas use 'In e acts_set' instead of E*)
  Ltac discr_dom DOM st := rewrite DOM; fold (E (G st));
                           rewrite !seqA; repeat seq_rewrite <- id_inter;
                           simplify_updated_sets;
                           repeat seq_rewrite id_inter;
                           rewrite !seqA; seq_rewrite <- DOM.

  Lemma progs_positions PO bsti BPI0
    (COMPILED: Forall2 is_instruction_compiled PO BPI0)
    (CORRECTED: Forall2 (block_corrected BPI0) BPI0 (binstrs bsti))
    (IN_PROG: bpc bsti < length (binstrs bsti)):
    exists oinstr block block0, 
      ⟪OINSTR: Some oinstr = nth_error PO (bpc bsti) ⟫/\
      ⟪BLOCK: Some block = nth_error (binstrs bsti) (bpc bsti) ⟫/\
      ⟪BLOCK0: Some block0 = nth_error BPI0 (bpc bsti) ⟫/\
      ⟪COMP: is_instruction_compiled oinstr block0 ⟫/\
      ⟪CORR: block_corrected BPI0 block0 block ⟫.
  Proof.
    apply nth_error_Some, OPT_VAL in IN_PROG. destruct IN_PROG as [block BLOCK].
    assert (exists block0, Some block0 = nth_error BPI0 (bpc bsti)) as [block0 BLOCK0].
    { apply OPT_VAL. apply nth_error_Some.
      replace (length BPI0) with (length (binstrs bsti)).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length; eauto. } 
    assert (exists oinstr, Some oinstr = nth_error PO (bpc bsti)) as [oinstr OINSTR]. 
    { apply OPT_VAL. apply nth_error_Some.        
      replace (length PO) with (length BPI0).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length; eauto. }
    repeat eexists; splits; eauto; eapply Forall2_index; eauto. 
  Qed.

  Lemma SEQ_EQV_CROSS {A: Type} (S1 S2 S3 S4: A -> Prop):
    ⦗S1⦘ ⨾ (S2 × S3) ⨾ ⦗S4⦘ ≡ (S1 ∩₁ S2) × (S3 ∩₁ S4). 
  Proof. ins. basic_solver. Qed.
  
  Variable bsti bsti': block_state.
  Notation "'sti'" := (bst2st bsti) (at level 1). 
  Notation "'sti''" := (bst2st bsti') (at level 1). 
    
  Lemma pair_step sto (MM_SIM: mm_similar_states sto bsti)
        tid (OSEQ_STEP: omm_block_step tid bsti bsti')
        (BPC'_BOUND: bpc bsti' <= length (binstrs bsti))
        (BLOCK_REACH: (block_step tid)＊ (binit (binstrs bsti)) bsti):
    exists sto', Ostep tid sto sto' /\ mm_similar_states sto' bsti'.
  Proof.
    pose proof (block_step_nonterminal (bs_extract OSEQ_STEP)) as BST_NONTERM.
    assert (is_thread_block_compiled (instrs sto) (binstrs bsti)) as ITBC by (red in MM_SIM; desc; auto).
    assert (binstrs bsti = binstrs bsti') as BINSTRS_SAME by (cdes OSEQ_STEP; auto). 
    red in ITBC. desc.
    forward eapply progs_positions as PP; eauto. desc.
    (* clear ITBC ITBC0.  *)
    pose proof (@reach_with_blocks bsti sti tid eq_refl BLOCK_REACH) as [n_steps REACH]. 
    assert (wf_thread_state tid sti) as WFT.
    { apply wf_thread_state_steps with (s := init (instrs sti));
        [apply wf_thread_state_init| ].
      apply crt_num_steps. eauto. } 
    assert (forall i block_i, Some block_i = nth_error block i -> Some block_i = nth_error (instrs sti) (pc sti + i)) as BLOCK_CONTENTS. 
    { ins. forward eapply (@near_pc block_i block i H bsti); eauto. }
    assert (forall (LEN1: length block = 1) (OBS: omm_block_step tid bsti bsti'),
               step tid sti sti') as STEP1. 
    { ins. red in OSEQ_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- BLOCK in AT_BLOCK. inversion AT_BLOCK. subst. simpl in *.
      rewrite LEN1 in BLOCK_STEP0. 
      apply (same_relation_exp (seq_id_l (step tid))). auto. }
    assert (forall (LEN2: length block = 2) (OBS: omm_block_step tid bsti bsti'),
               exists sti'', step tid sti sti'' /\ step tid sti'' sti') as STEP2. 
    { ins. red in OSEQ_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- BLOCK in AT_BLOCK. inversion AT_BLOCK. subst. simpl in *.
      rewrite LEN2 in BLOCK_STEP0. replace 2 with (1 + 1) in BLOCK_STEP0 by omega. 
      rewrite <- (same_relation_exp (pow_nm 1 1 (step tid))) in BLOCK_STEP0.
      red in BLOCK_STEP0. desc. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP0.
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP1.
      eexists. splits; eauto. }
    assert (forall sti1 sti2 instr pos
              (POS: Some instr = nth_error (instrs sti1) pos)
              (POS_EQ: pos = pc sti1),
               step tid sti1 sti2 ->
               (instrs sti1 = instrs sti2 /\ exists lbls, istep_ tid lbls sti1 sti2 instr)) as ISTEP1.
    { ins. do 2 (red in H; desc).
      subst pos. simpl in ISTEP. rewrite <- POS in ISTEP.
      inversion ISTEP. subst. split; eauto. }
    Ltac infer_istep_ ISTEP_ instr II := inversion ISTEP_; subst instr; try discriminate; inversion II; subst; clear II.
    assert (forall (UPC: pc sti' = pc sti + length block),
               pc sto + 1 = bpc bsti') as OPC'.
    { ins.
      forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti') _ BLOCK); eauto. 
      { cdes MM_SIM. eapply COMPILED_NONEMPTY; eauto. }
      { congruence. }
      ins. rewrite H. f_equal. by_IH MM_SIM. }

    assert (forall sto' (EXT: extends_with tid 0 (lab (G sti') (ThreadEvent tid (eindex sto + 0))) sto sto') (INDEX': eindex sti' = eindex sti + 1)
              (ADD: exists new_lbl ddata daddr dctrl drmw_dep,
    G sti' = add (G sti) tid (eindex sti) new_lbl ddata daddr dctrl drmw_dep),
               forall x, E (G sto') x -> lab (G sto') x = lab (bG bsti') x) as EXT_LAB_SIM.
    { ins. 
      forward eapply (@sim_lab_extension 0 tid sto sti sto' sti'); eauto.
      { cdes MM_SIM. auto. }
      { apply (@E_bounded n_steps tid sti); eauto. }
      { by_IH MM_SIM. }
      desc. 
      replace (0 + 1) with 1 by omega. rewrite (same_relation_exp (pow_unit _)).
      red. eexists. red. split; [| simpl; omega]. 
      rewrite Nat.add_0_r. desc. repeat eexists; eauto. }
    (* assert (forall sto' (EXT: extends_with tid 0 (lab (G sti') (ThreadEvent tid (eindex sto + 0))) sto sto') (INDEX': eindex sti' = eindex sti + 1) *)
    (*           (ADD: exists new_lbl ddata daddr dctrl drmw_dep, *)
    (* G sti' = add (G sti) tid (eindex sti) new_lbl ddata daddr dctrl drmw_dep), *)
    (*            forall x, E (G sto') x -> lab (G sto') x = lab (bG bsti') xhhh) as EXT_LAB_SIM2. *)
    (* { ins.  *)
    (*   forward eapply (@sim_lab_extension 0 tid sto sti sto' sti'); eauto. *)
    (*   { cdes MM_SIM. auto. } *)
    (*   { apply (@E_bounded n_steps tid sti); eauto. } *)
    (*   { by_IH MM_SIM. } *)
    (*   desc.  *)
    (*   replace (0 + 1) with 1 by omega. rewrite (same_relation_exp (pow_unit _)). *)
    (*   red. eexists. red. split; [| simpl; omega].  *)
    (*   rewrite Nat.add_0_r. desc. repeat eexists; eauto. } *)

    
    Ltac replace_bg_rels bst st := replace (bG bst) with (G st) by auto; replace (beindex bst) with (eindex st) by auto; replace (bectrl bst) with (ectrl st) by auto; replace (bdepf bst) with (depf st) by auto. 
    Ltac expand_intra sto' UG bst st :=
        subst sto'; simpl in *; unfold_clear_updated;
        rewrite UG; unfold add; simpl; remove_emptiness;
        replace_bg_rels bst st; rewrite RESTR_EXPAND; expand_rels. 
    
    inversion COMP; subst; simpl in *. 
    - assert (block = [ld]).
      { subst ld. inversion CORR. inversion H3. subst. inversion H1. auto. }
      subst block. simpl in *.
      specialize (BLOCK_CONTENTS 0 ld eq_refl). 
      apply (STEP1 eq_refl) in OSEQ_STEP.
      apply (@ISTEP1 sti sti' ld _ BLOCK_CONTENTS) in OSEQ_STEP; [| simpl; omega].
      destruct OSEQ_STEP as [SAME_INSTRS [lbls ISTEP_]].
      infer_istep_ ISTEP_ ld II. 

      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto)
                         (Aload false Orlx (RegFile.eval_lexpr (regf sto) lexpr) val) ∅
                         (DepsFile.lexpr_deps (depf sto) lexpr) (ectrl sto) ∅;
                         eindex := eindex sto + 1;
                regf := RegFun.add reg val (regf sto);
                depf := RegFun.add reg (eq (ThreadEvent tid (eindex sto))) (depf sto);
                ectrl := ectrl sto |}).

      exists sto'. splits.
      { red. exists [Aload false Orlx (RegFile.eval_lexpr (regf sto) lexpr) val].
        red. splits; [subst; simpl; auto| ].
        exists (Instr.load Orlx reg lexpr). exists 0.
        splits.
        { replace (pc sto) with (bpc bsti); [auto| cdes MM_SIM; vauto]. }
        pose proof (@Oload tid [Aload false Orlx (RegFile.eval_lexpr (regf sto) lexpr) val] sto sto' (Instr.load Orlx reg lexpr) 0 Orlx reg lexpr val (RegFile.eval_lexpr (regf sto) lexpr)) as OMM_STEP.
        specialize_full OMM_STEP; auto.
        all: subst sto'; simpl; repeat f_equal; omega. }
      forward eapply (@E_ADD (G sti) (G sti')) as E_SPLITS;
        [repeat eexists; eauto| ].          
      forward eapply (@RWO_ADD sti sti') as RWO_SPLITS; eauto.
      forward eapply (@E_ADD (G sto) (G sto')) as EGO'; [repeat eexists; eauto| ].
      assert (EINDEX_EQ: eindex sto = eindex sti).
      { cdes MM_SIM. vauto. }
      assert (ECTRL_EQ: ectrl sto ≡₁ ectrl sti ∩₁ (RWO (G sti))).
      { cdes MM_SIM. vauto. }
      forward eapply INSTR_LEXPR_HELPER as LEXPR_SAME; [vauto| vauto | vauto | vauto| ].
      forward eapply INSTR_LEXPR_DEPS_HELPER as LEXPR_DEPS_SAME; [vauto| vauto | vauto | vauto| ].
      simpl in RWO_SPLITS.
      cdes MM_SIM.
      red. splits.
      { subst sto'. simpl. congruence. }
      { subst sto'. simpl. apply OPC'; auto. }
      { red.        
        splits.
        { unfold_clear_updated. expand_rels.
          rewrite EINDEX_EQ. simpl.
          replace_bg_rels bsti sti. (* expand_intra sto' UG.  *)
          simplify_updated_sets. 
          apply set_equiv_union; [by_IH MM_SIM2 | basic_solver]. }
        { apply EXT_LAB_SIM; vauto; [| repeat eexists; eauto]. 
          red. split. 
          2: { subst sto'. simpl. omega. }
          rewrite Nat.add_0_r.
          subst sto'. simpl.
          replace (lab (bG bsti') (ThreadEvent tid (eindex sto))) with (Aload false Orlx (RegFile.eval_lexpr (regf sto) lexpr) val).
          { simpl. repeat eexists; eauto. }
          simpl in *. rewrite UG, EINDEX_EQ. simpl. rewrite upds.
          erewrite INSTR_LEXPR_HELPER; vauto. }
        { subst sto'. simpl. by_IH MM_SIM2. }
        { expand_intra sto' UG bsti sti. 
          discr_dom (wft_dataE WFT) sti.
          rewrite <- restr_relE. by_IH MM_SIM2. }
        { expand_intra sto' UG bsti sti.  
          discr_dom (wft_ctrlE WFT) sti.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets.
          discr_intra. remove_emptiness. 
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | basic_solver]. }
        { expand_intra sto' UG bsti sti. 
          discr_dom (wft_addrE WFT) sti.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets. 
          discr_intra. remove_emptiness.
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | basic_solver]. }
        subst sto'. simpl in *. remove_emptiness. by_IH MM_SIM2. }
      { ins. rewrite UREGS.
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg); auto.
        unfold RegFun.find. apply MM_SIM3. auto. }
      { subst sto'. simpl. ins. rewrite UDEPS. 
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg).
        { unfold_clear_updated. replace_bg_rels bsti sti. expand_rels.
          simplify_updated_sets. rewrite EINDEX_EQ. auto. }
        unfold RegFun.find.
        unfold_clear_updated. replace_bg_rels bsti sti. expand_rels.
        discr_intra. remove_emptiness.
        apply MM_SIM4. auto. }
      { subst sto'. simpl in *. unfold_clear_updated. rewrite UECTRL. 
        expand_rels. replace_bg_rels bsti sti. discr_intra. remove_emptiness. auto. }
      subst sto'. simpl. replace (beindex bsti') with (eindex sti') by auto.
      congruence. 
    - assert (block = [f; st]).
      { subst f st. inversion CORR. inversion H3. subst. inversion H8.
        subst. inversion H1. inversion H6. vauto. }
      subst block. simpl in *.
      pose proof (BLOCK_CONTENTS 0 f eq_refl) as BLOCK_CONTENTS0. 
      pose proof (BLOCK_CONTENTS 1 st eq_refl) as BLOCK_CONTENTS1. 
      apply (STEP2 eq_refl) in OSEQ_STEP.
      desc. rename sti'' into sti_.
      assert ((step tid) ^^ (n_steps + 1) (init (instrs sti_)) sti_) as REACH1. 
      { rewrite <- (same_relation_exp (pow_nm n_steps 1 (step tid))).
        red. exists sti. splits. 
        { erewrite <- (@steps_same_instrs sti); vauto. }
        rewrite (same_relation_exp (pow_unit _)). auto. }

      apply (@ISTEP1 sti sti_ f _ BLOCK_CONTENTS0) in OSEQ_STEP; [| simpl; omega].
      destruct OSEQ_STEP as [SAME_INSTRS [lbls ISTEP0_]].
      infer_istep_ ISTEP0_ f II. 
      replace (flatten (binstrs bsti)) with (instrs sti_) in BLOCK_CONTENTS1. 
      apply (@ISTEP1 sti_ sti' st _ BLOCK_CONTENTS1) in OSEQ_STEP0; [| vauto]. 
      destruct OSEQ_STEP0 as [SAME_INSTRS1 [lbls1 ISTEP1_]].
      infer_istep_ ISTEP1_ st II. 
      
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto;
                G := G sto;
                eindex := eindex sto;
                regf := regf sto;
                depf := depf sto;
                ectrl := ectrl sto |}).
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto' + 1;
                G := add (G sto') tid (eindex sto' + 1) (Astore Xpln Orlx (RegFile.eval_lexpr (regf sti_) lexpr) (RegFile.eval_expr (regf sti_) expr))
                         (DepsFile.expr_deps (depf sto') expr)
                         (DepsFile.lexpr_deps (depf sto') lexpr) (ectrl sto') ∅;
                eindex := eindex sto' + 2;
                regf := regf sto';
                depf := depf sto';
                ectrl := ectrl sto' |}).
      assert (Some (Instr.store Orlx lexpr expr) = nth_error (instrs sti) (pc sti + 1)) as ST_POS.
      { rewrite BLOCK_CONTENTS1. f_equal. auto. } 
      exists sto''. splits.
      { red. exists [Astore Xpln Orlx (RegFile.eval_lexpr (regf sti_) lexpr)
                       (RegFile.eval_expr (regf sti_) expr)].
        red. splits; [subst; simpl; auto| ].
        exists (Instr.store Orlx lexpr expr). exists 1. splits.
        { replace (pc sto) with (bpc bsti); [auto| cdes MM_SIM; vauto]. }
        pose proof (@Ostore tid [Astore Xpln Orlx (RegFile.eval_lexpr (regf sti_) lexpr) (RegFile.eval_expr (regf sti_) expr)] sto sto'' (Instr.store Orlx lexpr expr) 1 Orlx lexpr expr (RegFile.eval_lexpr (regf sti_) lexpr) (RegFile.eval_expr (regf sti_) expr)) as OMM_STEP.
        specialize_full OMM_STEP; auto.
        { subst sto'' sto'. rewrite UREGS. symmetry.
          eapply INSTR_LEXPR_HELPER with (instr := (Instr.store Orlx lexpr expr)); vauto. }
        { symmetry. rewrite UREGS. eapply INSTR_EXPR_HELPER with (instr := (Instr.store Orlx lexpr expr)); vauto. }
        subst sto'' sto'. simpl. omega. }
      forward eapply (@E_ADD (G sti_) (G sti')) as E_SPLITS1;
        [repeat eexists; eauto| ].
      forward eapply (@E_ADD (G sti) (G sti_)) as E_SPLITS;
        [repeat eexists; eauto| ].      
      forward eapply (@RWO_ADD sti_ sti') as RWO_SPLITS1; eauto.
      forward eapply (@RWO_ADD sti sti_) as RWO_SPLITS; eauto.
      forward eapply (@E_ADD (G sto) (G sto'')) as EGO''; [repeat eexists; eauto| ].
      cdes MM_SIM. 
      pose proof INSTR_LEXPR_HELPER as LEXPR_SAME. specialize LEXPR_SAME with (instr := (Instr.store Orlx lexpr expr)). specialize_full LEXPR_SAME; vauto. 
      pose proof INSTR_LEXPR_DEPS_HELPER as LEXPR_DEPS_SAME. specialize LEXPR_DEPS_SAME with (instr := (Instr.store Orlx lexpr expr)). specialize_full LEXPR_DEPS_SAME; vauto. 
      pose proof INSTR_EXPR_HELPER as EXPR_SAME. specialize EXPR_SAME with (instr := (Instr.store Orlx lexpr expr)). specialize_full EXPR_SAME; vauto. 
      simpl in RWO_SPLITS, RWO_SPLITS1.
      red. splits.
      { subst sto'. simpl. congruence. }
      { simpl. apply OPC'.
        replace (length (flatten (firstn (bpc bsti) (binstrs bsti)))) with (pc sti) by auto.
        replace (length (flatten (firstn (bpc bsti') (binstrs bsti')))) with (pc sti') by auto.
        omega. }
      { red. 
        splits.
        { unfold_clear_updated. rewrite UINDEX.
          simpl. replace_bg_rels bsti sti. expand_rels. simplify_updated_sets.  
          apply set_equiv_union; [by_IH MM_SIM2 | basic_solver]. }
        {
          (* TODO: unify with the Rrlx case *)
        forward eapply (@sim_lab_extension 1 tid sto sti sto'' sti'); eauto.
        { apply (@E_bounded n_steps tid sti); eauto. }
        { red. split. 
          2: { subst sto''. simpl. omega. } 
          replace (lab (G sti') (ThreadEvent tid (eindex sto + 1))) with (Astore Xpln Orlx (RegFile.eval_lexpr (regf sti_) lexpr) (RegFile.eval_expr (regf sti_) expr)).
          2: { rewrite UG0, UG. simpl.
               replace (eindex sti_) with (eindex sto + 1).
               2: { rewrite UINDEX. f_equal. by_IH MM_SIM2. }
               rewrite upds. auto. }
          repeat eexists. }
        simpl. red. exists sti_. split.
        { red. exists sti. split; [red; auto|]. red. eexists. red.
          rewrite Nat.add_0_r. split; auto. repeat eexists. eauto. }
        red. eexists. red. rewrite Nat.add_0_r. split; auto.
        repeat eexists. eauto. }
        { subst sto'. simpl. by_IH MM_SIM2. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UDEPS. 
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          rewrite !SEQ_EQV_CROSS.
          discr_dom (wft_dataE WFT) sti.
          rewrite comm_helper. discr_intra_body. remove_emptiness.  
          rewrite <- restr_relE.
          apply union_more; [by_IH MM_SIM2| ].
          apply cross_more.
          { rewrite eval_instr_expr_deps with (PI := instrs sti) (instr := (Instr.store Orlx lexpr expr)); vauto.
            { rewrite set_interC. eauto. }
            { auto. }
            eapply nth_error_In. simpl. eauto. }
          simpl. rewrite MM_SIM6. auto. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UECTRL.
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          expand_rels. discr_dom (wft_ctrlE WFT) sti.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets.
          discr_intra. remove_emptiness. 
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | ].
          rewrite MM_SIM6. simpl. basic_solver. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UDEPS. 
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          discr_dom (wft_addrE WFT) sti.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets. 
          discr_intra. remove_emptiness.
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | ].
          rewrite MM_SIM6. simpl. basic_solver. }
        subst sto'. simpl in *. remove_emptiness. by_IH MM_SIM2. }
      { ins. rewrite UREGS0, UREGS.
        apply MM_SIM3. auto. }
      { subst sto'. simpl. ins. rewrite UDEPS0, UDEPS.
        unfold_clear_updated. expand_rels. rewrite UINDEX.
        replace_bg_rels bsti sti. discr_intra. remove_emptiness. 
        apply MM_SIM4. auto. }
      { subst sto'' sto'. simpl in *. unfold_clear_updated.
        rewrite UECTRL0, UECTRL, UINDEX.
        expand_rels. replace_bg_rels bsti sti. discr_intra. remove_emptiness.
        auto. }
      subst sto'' sto'. simpl. replace_bg_rels bsti' sti'. 
      rewrite UINDEX0, UINDEX. simpl. omega. 
    - assert (block = [f; ld]).
      { subst f ld. inversion CORR. inversion H3. subst. inversion H8.
        subst. inversion H1. inversion H6. vauto. }
      subst block. simpl in *.
      pose proof (BLOCK_CONTENTS 0 f eq_refl) as BLOCK_CONTENTS0. 
      pose proof (BLOCK_CONTENTS 1 ld eq_refl) as BLOCK_CONTENTS1. 
      apply (STEP2 eq_refl) in OSEQ_STEP.
      desc. rename sti'' into sti_.
      assert ((step tid) ^^ (n_steps + 1) (init (instrs sti_)) sti_) as REACH1. 
      { rewrite <- (same_relation_exp (pow_nm n_steps 1 (step tid))).
        red. exists sti. splits. 
        { erewrite <- (@steps_same_instrs sti); vauto. }
        rewrite (same_relation_exp (pow_unit _)). auto. }

      apply (@ISTEP1 sti sti_ f _ BLOCK_CONTENTS0) in OSEQ_STEP; [| simpl; omega].
      destruct OSEQ_STEP as [SAME_INSTRS [lbls ISTEP0_]].
      infer_istep_ ISTEP0_ f II. 
      replace (flatten (binstrs bsti)) with (instrs sti_) in BLOCK_CONTENTS1. 
      apply (@ISTEP1 sti_ sti' ld _ BLOCK_CONTENTS1) in OSEQ_STEP0; [| vauto]. 
      destruct OSEQ_STEP0 as [SAME_INSTRS1 [lbls1 ISTEP1_]].
      infer_istep_ ISTEP1_ ld II. 
      
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto + 1) (Aload false Osc (RegFile.eval_lexpr (regf sti_) lexpr) val)
                         ∅
                         (DepsFile.lexpr_deps (depf sto) lexpr) (ectrl sto) ∅;
                eindex := eindex sto + 2;
                regf := RegFun.add reg val (regf sto);
                depf := RegFun.add reg (eq (ThreadEvent tid (eindex sto + 1))) (depf sto);
                ectrl := ectrl sto |}).
      assert (Some (Instr.load Osc reg lexpr) = nth_error (instrs sti) (pc sti + 1)) as ST_POS.
      { rewrite BLOCK_CONTENTS1. f_equal. auto. } 
      exists sto''. splits.
      { red. exists [(Aload false Osc (RegFile.eval_lexpr (regf sti_) lexpr) val)].
        red. splits; [subst; simpl; auto| ].
        exists (Instr.load Osc reg lexpr). exists 1. splits.
        { replace (pc sto) with (bpc bsti); [auto| cdes MM_SIM; vauto]. }
        pose proof (@Oload tid [Aload false Osc (RegFile.eval_lexpr (regf sti_) lexpr) val] sto sto'' (Instr.load Osc reg lexpr) 1 Osc reg lexpr val (RegFile.eval_lexpr (regf sto) lexpr)) as OMM_STEP.
        specialize_full OMM_STEP; auto.
        { subst sto''. rewrite UREGS. symmetry.
          erewrite INSTR_LEXPR_HELPER with (instr := (Instr.load Osc reg lexpr)); vauto. }
        { subst sto''. simpl. rewrite UREGS.
          do 2 f_equal. symmetry.  
          eapply INSTR_LEXPR_HELPER with (instr := (Instr.load Osc reg lexpr)); vauto. }
        subst sto''. simpl. omega. }
      forward eapply (@E_ADD (G sti_) (G sti')) as E_SPLITS1;
        [repeat eexists; eauto| ].
      forward eapply (@E_ADD (G sti) (G sti_)) as E_SPLITS;
        [repeat eexists; eauto| ].      
      forward eapply (@RWO_ADD sti_ sti') as RWO_SPLITS1; eauto.
      forward eapply (@RWO_ADD sti sti_) as RWO_SPLITS; eauto.
      forward eapply (@E_ADD (G sto) (G sto'')) as EGO''; [repeat eexists; eauto| ].
      cdes MM_SIM. 
      pose proof INSTR_LEXPR_HELPER as LEXPR_SAME. specialize LEXPR_SAME with (instr := (Instr.load Osc reg lexpr)). specialize_full LEXPR_SAME; vauto. 
      pose proof INSTR_LEXPR_DEPS_HELPER as LEXPR_DEPS_SAME. specialize LEXPR_DEPS_SAME with (instr := (Instr.load Osc reg lexpr)). specialize_full LEXPR_DEPS_SAME; vauto. 
      simpl in RWO_SPLITS, RWO_SPLITS1.
      red. splits.
      { subst sto''. simpl. congruence. }
      { simpl. apply OPC'.
        replace (length (flatten (firstn (bpc bsti) (binstrs bsti)))) with (pc sti) by auto.
        replace (length (flatten (firstn (bpc bsti') (binstrs bsti')))) with (pc sti') by auto.
        omega. }
      { red. 
        splits.
        { unfold_clear_updated. rewrite UINDEX.
          simpl. replace_bg_rels bsti sti. expand_rels. simplify_updated_sets.  
          apply set_equiv_union; [by_IH MM_SIM2 | basic_solver]. }
        {
          (* TODO: unify with the Rrlx case *)
        forward eapply (@sim_lab_extension 1 tid sto sti sto'' sti'); eauto.
        { apply (@E_bounded n_steps tid sti); eauto. }
        { red. split. 
          2: { subst sto''. simpl. omega. } 
          replace (lab (G sti') (ThreadEvent tid (eindex sto + 1))) with (Aload false Osc (RegFile.eval_lexpr (regf sti_) lexpr) val).
          2: { rewrite UG0, UG. simpl.
               replace (eindex sti_) with (eindex sto + 1).
               2: { rewrite UINDEX. f_equal. by_IH MM_SIM2. }
               rewrite upds. auto. }
          repeat eexists. }
        simpl. red. exists sti_. split.
        { red. exists sti. split; [red; auto|]. red. eexists. red.
          rewrite Nat.add_0_r. split; auto. repeat eexists. eauto. }
        red. eexists. red. rewrite Nat.add_0_r. split; auto.
        repeat eexists. eauto. }
        { subst sto''. simpl. by_IH MM_SIM2. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG. 
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          discr_dom (wft_dataE WFT) sti.
          rewrite <- restr_relE. by_IH MM_SIM2. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UECTRL.
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          expand_rels. discr_dom (wft_ctrlE WFT) sti.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets.
          discr_intra. remove_emptiness. 
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | ].
          rewrite MM_SIM6. simpl. basic_solver. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UDEPS. 
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          discr_dom (wft_addrE WFT) sti.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets. 
          discr_intra. remove_emptiness.
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | ].
          rewrite MM_SIM6. simpl. basic_solver. }
        subst sto''. simpl in *. remove_emptiness. by_IH MM_SIM2. }
      { ins. rewrite UREGS0, UREGS.
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg); auto.
        unfold RegFun.find. apply MM_SIM3. auto. }
      { subst sto''. simpl. ins. rewrite UDEPS0, UDEPS. 
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg).
        { unfold_clear_updated. replace_bg_rels bsti sti. expand_rels.
          rewrite UINDEX, MM_SIM6.
          replace_bg_rels bsti sti. simplify_updated_sets. auto. }
        unfold RegFun.find.
        unfold_clear_updated. replace_bg_rels bsti sti. expand_rels.
        rewrite UINDEX. replace_bg_rels bsti sti.
        discr_intra. remove_emptiness.
        apply MM_SIM4. auto. }
      { subst sto''. simpl in *. unfold_clear_updated.
        rewrite UECTRL0, UECTRL, UINDEX.  
        replace_bg_rels bsti sti. expand_rels.
        discr_intra. remove_emptiness. auto. }
      subst sto''. simpl. replace_bg_rels bsti' sti'. rewrite UINDEX0, UINDEX.
      simpl. omega.         
    - assert (block = [f; exc]).
      { subst f exc. inversion CORR. inversion H3. subst. inversion H8.
        subst. inversion H1. inversion H6. vauto. }
      subst block. simpl in *.
      pose proof (BLOCK_CONTENTS 0 f eq_refl) as BLOCK_CONTENTS0. 
      pose proof (BLOCK_CONTENTS 1 exc eq_refl) as BLOCK_CONTENTS1. 
      apply (STEP2 eq_refl) in OSEQ_STEP.
      desc. rename sti'' into sti_.
      assert ((step tid) ^^ (n_steps + 1) (init (instrs sti_)) sti_) as REACH1. 
      { rewrite <- (same_relation_exp (pow_nm n_steps 1 (step tid))).
        red. exists sti. splits. 
        { erewrite <- (@steps_same_instrs sti); vauto. }
        rewrite (same_relation_exp (pow_unit _)). auto. }

      apply (@ISTEP1 sti sti_ f _ BLOCK_CONTENTS0) in OSEQ_STEP; [| simpl; omega].
      destruct OSEQ_STEP as [SAME_INSTRS [lbls ISTEP0_]].
      infer_istep_ ISTEP0_ f II. 
      replace (flatten (binstrs bsti)) with (instrs sti_) in BLOCK_CONTENTS1. 
      apply (@ISTEP1 sti_ sti' exc _ BLOCK_CONTENTS1) in OSEQ_STEP0; [| vauto]. 
      destruct OSEQ_STEP0 as [SAME_INSTRS1 [lbls1 ISTEP1_]].
      infer_istep_ ISTEP1_ exc II.
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto + 2) (Astore Xpln Osc (RegFile.eval_lexpr (regf sto) loc_expr)
                 (RegFile.eval_expr (regf sto) new_expr))
                         (DepsFile.expr_deps (depf sto) new_expr)
                         (DepsFile.lexpr_deps (depf sto) loc_expr) 
                         (ectrl sto) ∅;
                eindex := eindex sto + 3;
                regf := regf sto;
                depf := depf sto; (* TODO: deal with changed depf after rmw *)
                ectrl := ectrl sto |}).
      assert (Some (Instr.update (Instr.exchange new_expr) Xpln Osc Osc
                         exchange_reg loc_expr) = nth_error (instrs sti) (pc sti + 1)) as ST_POS.
      { rewrite BLOCK_CONTENTS1. f_equal. auto. } 
      exists sto''. splits.
      { red. exists [(Astore Xpln Osc (RegFile.eval_lexpr (regf sto) loc_expr)
             (RegFile.eval_expr (regf sto) new_expr))].
        red. splits; [subst; simpl; auto| ].
        exists (Instr.store Osc loc_expr new_expr). exists 2. splits.
        { replace (pc sto) with (bpc bsti); [auto| cdes MM_SIM; vauto]. }
        pose proof (@Ostore tid [Astore Xpln Osc (RegFile.eval_lexpr (regf sto) loc_expr) (RegFile.eval_expr (regf sto) new_expr)] sto sto'' st 2 Osc loc_expr new_expr (RegFile.eval_lexpr (regf sto) loc_expr) (RegFile.eval_expr (regf sto) new_expr) Xpln) as OMM_STEP. 
        specialize_full OMM_STEP; auto.
        subst sto''. simpl. omega. }
      forward eapply (@E_ADD_RMW (G sti_) (G sti')) as E_SPLITS1;
        [repeat eexists; eauto| ].
      forward eapply (@E_ADD (G sti) (G sti_)) as E_SPLITS;
        [repeat eexists; eauto| ].      
      forward eapply (@RWO_ADD_rmw sti_ sti') as RWO_SPLITS1; eauto.
      forward eapply (@RWO_ADD sti sti_) as RWO_SPLITS; eauto.
      forward eapply (@E_ADD (G sto) (G sto'')) as EGO''; [repeat eexists; eauto| ].
      cdes MM_SIM. 
      pose proof INSTR_LEXPR_HELPER as LEXPR_SAME. specialize LEXPR_SAME with (instr := (Instr.update (Instr.exchange new_expr) Xpln Osc Osc exchange_reg loc_expr)). specialize_full LEXPR_SAME; vauto. 
      pose proof INSTR_LEXPR_DEPS_HELPER as LEXPR_DEPS_SAME. specialize LEXPR_DEPS_SAME with (instr := (Instr.update (Instr.exchange new_expr) Xpln Osc Osc exchange_reg loc_expr)). specialize_full LEXPR_DEPS_SAME; vauto. 
      assert (RegFile.eval_expr (regf sto) new_expr = RegFile.eval_expr (regf sti) new_expr) as EXPR_SAME.
      { eapply eval_rmw_expr; eauto. 
        { exists (instrs sto). red.
          unfold is_thread_compiled_with.
          eexists. eauto. }
        repeat eexists. eapply nth_error_In.
        replace (flatten (binstrs bsti)) with (instrs sti); eauto. subst. vauto. }
      (* pose proof INSTR_EXPR_HELPER as EXPR_SAME. specialize EXPR_SAME with (instr := (Instr.update (Instr.exchange new_expr) Xpln Osc Osc exchange_reg loc_expr)). *)
      (* specialize_full EXPR_SAME; vauto. *)
      (* { Unshelve. 2: exact new_expr. simpl.  *)
      simpl in RWO_SPLITS, RWO_SPLITS1.      
      red. splits.
      { subst sto''. simpl. congruence. }
      { simpl. apply OPC'.
        replace (length (flatten (firstn (bpc bsti) (binstrs bsti)))) with (pc sti) by auto.
        replace (length (flatten (firstn (bpc bsti') (binstrs bsti')))) with (pc sti') by auto.
        omega. }
      { red. 
        splits.
        { replace_bg_rels bsti' sti'.
          rewrite E_SPLITS in E_SPLITS1. rewrite E_SPLITS1. clear E_SPLITS1.
          unfold_clear_updated. rewrite UINDEX. 
          replace_bg_rels bsti sti. expand_rels. simplify_updated_sets.  
          apply set_equiv_union; [by_IH MM_SIM2 | ].
          cut (eindex sto + 2 = eindex sti + 1 + 1); [ins; basic_solver| ]. 
          simpl. omega. }
        {

        ins. rewrite UG0, UG, UINDEX. simpl.
        unfold add, acts_set in EGOx. simpl in EGOx. destruct EGOx.
        - rewrite <- H. rewrite MM_SIM6.
          replace (beindex bsti + 1 + 1) with (beindex bsti + 2) by omega.
          repeat rewrite upds. congruence. 
        - assert (E (G sti) x).
          { red in MM_SIM2. desc. red in RESTR_EVENTS. desc.
            red in RESTR_EVENTS. unfold acts_set in RESTR_EVENTS.
            apply RESTR_EVENTS in H. red in H. desc. vauto. }
          apply (hahn_subset_exp (@E_bounded n_steps tid sti REACH)) in H0. 
          repeat rewrite updo.
          2-5: red; ins; subst; simpl in H0; omega.
          replace (G sti) with (bG bsti); [| vauto ].
          red in MM_SIM2. desc. apply SAME_LAB. auto. }
        { subst sto''. simpl. by_IH MM_SIM2. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UDEPS. 
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets.
          discr_dom (wft_dataE WFT) sti.
          discr_intra. remove_emptiness.
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2| ].
          apply cross_more.
          2: { replace (eindex sti + 1 + 1) with (eindex sto + 2); [auto|]. 
               simpl. omega. }
          cdes MM_SIM2. 
          rewrite (eval_expr_deps_same sto sti); eauto.
          { basic_solver. }
          forward eapply exchange_reg_dedicated as DEDICATED. 
          { vauto. }
          { Unshelve. 2: exact (Instr.update (Instr.exchange new_expr) Xpln Osc Osc exchange_reg loc_expr). eapply nth_error_In; eauto. }
          simpl in DEDICATED. destruct new_expr.
          - destruct val; simpl; tauto.
          - simpl. destruct op0; simpl; tauto.
          - simpl. destruct op1, op2; simpl; tauto. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UECTRL.
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          expand_rels.
          assert (singl_rel_restr_eq:
                    forall (A : Type) (x y : A),
                      singl_rel x y ≡ eq x × eq y).
          { ins. basic_solver. }
          repeat rewrite singl_rel_restr_eq. 
          rewrite !SEQ_EQV_CROSS. simplify_updated_sets.
          discr_dom (wft_ctrlE WFT) sti.
          discr_intra. remove_emptiness.
          expand_sets_only. simplify_updated_sets. 
          rewrite <- restr_relE.
          apply union_more; [by_IH MM_SIM2 | ].
          replace (eindex sti + 1 + 1) with (eindex sto + 2); [basic_solver| ].
          rewrite MM_SIM6. simpl. omega. }
        { expand_intra sto'' UG0 bsti sti. rewrite UINDEX, UG, UDEPS. 
          simpl. replace_bg_rels bsti sti. remove_emptiness.
          discr_dom (wft_addrE WFT) sti.
          rewrite !SEQ_EQV_CROSS. discr_intra. remove_emptiness.
          expand_sets_only. simplify_updated_sets. 
          rewrite <- restr_relE. 
          apply union_more; [by_IH MM_SIM2 | ].
          replace (eindex sti + 1 + 1) with (eindex sto + 2); [basic_solver| ].
          rewrite MM_SIM6. simpl. omega. }
        subst sto''. simpl in *. remove_emptiness. by_IH MM_SIM2. }
      { ins. rewrite UREGS0, UREGS.
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg exchange_reg); vauto.
        unfold RegFun.find. apply MM_SIM3. auto. }
      { subst sto''. simpl. ins. rewrite UDEPS0, UDEPS. 
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg exchange_reg); vauto.
        unfold_clear_updated. replace_bg_rels bsti sti. expand_rels.
        unfold RegFun.find. rewrite UINDEX. replace_bg_rels bsti sti.
        discr_intra. remove_emptiness.
        apply MM_SIM4. auto. }
      { subst sto''. simpl in *. unfold_clear_updated.
        rewrite UECTRL0, UECTRL, UINDEX.  
        replace_bg_rels bsti sti. expand_rels.
        discr_intra. remove_emptiness. auto. }
      subst sto''. simpl. replace_bg_rels bsti' sti'. rewrite UINDEX0, UINDEX.
      simpl. omega.
    - assert (block = [asn]).
      { subst asn. inversion CORR. inversion H3. subst. inversion H1. vauto. }
      subst block. simpl in *.
      pose proof (BLOCK_CONTENTS 0 asn eq_refl) as BLOCK_CONTENTS0. 
      apply (STEP1 eq_refl) in OSEQ_STEP.
      apply (@ISTEP1 sti sti' asn _ BLOCK_CONTENTS0) in OSEQ_STEP; [| simpl; omega].
      destruct OSEQ_STEP as [SAME_INSTRS [lbls ISTEP0_]].
      infer_istep_ ISTEP0_ asn II. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := G sto;
                regf := RegFun.add reg (RegFile.eval_expr (regf sto) expr) (regf sto);
                depf := RegFun.add reg (DepsFile.expr_deps (depf sto) expr) (depf sto);
                ectrl := ectrl sto;
                eindex := eindex sto |}).
      exists sto'. splits.
      { red. exists [].
        red. splits; [subst; simpl; auto| ].
        exists (Instr.assign reg expr). exists 0. splits.
        { replace (pc sto) with (bpc bsti); [auto| cdes MM_SIM; vauto]. }
        pose proof (@Oassign tid [] sto sto' (Instr.assign reg expr) 0 reg expr) as OMM_STEP.
        specialize_full OMM_STEP; auto. }
      cdes MM_SIM. 
      (* pose proof INSTR_LEXPR_HELPER as LEXPR_SAME. specialize LEXPR_SAME with (instr := (Instr.assign reg expr)). specialize_full LEXPR_SAME; vauto.  *)
      (* pose proof INSTR_LEXPR_DEPS_HELPER as LEXPR_DEPS_SAME. specialize LEXPR_DEPS_SAME with (instr := (Instr.update (Instr.exchange new_expr) Xpln Osc Osc exchange_reg loc_expr)). specialize_full LEXPR_DEPS_SAME; vauto.  *)
      pose proof INSTR_EXPR_HELPER as EXPR_SAME. specialize EXPR_SAME with (instr := (Instr.assign reg expr)). specialize_full EXPR_SAME; vauto. 
      pose proof INSTR_EXPR_DEPS_HELPER as EXPR_DEPS_SAME. specialize EXPR_DEPS_SAME with (instr := (Instr.assign reg expr)). specialize_full EXPR_DEPS_SAME; vauto. 
      red. splits.
      { subst sto'. simpl. congruence. }
      { subst sto'. simpl. apply OPC'; auto. }
      { simpl. replace_bg_rels bsti' sti'. rewrite UG. simpl. auto. }
      { ins. rewrite UREGS.
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg); auto.
        unfold RegFun.find. auto. }
      { subst sto'. simpl. ins. rewrite UDEPS. 
        unfold RegFun.add. destruct (LocSet.Facts.eq_dec reg0 reg).
        { replace_bg_rels bsti sti. rewrite UG. auto. }
        unfold RegFun.find. replace_bg_rels bsti sti. rewrite UG.
        apply MM_SIM4. auto. }
      { subst sto'. simpl in *. unfold_clear_updated. rewrite UECTRL. 
        replace_bg_rels bsti sti. rewrite UG. auto. }
      subst sto'. simpl. replace (beindex bsti') with (eindex sti') by auto.
      rewrite UINDEX. auto.
    - assert (block = [Instr.ifgoto e (length (flatten (firstn n (binstrs bsti))))]). 
      { inversion CORR. subst. inversion H3. subst.
           subst igt. inversion H1; vauto. 
           subst. subst addr. f_equal. f_equal.
           apply SAME_STRUCT_PREF.
           cdes MM_SIM. cdes OSEQ_STEP. red in COMPILED. desc. 
           eapply correction_same_struct; vauto. }
      subst block. simpl in *.
      pose proof (BLOCK_CONTENTS 0 (Instr.ifgoto e (length (flatten (firstn n (binstrs bsti))))) eq_refl) as BLOCK_CONTENTS0. 
      apply (STEP1 eq_refl) in OSEQ_STEP.
      apply (@ISTEP1 sti sti' (Instr.ifgoto e (length (flatten (firstn n (binstrs bsti))))) _ BLOCK_CONTENTS0) in OSEQ_STEP; [| simpl; omega].
      destruct OSEQ_STEP as [SAME_INSTRS [lbls ISTEP0_]].
      remember (Instr.ifgoto e (length (flatten (firstn n (binstrs bsti))))) as igt_comp. 
      infer_istep_ ISTEP0_ igt_comp II. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := if Const.eq_dec (RegFile.eval_expr (regf sto) expr) 0 then pc sto + 1 else n;
                G := G sto;
                regf := regf sto;
                depf := depf sto;
                ectrl := DepsFile.expr_deps (depf sto) expr ∪₁ ectrl sto;
                eindex := eindex sto |}).
      exists sto'. splits.
      { red. exists [].
        red. splits; [subst; simpl; auto| ].
        exists igt. exists 0. splits.
        { replace (pc sto) with (bpc bsti); [auto| cdes MM_SIM; vauto]. }
        pose proof (@Oif_ tid [] sto sto' igt 0 expr n) as OMM_STEP.
        specialize_full OMM_STEP; auto.
        destruct (Const.eq_dec (RegFile.eval_expr (regf sto) expr) 0); vauto. }
      assert (RegFile.eval_expr (regf sto) expr = RegFile.eval_expr (regf sti) expr) as EXPR_SAME.
      { eapply INSTR_EXPR_HELPER; eauto. vauto. }
      (* assert (DepsFile.expr_deps (depf sto) expr = DepsFile.expr_deps (depf sti) expr) as EXPR_DEPS_SAME. *)
      (* { eapply INSTR_EXPR_DEPS_HELPER; eauto. vauto. } *)
      
      red. splits.      
      { subst sto'. simpl. rewrite <- BINSTRS_SAME.
        red. eexists. eauto. }
      { subst sto'. simpl.
        rewrite EXPR_SAME.
        destruct (Const.eq_dec (RegFile.eval_expr (regf sti) expr) 0) eqn:OCOND.
        { cut (bpc bsti' = bpc bsti + 1).
          { ins. rewrite H. cdes MM_SIM. congruence. }
          simpl in UPC.
          forward eapply (@ll_index_shift _ _ (bpc bsti) (bpc bsti') _ BLOCK); eauto. 
          { eapply COMPILED_NONEMPTY. red. eexists; eauto. }
          simpl. simpl in UPC. congruence. }
        simpl in UPC. (* inversion OCOND. *)
        rewrite <- UPC in BLOCK_CONTENTS0. eapply NONEMPTY_PREF.
        { eapply COMPILED_NONEMPTY. red. eexists; eauto. }
        { congruence. }
        { replace (length (binstrs bsti)) with (length (instrs sto)).  
          { eapply compilation_addresses_restricted; vauto. }
          apply compilation_same_length. vauto. }
        omega. }
      { subst sto'. simpl in UG. rewrite UG. simpl. cdes MM_SIM. auto. }
      { ins. rewrite UREGS. cdes MM_SIM. auto. }
      { ins. rewrite UDEPS. simpl in UG. rewrite UG. cdes MM_SIM. auto. }
      { subst sto'. simpl. replace_bg_rels bsti' sti'.
        rewrite UECTRL, UG. rewrite set_inter_union_l.
        cdes MM_SIM. 
        apply set_equiv_union; [| auto]. 
        apply eval_expr_deps_same; vauto.
        forward eapply exchange_reg_dedicated as DEDICATED. 
        { vauto. }
        { Unshelve. 2: exact (Instr.ifgoto expr (length (flatten (firstn n (binstrs bsti))))). eapply nth_error_In; eauto. }
        simpl in DEDICATED. destruct expr.
        - destruct val; simpl; tauto.
        - simpl. destruct op0; simpl; tauto.
        - simpl. destruct op1, op2; simpl; tauto. }
      subst sto'. replace_bg_rels bsti' sti'. rewrite UINDEX. simpl.
      cdes MM_SIM. auto.  
  Qed. 
      

End PairStep.  