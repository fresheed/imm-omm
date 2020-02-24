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
  (* Warning: F implicitly means at least acq/rel fence *)
  Notation "'F' G" := (fun a => is_true (is_nonnop_f G.(lab) a)) (at level 1).
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

  Lemma pair_step sto bsti (MM_SIM: mm_similar_states sto bsti)
        tid bsti' (OSEQ_STEP: omm_block_step tid bsti bsti')
        (BLOCK_REACH: (block_step tid)＊ (binit (binstrs bsti)) bsti):
    exists sto', Ostep tid sto sto' /\ mm_similar_states sto' bsti'.
  Proof.
    pose proof (block_step_nonterminal (bs_extract OSEQ_STEP)) as BST_NONTERM. 
    pose proof (BPC_CHANGE OSEQ_STEP) as BPC'. 
    red in OSEQ_STEP. destruct OSEQ_STEP as [block [BLOCK_STEP_ COMP_BLOCK]].
    forward eapply (@SAME_BINSTRS bsti bsti' tid) as BINSTRS_SAME.
    { red. eauto. }
    desc.
    red in BLOCK_STEP_. desc.
    inversion COMP_BLOCK.
    all: rename H into OINSTR.
    all: rename H0 into BLOCK_CONTENTS.
    all: subst; simpl in *.
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some ld = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc ld [ld] 0 _ bsti sti); eauto.
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
      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      exists sto'. splits.
      { red. exists lbls. red. splits; [subst; simpl; auto| ].
        exists ld. exists 0. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (ld = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP; vauto. }
          desc. inversion COMP0. }
        pose proof (@Oload tid lbls sto sto' ld 0 Orlx reg lexpr val l) as OMM_STEP.
        assert (ORD_RLX: ord = Orlx). 
        { subst ld. congruence. }
        rewrite ORD_RLX, REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto.
        { subst sto'. simpl. rewrite ORD_RLX, EINDEX_EQ, Nat.add_0_r. auto. }
        { subst sto'. simpl. rewrite EINDEX_EQ, Nat.add_0_r.  auto. }
        { subst sto'. simpl. rewrite REGF_EQ. auto. }
        subst sto'. simpl. rewrite Nat.add_0_r. congruence. }
      red. splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME. auto. }
      {  subst sto'. simpl. destruct BPC' as [BPC' | BPC']. 
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { red.
        pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH]. 
        splits.
        { replace (bG bsti') with (G sti') by vauto.
          rewrite (@E_ADD).
          2: { repeat eexists. } 
          rewrite (@E_ADD (G sti) (G sti')).
          2: { repeat eexists. eapply UG. }
          desc.
          remember (Aload false ord (RegFile.eval_lexpr (regf sti) lexpr) val) as new_lbl. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti sti' tid new_lbl _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH)) as R_EXT; eauto. 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti sti' tid new_lbl _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH)) as W_EXT; eauto. 
 
          rewrite R_EXT, W_EXT. subst new_lbl. simpl in *.
          arewrite (rmw (G sti') ≡ rmw (G sti)).
          { rewrite UG. vauto. }
          rewrite EINDEX_EQ, set_union_empty_r. 
          remember (eq (ThreadEvent tid (eindex sti))) as nev.
          rewrite set_unionA, (set_unionC _ (W (G sti))), <- set_unionA.
          rewrite set_inter_union_l. apply set_equiv_union.
          { rewrite set_inter_minus_r.
            arewrite (E (G sti) ∩₁ (RW (G sti) ∪₁ nev) ≡₁ E (G sti) ∩₁ RW (G sti)).
            { rewrite set_inter_union_r. 
              arewrite (E (G sti) ∩₁ nev ≡₁ ∅); [| basic_solver ].
              split; [| basic_solver].
              rewrite E_bounded; eauto. vauto.
              red. ins. red in H. desc. rewrite <- H0 in H. simpl in H. omega. }
            red in MM_SIM1. desc.
            replace (G sti) with (bG bsti) by vauto.
            rewrite <- set_inter_minus_r. auto. }
          split; [| basic_solver].
          apply set_subset_inter_r. split; [basic_solver| ].
          apply inclusion_minus. split; [basic_solver| ]. 
          subst nev. red. ins. red in H. desc. red. 
          forward eapply rmw_bibounded; eauto.
          ins. red in H1. desc.
          red in H0. desc. specialize (H1 x y).
          pose proof (H1 H0). desc. 
          rewrite <- H in H2. simpl in H2. omega. }
        (* **** *)
        replace (bG bsti') with (G sti'); [| vauto ]. 
        forward eapply (@sim_lab_extension 0 tid sto sti); eauto.
        { vauto. }
        { apply (@E_bounded n_steps tid sti); eauto. }
        { red. split. 
          2: { subst sto'. simpl. omega. }
          rewrite Nat.add_0_r.
          replace (lab (G sti') (ThreadEvent tid (eindex sto))) with (Aload false ord (RegFile.eval_lexpr (regf sti) lexpr) val).
          { repeat eexists. }
          unfold add. rewrite UG, EINDEX_EQ. simpl.
          rewrite upds. auto. }
        replace (0 + 1) with 1 by omega. rewrite (same_relation_exp (pow_unit _)).
        red. eexists. red. split.
        2: { cut (eindex sti' = eindex sti + 1); [omega |].
             vauto. }
        rewrite Nat.add_0_r. repeat eexists. eauto. }
      { subst sto'. replace (bregf bsti') with (regf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc f [f; st] 0 _ bsti sti); eauto.
        rewrite Nat.add_0_r. auto. }
      assert (AT_PC': Some st = nth_error (instrs sti) (pc sti + 1)).
      { forward eapply (@near_pc st [f; st] 1 _ bsti sti); eauto. }

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

      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      
      exists sto''. splits.
      { red. exists lbls0. red. splits; [subst; simpl; auto| ].
        exists st. exists 1. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (st = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        assert (ORD_RLX: ord0 = Orlx). 
        { subst st. congruence. }
        rewrite ORD_RLX in *. 
        assert (Instr.store Orlx lexpr expr = Instr.store Orlx loc val) by vauto.
        inversion H. subst lexpr. subst expr. clear H. 

        pose proof (@Ostore tid lbls0 sto sto'' st 1 Orlx loc val l v) as OMM_STEP.

        forward eapply OMM_STEP; eauto.
        (* TODO: modify equalities above to operate with sti' ? *)
        { rewrite REGF_EQ, <- UREGS. auto. }
        { rewrite REGF_EQ, <- UREGS. auto. }
        { subst sto''. subst sto'. simpl. rewrite ORD_RLX, EINDEX_EQ.
          unfold add at 1. simpl. basic_solver.  }
        subst sto''. subst sto'. simpl. omega. }
      red.
      pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH]. 
      
      splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl. destruct BPC' as [BPC' | BPC']. 
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { red.
        assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
        { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
          exists sti. split.
          { rewrite <- INSTRS. auto. }
          red. exists lbls. red. splits; auto.
          eexists. eauto. }
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.
          rewrite (@E_ADD).
          2: { repeat eexists. } 
          rewrite (@E_ADD (G sti') (G sti'') tid (eindex sti + 1)).
          2: { repeat eexists. rewrite <- UINDEX. eapply UG0. }
          rewrite (@E_ADD (G sti) (G sti') tid (eindex sti)).
          2: { repeat eexists. eapply UG. }
          
          desc.
          remember (Afence ord) as new_lbl. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti sti' tid new_lbl _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH)) as R_EXT; eauto. 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti sti' tid new_lbl _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH)) as W_EXT; eauto. 
          
          desc.
          remember (Astore xmd ord0 l v) as new_lbl'. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti' sti'' tid new_lbl' _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH')) as R_EXT'; eauto. 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti' sti'' tid new_lbl' _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH')) as W_EXT'; eauto. 

          rewrite W_EXT', R_EXT', R_EXT, W_EXT.
          arewrite (rmw (G sti'') ≡ rmw (G sti)).
          { rewrite UG0, UG. vauto. }
          subst new_lbl'. subst new_lbl. simpl in *.  
          rewrite EINDEX_EQ, !set_union_empty_r. 
          remember (eq (ThreadEvent tid (eindex sti))) as nev.
          rewrite UINDEX. remember (eq (ThreadEvent tid (eindex sti + 1))) as nev'.
          rewrite <- set_unionA, set_unionA. 
          rewrite set_inter_union_l. apply set_equiv_union.
          { rewrite set_inter_minus_r.
            arewrite (E (G sti) ∩₁ (RW (G sti) ∪₁ nev') ≡₁ E (G sti) ∩₁ RW (G sti)).
            { rewrite set_inter_union_r. 
              arewrite (E (G sti) ∩₁ nev' ≡₁ ∅); [| basic_solver ].
              split; [| basic_solver].
              rewrite E_bounded; eauto. vauto.
              red. ins. red in H. desc. rewrite <- H0 in H. simpl in H. omega. }
            red in MM_SIM1. desc.
            replace (G sti) with (bG bsti) by vauto.
            rewrite <- set_inter_minus_r. auto. }
          split.
          2: { rewrite set_inter_union_l. apply set_subset_union_l.
               split; [| basic_solver].
               rewrite set_inter_minus_r. rewrite set_inter_union_r.
               arewrite (nev ∩₁ nev' ≡₁ ∅).
               { subst. red. split; [| basic_solver].
                 red. ins. red in H. desc. rewrite <- H in H0.
                 inversion H0. omega. }
               arewrite (nev ∩₁ RW (G sti) ≡₁ ∅).
               2: basic_solver.
               red. split; [| basic_solver]. 
               red. ins. red in H. desc. rewrite Heqnev in H.
               red in H0. destruct H0.
               + forward eapply (@nonnop_bounded n_steps (@is_r actid) r_matcher sti tid) as R_BOUNDED; eauto. 
               { apply r_pl. }
               { red. vauto. }
                 do 2 red in R_BOUNDED. specialize (R_BOUNDED x H0).
                 rewrite <- H in R_BOUNDED. simpl in R_BOUNDED. omega.
               + forward eapply (@nonnop_bounded n_steps (@is_w actid) w_matcher sti tid) as W_BOUNDED; eauto. 
               { apply w_pl. }
               { red. vauto. }
                 do 2 red in W_BOUNDED. specialize (W_BOUNDED x H0).
                 rewrite <- H in W_BOUNDED. simpl in W_BOUNDED. omega. }
               
          apply set_subset_inter_r. split; [basic_solver| ].
          apply inclusion_minus. split; [basic_solver| ]. 
          subst nev. red. ins. red in H. desc. red. 
          forward eapply rmw_bibounded; eauto.
          ins. red in H1. desc.
          red in H0. desc. specialize (H1 x y).

          assert (rmw (G sti') x y) as RMW'xy. 
          { assert (rmw (G sti') ≡ rmw (G sti)). 
            { rewrite UG. vauto. }
            apply (same_relation_exp H2). auto. }
          
          pose proof (H1 RMW'xy). desc. 
          rewrite Heqnev' in H. rewrite <- H in H2. simpl in H2. omega. }
        
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
      { subst sto'. replace (bregf bsti'') with (regf sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti'') with (depf sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc f [f; ld] 0 _ bsti sti); eauto.
        rewrite Nat.add_0_r. auto. }
      assert (AT_PC': Some ld = nth_error (instrs sti) (pc sti + 1)).
      { forward eapply (@near_pc ld [f; ld] 1 _ bsti sti); eauto. }

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

      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      
      exists sto''. splits.
      { red. exists lbls0. red. splits; [subst; simpl; auto| ].
        exists ld. exists 1. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (ld = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        assert (ORD_SC: ord0 = Osc). 
        { subst ld. congruence. }
        rewrite ORD_SC in *.
        assert (Instr.load Osc reg lexpr = Instr.load Osc lhs loc) by vauto.
        inversion H. subst lexpr. subst reg. clear H. 
        
        pose proof (@Oload tid lbls0 sto sto'' ld 1 Osc lhs loc val l) as OMM_STEP.

        forward eapply OMM_STEP; eauto.
        (* TODO: modify equalities above to operate with sti' ? *)
        { rewrite REGF_EQ, <- UREGS. auto. }
        { rewrite REGF_EQ, <- UREGS. auto. }
        { subst sto''. simpl. rewrite ORD_SC, EINDEX_EQ.
          unfold add at 1. simpl. basic_solver. }
        subst sto''. simpl. omega. }
      red.
      pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH]. 
      
      splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl. destruct BPC' as [BPC' | BPC']. 
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { red.
        assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
        { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
          exists sti. split.
          { rewrite <- INSTRS. auto. }
          red. exists lbls. red. splits; auto.
          eexists. eauto. }
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.
          rewrite (@E_ADD).
          2: { repeat eexists. } 
          rewrite (@E_ADD (G sti') (G sti'') tid (eindex sti + 1)).
          2: { repeat eexists. rewrite <- UINDEX. eapply UG0. }
          rewrite (@E_ADD (G sti) (G sti') tid (eindex sti)).
          2: { repeat eexists. eapply UG. }
          
          desc.
          remember (Afence ord) as new_lbl. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti sti' tid new_lbl _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH)) as R_EXT; eauto. 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti sti' tid new_lbl _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH)) as W_EXT; eauto. 
          
          desc.
          remember (Aload false ord0 (RegFile.eval_lexpr (regf sto) lexpr) val) as new_lbl'. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti' sti'' tid new_lbl' _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH')) as R_EXT'; eauto. 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti' sti'' tid new_lbl' _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH')) as W_EXT'; eauto. 

          rewrite W_EXT', R_EXT', R_EXT, W_EXT.
          arewrite (rmw (G sti'') ≡ rmw (G sti)).
          { rewrite UG0, UG. vauto. }
          subst new_lbl'. subst new_lbl. simpl in *.  
          rewrite EINDEX_EQ, !set_union_empty_r. 
          remember (eq (ThreadEvent tid (eindex sti))) as nev.
          rewrite UINDEX. remember (eq (ThreadEvent tid (eindex sti + 1))) as nev'.
          rewrite set_unionA. rewrite set_unionA. rewrite set_unionC with (s := nev'). rewrite <- set_unionA with (s := R (G sti)). 
          rewrite set_inter_union_l. apply set_equiv_union.
          { rewrite set_inter_minus_r.
            arewrite (E (G sti) ∩₁ (RW (G sti) ∪₁ nev') ≡₁ E (G sti) ∩₁ RW (G sti)).
            { rewrite set_inter_union_r. 
              arewrite (E (G sti) ∩₁ nev' ≡₁ ∅); [| basic_solver ].
              split; [| basic_solver].
              rewrite E_bounded; eauto. vauto.
              red. ins. red in H. desc. rewrite <- H0 in H. simpl in H. omega. }
            red in MM_SIM1. desc.
            replace (G sti) with (bG bsti) by vauto.
            rewrite <- set_inter_minus_r. auto. }
          split.
          2: { rewrite set_inter_union_l. apply set_subset_union_l.
               split; [| basic_solver].
               rewrite set_inter_minus_r. rewrite set_inter_union_r.
               arewrite (nev ∩₁ nev' ≡₁ ∅).
               { subst. red. split; [| basic_solver].
                 red. ins. red in H. desc. rewrite <- H in H0.
                 inversion H0. omega. }
               arewrite (nev ∩₁ RW (G sti) ≡₁ ∅).
               2: basic_solver.
               red. split; [| basic_solver]. 
               red. ins. red in H. desc. rewrite Heqnev in H.
               red in H0. destruct H0.
               + forward eapply (@nonnop_bounded n_steps (@is_r actid) r_matcher sti tid) as R_BOUNDED; eauto. 
               { apply r_pl. }
               { red. vauto. }
                 do 2 red in R_BOUNDED. specialize (R_BOUNDED x H0).
                 rewrite <- H in R_BOUNDED. simpl in R_BOUNDED. omega.
               + forward eapply (@nonnop_bounded n_steps (@is_w actid) w_matcher sti tid) as W_BOUNDED; eauto. 
               { apply w_pl. }
               { red. vauto. }
                 do 2 red in W_BOUNDED. specialize (W_BOUNDED x H0).
                 rewrite <- H in W_BOUNDED. simpl in W_BOUNDED. omega. }
               
          apply set_subset_inter_r. split; [basic_solver| ].
          apply inclusion_minus. split; [basic_solver| ]. 
          subst nev. red. ins. red in H. desc. red. 
          forward eapply rmw_bibounded; eauto.
          ins. red in H1. desc.
          red in H0. desc. specialize (H1 x y).

          assert (rmw (G sti') x y) as RMW'xy. 
          { assert (rmw (G sti') ≡ rmw (G sti)). 
            { rewrite UG. vauto. }
            apply (same_relation_exp H2). auto. }
          
          pose proof (H1 RMW'xy). desc. 
          rewrite Heqnev' in H. rewrite <- H in H2. simpl in H2. omega. }
        
        replace (bG bsti'') with (G sti''); [| vauto ]. 
        forward eapply (@sim_lab_extension 1 tid sto sti); eauto.
        { vauto. }
        { apply (@E_bounded n_steps tid sti); eauto. }
        { red. split. 
          2: { subst sto''. simpl. omega. } 
          replace (lab (G sti'') (ThreadEvent tid (eindex sto + 1))) with (Aload false ord0 (RegFile.eval_lexpr (regf sto) lexpr) val).
          2: { rewrite UG0, UG. rewrite UREGS, REGF_EQ. simpl.
               replace (eindex sti') with (eindex sto + 1) by congruence. 
               rewrite upds. auto. }
          repeat eexists. }
        simpl. red. exists sti'. split.
        { red. exists sti. split; [red; auto|]. red. eexists. red.
          rewrite Nat.add_0_r. split; auto. repeat eexists. eauto. }
        red. eexists. red. rewrite Nat.add_0_r. split; auto.
        repeat eexists. eauto. }
      { replace (bregf bsti'') with (regf sti''); [| vauto ].
        simpl. congruence. }
      { replace (bdepf bsti'') with (depf sti''); [| vauto ].
        simpl. congruence. }
      { replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc f [f; exc] 0 _ bsti sti); eauto.
        rewrite Nat.add_0_r. auto. }
      assert (AT_PC': Some exc = nth_error (instrs sti) (pc sti + 1)).
      { forward eapply (@near_pc exc [f; exc] 1 _ bsti sti); eauto. }

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

      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti).
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti).
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti).
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti).
      { rewrite MM_SIM4. vauto. }
      
      exists sto''. splits.
      { red. exists [Astore Xpln Osc loc0 new_value]. red. splits; [subst; simpl; auto| ].
        exists st. exists 2. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto.
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (st = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        assert (ORDR_SC: ordr = Osc).
        { subst exc. congruence. }
        assert (ORDW_SC: ordw = Osc).
        { subst exc. congruence. }
        rewrite ORDR_SC, ORDW_SC in *.
        assert (Instr.update (Instr.exchange new_expr) xmod Osc Osc reg loc_expr = Instr.update (Instr.exchange val) Xpln Osc Osc exchange_reg loc) by vauto.
        inversion H. subst new_expr. subst xmod. subst reg. subst loc_expr. clear H.
        
        pose proof (@Ostore tid [Astore Xpln Osc loc0 new_value] sto sto'' st 2 Osc loc val loc0 new_value) as OMM_STEP.

        forward eapply OMM_STEP; eauto.
        { rewrite REGF_EQ, <- UREGS. auto. }
        { rewrite REGF_EQ, <- UREGS. auto. }
        { subst sto''. simpl. congruence. }
        subst sto''. simpl. omega. }
      red.
      pose proof (reach_with_blocks Heqsti BLOCK_REACH) as [n_steps REACH].
      
      splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl. destruct BPC' as [BPC' | BPC'].
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { red.
        assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
        { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
          exists sti. split.
          { rewrite <- INSTRS. auto. }
          red. exists lbls. red. splits; auto.
          eexists. eauto. }
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.
          rewrite (@E_ADD).
          2: { repeat eexists. }
          (* move UG0 at bottom.  *)
          (* unfold add_rmw in UG0. simpl in UG0.   *)
          
          rewrite (@E_ADD_RMW (G sti') (G sti'') tid (eindex sti + 1)).
          2: { repeat eexists. rewrite <- UINDEX. eapply UG0. }
          rewrite (@E_ADD (G sti) (G sti') tid (eindex sti)).
          2: { repeat eexists. eapply UG. }
          
          desc.
          remember (Afence ord) as new_lbl.
          forward eapply (@label_set_step (@is_r actid) r_matcher sti sti' tid new_lbl _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH)) as R_EXT; eauto.
          forward eapply (@label_set_step (@is_w actid) w_matcher sti sti' tid new_lbl _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH)) as W_EXT; eauto.

          desc.
          remember (Aload true ordr loc0 old_value) as new_lbl'.
          remember (Astore xmod ordw loc0 new_value) as new_lbl''.
          forward eapply (@label_set_rmw_step (@is_r actid) r_matcher sti' sti'' tid new_lbl' new_lbl'' _ r_pl (@nonnop_bounded _ (@is_r actid) r_matcher _ _ r_pl (eq_refl false) REACH')) as R_EXT'; eauto.
          forward eapply (@label_set_rmw_step (@is_w actid) w_matcher sti' sti'' tid new_lbl' new_lbl'' _ w_pl (@nonnop_bounded _ (@is_w actid) w_matcher _ _ w_pl (eq_refl false) REACH')) as W_EXT'; eauto.

          rewrite W_EXT', R_EXT', R_EXT, W_EXT. rewrite UINDEX in *.
          remember (ThreadEvent tid (eindex sti + 1)) as evr. 
          remember (ThreadEvent tid (eindex sti + 1 + 1)) as evw. 
          arewrite (rmw (G sti'') ≡ rmw (G sti) ∪ singl_rel evr evw).
          { rewrite UG0, UG. unfold add_rmw. simpl.
            rewrite <- Heqevr, <- Heqevw. basic_solver. }
          subst new_lbl''. subst new_lbl'. subst new_lbl. simpl in *.
          rewrite EINDEX_EQ, !set_union_empty_r.
          remember (eq (ThreadEvent tid (eindex sti))) as nev.
          replace (ThreadEvent tid (eindex sti + 2)) with evw.
          2: { rewrite Heqevw. f_equal. omega. }
          remember (eq evr) as nevr. remember (eq evw) as nevw.
          do 2 rewrite set_unionA.
          rewrite set_unionA with (s := R (G sti)). 
          rewrite set_unionC with (s' := W (G sti) ∪₁ nevw).
          do 2 rewrite <- set_unionA with (s := R (G sti)).
          rewrite set_unionA. 
          rewrite set_inter_union_l. apply set_equiv_union.
          { rewrite set_inter_minus_r.
            arewrite (E (G sti) ∩₁ (RW (G sti) ∪₁ (nevw ∪₁ nevr)) ≡₁ E (G sti) ∩₁ RW (G sti)).
            { rewrite set_inter_union_r.
              arewrite (E (G sti) ∩₁ (nevw ∪₁ nevr)  ≡₁ ∅); [| basic_solver ].
              split; [| basic_solver].              
              arewrite (nevw ∪₁ nevr ⊆₁ fun e => index e >= eindex sti).
              { red. ins. red in H. destruct H.
                all: subst; subst; simpl; omega. }
              rewrite E_bounded; eauto.
              red. ins. red in H. omega. }
            rewrite dom_union.
            rewrite set_minus_union_r.
            rewrite empty_inter_minus_same with (Y := dom_rel (singl_rel evr evw)).
            { rewrite set_inter_minus_l. rewrite set_interK.
              red in MM_SIM1. desc.
              replace (G sti) with (bG bsti) by vauto.
              rewrite <- set_inter_minus_r. auto. }
            red. split; [| basic_solver].
            arewrite (dom_rel (singl_rel evr evw) ⊆₁ fun e => index e >= eindex sti).
            { red. ins. red in H. desc. red in H. desc.
              subst. rewrite Heqevr. simpl. omega. }
            rewrite E_bounded; eauto. red. ins. do 2 (red in H; desc). omega. } 
          split.
          2: { rewrite set_inter_union_l.
               apply set_subset_union_l.
               split.
               2: { rewrite set_inter_union_l. apply set_subset_union_l.
                    split.
                    { rewrite set_inter_minus_r.
                      arewrite (nevr ∩₁ (RW (G sti) ∪₁ (nevw ∪₁ nevr)) ≡₁ nevr) by basic_solver.
                      rewrite dom_union, set_minus_union_r.
                      arewrite (nevr \₁ dom_rel (singl_rel evr evw) ⊆₁ ∅) by basic_solver.
                      basic_solver. }
                    rewrite set_inter_minus_r.
                    arewrite (nevw ∩₁ (RW (G sti) ∪₁ (nevw ∪₁ nevr)) ⊆₁ nevw) by basic_solver.
                    rewrite dom_union, set_minus_union_r.
                    arewrite (nevw \₁ dom_rel (singl_rel evr evw) ⊆₁ nevw) by basic_solver.
                    arewrite (nevw \₁ dom_rel (rmw (G sti)) ⊆₁ nevw); [| basic_solver].
                    rewrite empty_inter_minus_same; [basic_solver |].
                    red. split; [| basic_solver].
                    rewrite (rmw_bibounded _ _ _ REACH).
                    rewrite Heqnevw. red. ins. red in H. desc. subst.
                    red in H0. desc. subst. simpl in H0. omega. }
               rewrite set_inter_minus_r.
               arewrite (nev ∩₁ (RW (G sti) ∪₁ (nevw ∪₁ nevr)) ⊆₁ ∅); [| basic_solver].
               rewrite set_inter_union_r.
               apply set_subset_union_l.
               split.
               2: { subst. rewrite Heqevw. rewrite Heqevr.
                    red. ins. red in H. desc. red in H0.
                    destruct H0; subst; inversion H0; omega. }
               arewrite (RW (G sti) ⊆₁ (fun e => index e < eindex sti)).
               2: { rewrite Heqnev. red. ins. red in H. desc.
                    subst. simpl in H0. omega. }
               apply set_subset_union_l. split.
               { forward eapply (@nonnop_bounded n_steps (@is_r actid) r_matcher sti tid) as R_BOUNDED; eauto.
               { apply r_pl. }
               red. vauto. }
               forward eapply (@nonnop_bounded n_steps (@is_w actid) w_matcher sti tid) as W_BOUNDED; eauto.
               { apply w_pl. }
               red. vauto. }
          apply set_subset_inter_r. split; [basic_solver |].
          apply inclusion_minus. split; [basic_solver| ].
          rewrite dom_union. rewrite set_inter_union_r.
          assert (forall {A: Type} (x y: A -> Prop), dom_rel (singl_rel x y) ≡₁ eq x) as DOM_SINGLE. 
          { ins. basic_solver. }
          apply set_subset_union_l. split.
          2: { red. ins. red in H. desc. subst. rewrite <- H in H0.
               red in H0. desc. red in H0. desc. subst.
               inversion H0. omega. }
          rewrite (rmw_bibounded _ _ _ REACH). subst.
          rewrite Heqevw. red. ins. red in H. desc. rewrite <- H in H0.
          red in H0. desc. simpl in H0. omega. }        
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
        rewrite UREGS0, UREGS. simpl. admit. }
      { replace (bdepf bsti'') with (depf sti''); [| vauto ].
        subst sto''. simpl. rewrite UDEPS0, UDEPS. admit. }
      { replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some asn = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc asn [asn] 0 _ bsti sti); eauto.
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
      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      exists sto'. splits.
      { red. exists []. red. splits; [subst; simpl; auto| ].
        exists asn. exists 0. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (asn = oinstr); [congruence| ].
          destruct COMP as [[COMP NOT_IGT] | COMP]. 
          { inversion COMP. vauto. } 
          desc. inversion COMP0. }
        pose proof (@Oassign tid [] sto sto' asn 0 reg expr) as OMM_STEP.
        rewrite REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto.
        { subst sto'. simpl. congruence. }
        subst sto'. simpl. congruence. }
      red. splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME. auto. }
      {  subst sto'. simpl. destruct BPC' as [BPC' | BPC']. 
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { subst sto'. simpl. replace (bG bsti') with (G sti'); [| vauto ].
        rewrite UG. vauto. }
      { subst sto'. replace (bregf bsti') with (regf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some igt = nth_error (instrs sti) (pc sti)).
      { forward eapply (@near_pc igt [igt] 0 _ bsti sti); eauto.
        rewrite Nat.add_0_r. auto. }
      red in BLOCK_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 

      assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)) as [oinstr OINSTR]. 
      { apply OPT_VAL. apply nth_error_Some.
        red in MM_SIM. desc. rewrite MM_SIM0.
        replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
        symmetry. apply compilation_same_length. red.
        red in MM_SIM. desc. 
        eexists. split; eauto. }
      red in MM_SIM. desc.
      forward eapply (@every_instruction_compiled (instrs sto) (binstrs bsti)) as COMP; eauto. 
      { rewrite MM_SIM0. eauto. }
      destruct COMP as [[COMP NOT_IGT]| COMP]. 
      { inversion COMP. subst. simpl in NOT_IGT. vauto. } 
      desc. inversion COMP0. subst.
      replace expr with cond in * by congruence. replace shift with addr in * by congruence. clear EQ.  
      set (sto' :=
             {| instrs := instrs sto;
                pc := if Const.eq_dec (RegFile.eval_expr (regf sto) cond) 0 then pc sto + 1 else addr0;
                G := G sto;
                regf := regf sto;
                depf := depf sto;
                ectrl := DepsFile.expr_deps (depf sto) cond ∪₁ ectrl sto;
                eindex := eindex sto |}).
      red in MM_SIM. desc.
      remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      exists sto'. splits.
      { red. exists []. red. splits; [subst; simpl; auto| ].
        
        
        (* assert (exists block0, Some block0 = nth_error BPI0 (bpc bsti)) as [block0 BLOCK0].  *)
        (* { apply OPT_VAL, nth_error_Some. *)
        (*   replace (length BPI0) with (length (binstrs bsti)); auto. *)
        (*   symmetry. eapply Forall2_length; eauto. } *)
        (* assert (exists addr0, block0 = [Instr.ifgoto e addr0]) as [addr0 BLOCK0'].  *)
        (* { cut ((block_corrected BPI0) block0 [igt]). *)
        (*   { intros BC. inversion BC. subst. inversion H3. subst. *)
        (*     inversion H2; eauto. subst. vauto. } *)
        (*   eapply Forall2_index; eauto. }         *)
        
        exists (Instr.ifgoto cond addr0). exists 0. splits; auto. 
        pose proof (@Oif_ tid [] sto sto' (Instr.ifgoto cond addr0) 0 cond addr0) as OMM_STEP.
        rewrite REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto.
        2: { subst sto'. simpl. congruence. }
        destruct (Const.eq_dec (RegFile.eval_expr (regf sti) cond)) eqn:ICOND.
        { subst sto'. simpl. rewrite REGF_EQ. rewrite ICOND. auto. }
        subst sto'. simpl. rewrite REGF_EQ, ICOND. auto. }
      red. 
      splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME.
        red. eexists. eauto. }
      { subst sto'. simpl.
        destruct (Const.eq_dec (RegFile.eval_expr (regf sto) cond) 0) eqn:OCOND.
        { rewrite <- REGF_EQ, OCOND in UPC. unfold bst2st in UPC. simpl in UPC.
          admit. }
        rewrite <- REGF_EQ, OCOND in UPC. unfold bst2st in UPC. simpl in UPC.
        assert (Some [Instr.ifgoto cond addr0] = nth_error BPI0 (bpc bsti)) as BLOCK0 by admit.
        pose proof (Forall2_index MM_SIM6 _ BLOCK0 AT_BLOCK).
        red in H. inversion H. subst. inversion H3; vauto; subst.
        subst addr.
        set (same_struct := fun {A: Type} (ll1 ll2: list (list A)) => Forall2 (fun l1 l2 => length l1 = length l2) ll1 ll2).
        assert (forall {A: Type} (ll1 ll2: list (list A)) (SS: same_struct _ ll1 ll2) i,
                   length (flatten (firstn i ll1)) = length (flatten (firstn i ll2))) as SAME_STRUCT_PREF by admit.
        assert (same_struct _ BPI0 (binstrs bsti')) as SAME_STRUCT_CORR by admit.
        rewrite (SAME_STRUCT_PREF _ _ _ SAME_STRUCT_CORR) in H6. 
        assert (forall {A: Type} (ll: list (list A)) (NE: Forall (fun l => l <> []) ll)
                  i j, length (flatten (firstn i ll)) = length (flatten (firstn j ll)) -> i = j) as NONEMPTY_PREF by admit.
        apply NONEMPTY_PREF in H6; auto.
        rewrite <- BINSTRS_SAME.
        assert (forall PO BPI, is_thread_block_compiled PO BPI -> Forall (fun l : list Instr.t => l <> []) BPI) as COMPILED_NONEMPTY by admit.
        eapply COMPILED_NONEMPTY. red. eexists; eauto. } 
      { subst sto'. simpl. replace (bG bsti') with (G sti'); [| vauto ].
        rewrite UG. replace (G sti) with (bG bsti); [| vauto ]. auto. }
      { subst sto'. simpl. replace (bregf bsti') with (regf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
  Admitted.

End PairStep.  