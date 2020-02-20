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
          inversion COMP. vauto. }
        pose proof (@Oload tid lbls sto sto' ld 0 Orlx reg lexpr val l) as OMM_STEP.
        assert (ORD_RLX: ord = Orlx). 
        { subst ld. congruence. }
        rewrite ORD_RLX, REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto.
        { subst sto'. simpl. rewrite ORD_RLX, EINDEX_EQ, Nat.add_0_r. auto. }
        { subst sto'. simpl. rewrite EINDEX_EQ, Nat.add_0_r.  auto. }
        { subst sto'. simpl. rewrite REGF_EQ. auto. }
        subst sto'. simpl. rewrite DEPF_EQ. auto. }
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
        subst sto'. rewrite UG. simpl.
        ins. unfold add, acts_set in EGOx. simpl in EGOx.
        red in MM_SIM. rewrite <- EINDEX_EQ. destruct EGOx.
        + rewrite H. do 2 rewrite upds. auto.
        + assert (x <> ThreadEvent tid (eindex sto)) as NEQ.
          { red. ins. rewrite H0 in H.
            forward eapply E_bounded as BOUND; eauto.
            rewrite  EINDEX_EQ in H0, H.
            assert (E (G sti) x) as EGIx.
            { red in MM_SIM1. desc. red in RESTR_EVENTS. desc.
              red in RESTR_EVENTS. forward eapply (RESTR_EVENTS x); vauto.
              basic_solver. }
            red in BOUND. specialize (BOUND x EGIx).
            rewrite H0 in BOUND. simpl in BOUND. omega. }
          rewrite updo; auto. rewrite updo; auto. 
          red in MM_SIM1. desc. replace (G sti) with (bG bsti); [| vauto ]. 
          apply SAME_LAB. auto. }
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
          inversion COMP. vauto. }
        assert (ORD_RLX: ord0 = Orlx). 
        { subst st. congruence. }
        rewrite ORD_RLX in *. 
        assert (Instr.store Orlx lexpr expr = Instr.store Orlx loc val) by vauto.
        inversion H. subst lexpr. subst expr. clear H. 

        
        (* pose proof (@Ostore tid lbls0 sto sto'' st 2 (gt_Sn_O 1) Orlx loc val l v) as OMM_STEP. *)
        pose proof (@Ostore tid lbls0 sto sto'' st 1 Orlx loc val l v) as OMM_STEP.

        
        (* TODO: ???*)
        (* rewrite ORD_RLX, REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. *)
        (*********)
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
        subst sto''. rewrite UG0, UG. simpl.
        ins. unfold add, acts_set in EGOx. simpl in EGOx.
        rewrite UINDEX, <- EINDEX_EQ.
        destruct EGOx.
        + rewrite H. do 2 rewrite upds. auto.
        + assert (index x < eindex sto) as NEQ.
          { destruct (Const.lt_decidable (index x) (eindex sto)); auto.
            exfalso. 
            forward eapply (@E_bounded n_steps tid sti) as BOUND; eauto.
            assert (E (G sti) x) as EGIx.
            { red in MM_SIM1. desc. red in RESTR_EVENTS. desc.
              red in RESTR_EVENTS. forward eapply (RESTR_EVENTS x); vauto.
              basic_solver. }
            red in BOUND. specialize (BOUND x EGIx).
            omega. }
          rewrite updo. rewrite updo. rewrite updo.
          2, 3, 4: red; ins; rewrite H0 in NEQ; simpl in NEQ; omega.
          red in MM_SIM1. desc. replace (G sti) with (bG bsti); [| vauto ]. 
          apply SAME_LAB. auto. }
      { subst sto'. replace (bregf bsti'') with (regf sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti'') with (depf sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
      (* - .....*)
      (* - .....*)
      (* - .....*)
  Admitted.

End PairStep.  