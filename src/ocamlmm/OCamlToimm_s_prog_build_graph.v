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
Require Import OCamlToimm_s_prog_pair_step. 
(* Require Import OCamlToimm_s_prog_bounded_properties.  *)
(* Require Import OCamlToimm_s_compcorrhelpers.  *)
Require Import OCamlToimm_s_steps. 
Require Import Utils.
Require Import ClosuresProperties. 
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import Logic.Decidable. 
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.

  
Section BUILD_OMM_GRAPH.

  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI. 
  Proof.
    red in ExI. destruct ExI as [sti_fin ExI]. desc.
    apply (@crt_num_steps _ (step tid) (init PI) sti_fin) in STEPS as [n_isteps ISTEPS].
    assert (SAME_INSTRS: PI = instrs sti_fin). 
    { replace PI with (instrs (init PI)); auto. 
      apply steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
    red in COMP. desc.
    set (bsti_fin := {|
          binstrs := BPI;
          bpc := length BPI;
          bG := G sti_fin;
          beindex := eindex sti_fin;
          bregf := regf sti_fin;
          bdepf := depf sti_fin;
          bectrl := ectrl sti_fin |}). 
    assert (sti_fin = bst2st bsti_fin) as BST. 
    { unfold bst2st. 
      simpl.
      rewrite firstn_all.
      red in COMP. desc.
      rewrite <- COMP0.
      rewrite SAME_INSTRS.
      rewrite (@is_terminal_pc_bounded sti_fin tid PO PI) in TERMINAL; vauto.
      2: { apply crt_num_steps. eauto. }
      rewrite <- TERMINAL; auto.
      (* TODO: why so complicated? *)      
      apply state_record_equality. } 
    
    assert (is_block_terminal bsti_fin) as BLOCK_TERM. 
    { red. destruct (dec_ge (bpc bsti_fin) (length (binstrs bsti_fin))); auto. }
    assert (exists n_osteps, (omm_block_step tid) ^^ n_osteps (binit BPI) bsti_fin) as [n_osteps OMM_STEPS]. 
    { apply crt_num_steps.
      forward eapply (@steps_imply_ommblocks bsti_fin _ tid); eauto.
      { exists PO. red in COMP. desc. auto. }
      Unshelve. 2: simpl; omega. 
      rewrite <- BST. apply crt_num_steps.
      rewrite <- SAME_INSTRS. eauto. }
    
    assert (BY_STEPS:
              forall i bsti_i (INDEX: i <= n_osteps)
                (STEPS_TO: (omm_block_step tid)^^i (binit BPI) bsti_i)
                (STEPS_FROM: (omm_block_step tid)^^(n_osteps - i) bsti_i bsti_fin),
                 exists sto_i,
                 (Ostep tid)^^i (init PO) sto_i /\
                 mm_similar_states sto_i bsti_i /\
                 pc sto_i <= length PO).
    { induction i.
      - intros bsti_i _ STEPS_TO STEPS_FROM.
        exists (init PO). splits; [basic_solver| | simpl; omega].
        replace (bsti_i) with (binit BPI); [apply init_mm_same; auto| ].
        { red in COMP. desc. auto. }
        generalize STEPS_TO. simpl. basic_solver 10.
      - intros bsti_i INDEX STEPS_TO STEPS_FROM.
        rewrite step_prev in STEPS_TO.
        destruct STEPS_TO as [bsti_i' [STEPS_TO' STEPS_FROM']].
        forward eapply IHi as [sto' [OSTEPS' [MM_SIM' PCO_BOUND]]]. 
        { omega. }
        { eauto. }
        { apply (@steps_split _ _ _ 1 (n_osteps - S i)); [omega| ].
          eexists. split; eauto. simpl. basic_solver. }

        forward eapply (@clos_refl_trans_mori _ (omm_block_step tid) (block_step tid)).
        { red. ins. apply bs_extract. auto. }
        intros OB_B.
        assert (bpc bsti_i <= length (binstrs bsti_i')) as BPC_BOUND.
        { replace (binstrs bsti_i') with (binstrs bsti_i).
          2: { red in STEPS_FROM'. desc. auto. }
          destruct (gt_0_eq (n_osteps - S i)) as [GT | FIN].
          2: { rewrite <- FIN in STEPS_FROM.
               apply (steps0 (omm_block_step tid)) in STEPS_FROM.
               subst bsti_i. auto. }
          apply Nat.lt_le_incl. apply nth_error_Some, OPT_VAL. 
          apply steps_sub with (m := 1) in STEPS_FROM; [| omega].
          destruct STEPS_FROM as [bst_next STEP_NEXT].
          apply (same_relation_exp (pow_unit (omm_block_step tid))) in STEP_NEXT. 
          red in STEP_NEXT. desc. red in BLOCK_STEP. desc. eauto. }          
        assert (bpc bsti_i' <= length (binstrs bsti_i')).
        { red in MM_SIM'. desc. rewrite <- MM_SIM'0.
          replace (length (binstrs bsti_i')) with (length PO); auto.
          apply compilation_same_length.
          replace PO with (instrs sto'); auto.
          replace PO with (instrs (init PO)) by vauto.
          symmetry. apply omm_steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
        assert (SAME_BINSTRS': BPI = binstrs bsti_i').
        { assert (forall bst BPI_ n, (omm_block_step tid) ^^ n (binit BPI_) bst -> BPI_ = binstrs bst).
          { ins. generalize dependent bst. induction n. 
            { ins. red in H0. desc. unfold binit in H0. subst bst. auto. }
            ins. red in H0. desc. specialize (IHn _ H0). cdes H1. congruence. }
          eapply H0; eauto. 
          (* cdes STEPS_FROM'. rewrite BINSTRS_SAME.   *)

          (* replace BPI with (binstrs bsti_fin); auto. symmetry.  *)
          (* apply (@inclusion_t_ind _ (block_step tid) (fun x y => binstrs x = binstrs y)). *)
          (* { red. ins. eapply SAME_BINSTRS. eauto. } *)
          (* { red. ins. congruence. } *)
          (* apply t_step_rt. exists bsti_i. split. *)
          (* { apply bs_extract. auto. } *)
          (* apply OB_B. apply crt_num_steps. eexists. eauto. *) }

        forward eapply (pair_step MM_SIM' STEPS_FROM') as [sto [OSTEP MM_SIM]]; eauto. 
        { apply OB_B. apply crt_num_steps. exists i.
          replace (binstrs bsti_i') with BPI; auto. }
        exists sto. splits; eauto.
        2: { red in MM_SIM. desc.
             replace (length PO) with (length (binstrs bsti_i')); [omega|].
             replace (binstrs bsti_i') with BPI; auto.
             symmetry. apply compilation_same_length.
             red in COMP. desc. auto. }
        apply step_prev. eexists. splits; eauto. }
    
    forward eapply (BY_STEPS n_osteps bsti_fin (Nat.le_refl n_osteps)) as [sto_fin [OSTEPS [MM_SIM PC_BOUND]]].
    { auto. }
    { rewrite Nat.sub_diag. basic_solver. }
    assert (SAME_OINSTRS: PO = instrs sto_fin).
    { replace PO with (instrs (init PO)); auto.
      apply omm_steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
    
    exists (G sto_fin).
    splits.
    { red. exists sto_fin. splits; auto. 
      { apply crt_num_steps. vauto. }
      apply is_terminal_new.
      replace (length (instrs sto_fin)) with (length (binstrs bsti_fin)).
      2: { symmetry. apply compilation_same_length. rewrite <- SAME_OINSTRS.
           subst bsti_fin. simpl. red in COMP. desc. auto. }
      replace (pc sto_fin) with (bpc bsti_fin).
      2: { red in MM_SIM. desc. auto. }
      apply BLOCK_TERM. }
    { red in MM_SIM. desc.
      replace SGI with (bG bsti_fin); auto. }
  Qed.



  Variable ProgO ProgI: Prog.Prog.t.
  Hypothesis Compiled: is_compiled ProgO ProgI.
  Hypothesis OCamlProgO: OCamlProgram ProgO.
  
  Variable GI: execution.
  Hypothesis WFI: Wf GI.
  Variable sc: relation actid. 
  Hypothesis ExecI: program_execution ProgI GI.
  Hypothesis IPC: imm_s.imm_psc_consistent GI sc.

  Hypothesis programs_without_tid_init: ~ (IdentMap.In tid_init ProgI).

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


  Record hlpr := { htid: thread_id; hPO: list Instr.t; hPI: list Instr.t; hSGI: execution}.
  
  Definition hlpr_restr hlpr := 
    ⟪THREADO': Some (hPO hlpr) = IdentMap.find (htid hlpr) ProgO ⟫/\
    ⟪THREADI': Some (hPI hlpr) = IdentMap.find (htid hlpr) ProgI ⟫ /\
    ⟪RESTR': thread_restricted_execution GI (htid hlpr) (hSGI hlpr) ⟫. 
    
  Definition hlpr_GO SGO hlpr :=
    ⟪OEXEC':Othread_execution (htid hlpr) (hPO hlpr) SGO ⟫ /\
    ⟪SBL': same_behavior_local SGO (hSGI hlpr) ⟫.

  Definition intra_E G :=
    rmw G ≡ ⦗E G⦘ ⨾ rmw G ⨾ ⦗E G⦘ /\
    data G ≡ ⦗E G⦘ ⨾ data G ⨾ ⦗E G⦘ /\
    ctrl G ≡ ⦗E G⦘ ⨾ ctrl G ⨾ ⦗E G⦘ /\
    addr G ≡ ⦗E G⦘ ⨾ addr G ⨾ ⦗E G⦘ /\
    rmw_dep G ≡ ⦗E G⦘ ⨾ rmw_dep G ⨾ ⦗E G⦘. 

  
  Lemma sbl_sim_rect GI1 GO1 GI2 GO2 (SIM: graphs_sim_weak GI1 GI2)
        (SBL: same_behavior_local GO1 GI1)
        (SBL': same_behavior_local GO2 GI2)
        (INTRA_E: intra_E GI1):
    graphs_sim_weak GO1 GO2.
  Proof.
    red in SIM, SBL, SBL'. desc.
    assert (E GI1 ∩₁ RWO GI1 ≡₁ E GI1 ∩₁ RWO GI2) as E_RWO.
    { unfold RWO. rewrite <- SIM1. repeat rewrite set_inter_minus_r.
      apply set_equiv_inter; [| basic_solver].
      apply inter_subset_helper. ins. unfold is_r, is_w, set_union.
      rewrite SIM0; vauto. }
    assert (forall rel (RESTR1: rel GO1 ≡ restr_rel (RWO GI1) (rel GI1))
              (RESTR2: rel GO2 ≡ restr_rel (RWO GI2) (rel GI2))
              (EQV: rel GI1 ≡ rel GI2)
              (ON_E: rel GI1 ≡ ⦗E GI1⦘ ⨾ rel GI1 ⨾ ⦗E GI1⦘),
               rel GO1 ≡ rel GO2) as INTRA_HELPER. 
    { ins. rewrite RESTR1, RESTR2, <- EQV.
      rewrite ON_E.
      rewrite <- restr_relE. do 2 rewrite restr_restr.
      apply restr_rel_more; [done | basic_solver]. }
    assert (E GO1 ≡₁ E GO2) as E_EQ.
    { rewrite RESTR_EVENTS, RESTR_EVENTS0. rewrite <- SIM. auto. }
    red. splits; auto. 
    { ins. assert (E GO2 x) as E2 by (apply E_EQ; auto). 
      rewrite SAME_LAB, SAME_LAB0; auto.
      apply SIM0. rewrite (set_equiv_exp RESTR_EVENTS0) in H.
      red in H. desc. auto. }
    all: red in INTRA_E; desc; intuition.
    { rewrite RESTR_RMW, RESTR_RMW0. auto. }
    rewrite RESTR_RMWDEP0, RESTR_RMWDEP. auto. 
  Qed. 

  Lemma wf_tre_intra_E G thread (WF: Wf G) Gi
        (TRE: thread_restricted_execution G thread Gi):
    intra_E Gi.
  Proof. 
    red. destruct TRE. 
    assert (forall rel (THREAD_RESTR: rel Gi ≡ ⦗Tid_ thread⦘ ⨾ rel G ⨾ ⦗Tid_ thread⦘)
              (REL_E: rel G ≡ ⦗E G⦘ ⨾ rel G ⨾ ⦗E G⦘),
               rel Gi  ≡ ⦗E Gi⦘ ⨾ rel Gi ⨾ ⦗E Gi⦘) as E_HELPER. 
    { ins. rewrite THREAD_RESTR, REL_E. 
      rewrite <- !restr_relE, !restr_restr.
      apply restr_rel_more; [| basic_solver].
      rewrite tr_acts_set. basic_solver. } 
    Hint Resolve wf_rmwE wf_dataE wf_addrE wf_ctrlE wf_rmw_depE. 
    destruct WFI.
    splits. all: apply E_HELPER; auto.
  Qed.

  Lemma sbl_sim GO1 GO2 G (SBL1: same_behavior_local GO1 G) (SBL2: graphs_sim_weak GO1 GO2):
    same_behavior_local GO2 G.
  Proof.
    red in SBL1. red in SBL2. desc.
    assert (forall (r1 r2: execution -> relation actid) R3 (EQ: r1 GO1 ≡ r2 GO2) (TGT: r1 GO1 ≡ R3), r2 GO2 ≡ R3) as TRANS by basic_solver.
    red. splits.
    all: try (by eapply TRANS; vauto).
    { rewrite <- SBL2. auto. }
    ins. rewrite <- (set_equiv_exp SBL2) in EGOx. 
    rewrite <- SBL0; intuition.
  Qed. 
  
    
  Lemma tre_sim_weak G G1 G2 thread
        (TRE1: thread_restricted_execution G thread G1)
        (TRE2: thread_restricted_execution G thread G2):
    graphs_sim_weak G1 G2. 
  Proof.
    destruct TRE1, TRE2. red.
    assert (E G1 ≡₁ E G2) as E_EQV.
    { symmetry in tr_acts_set0. eapply set_equiv_rel_Transitive; eauto. }
    splits; auto.
    { ins. rewrite tr_lab; auto. rewrite tr_lab0; auto. apply E_EQV. auto. }
    all: eapply same_rel_Transitive; eauto; symmetry; auto. 
  Qed. 
    
  Lemma RWO_RESTR thread GIi (TRE: thread_restricted_execution GI thread GIi):
    E GIi ∩₁ RWO GIi ≡₁ E GIi ∩₁ ((Tid_ thread) ∩₁ (RWO GI)). 
  Proof.
    unfold RWO.
    arewrite (Tid_ thread ∩₁ (RW GI \₁ dom_rel (rmw GI)) ≡₁ ((Tid_ thread ∩₁ (RW GI)) \₁ (Tid_ thread ∩₁ dom_rel (rmw GI)))).
    { split; try basic_solver.
      red. ins. red in H. desc. red in H0. desc.
      red. unfold set_inter. splits; vauto. tauto. }
    arewrite (Tid_ thread ∩₁ dom_rel (rmw GI) ≡₁ dom_rel (rmw GIi)).
    { destruct TRE. rewrite tr_rmw. split; try basic_solver.
      red. ins. red in H. desc. red in H0. desc.
      red. exists y. apply seq_eqv_lr. splits; auto.
      apply (wf_rmwt WFI) in H0. congruence. }
    repeat rewrite set_inter_minus_r. apply set_equiv_minus; [| basic_solver].
    rewrite <- set_interA.
    arewrite (E GIi ∩₁ Tid_ thread ≡₁ E GIi).
    { destruct TRE. rewrite tr_acts_set. basic_solver. }
    apply inter_subset_helper. ins.
    unfold is_r, is_w, set_union. destruct TRE.
    rewrite tr_lab; auto.
  Qed. 
    
  Lemma restr_graph G tid: exists Gi, thread_restricted_execution G tid Gi.
  Proof.
    set (Gi :=   {| acts := filterP (fun e => Events.tid e = tid) (acts G);
                    lab := lab G;
                    rmw := ⦗Tid_ tid⦘ ⨾ rmw G ⨾ ⦗Tid_ tid⦘;
                    data :=  ⦗Tid_ tid⦘ ⨾ data G ⨾ ⦗Tid_ tid⦘;
                    addr :=  ⦗Tid_ tid⦘ ⨾ addr G ⨾ ⦗Tid_ tid⦘;
                    ctrl :=  ⦗Tid_ tid⦘ ⨾ ctrl G ⨾ ⦗Tid_ tid⦘;
                    rmw_dep :=  ⦗Tid_ tid⦘ ⨾ rmw_dep G ⨾ ⦗Tid_ tid⦘;
                    rf := ∅₂;
                    co := ∅₂;
                 |}). 
    exists Gi.
    split.
    all: subst Gi; try unfold acts_set; simpl; auto. 
    simpl. apply set_equiv_exp_iff. ins.
    red. split.
    - ins. apply in_filterP_iff in H. desc.  red. split; auto.
    - ins. apply in_filterP_iff. red in H. desc. split; vauto.
  Qed. 
          
  Definition GOi_rel (rel: execution -> relation actid) :=
    bunion hlpr_restr (fun hlpr x y => exists GOi, (hlpr_GO GOi hlpr) /\ (rel GOi x y)).
  
  Lemma inter_subset_helper_ext {A: Type} (S S1 S2: A -> Prop):
    (forall x (Sx: S x), S1 x <-> S2 x) <-> S ∩₁ S1 ≡₁ S ∩₁ S2.
  Proof.
    ins. split; [apply inter_subset_helper| ].
    ins. unfold set_inter in H. red in H. unfold set_subset in H. desc.
    split.
    { ins. specialize_full H; vauto. desc. auto. } 
    ins. specialize_full H0; vauto. desc. auto.
  Qed. 

  Lemma REL_NINIT r a b (IN_SB: r ⊆ sb GI) (DOM_R: r ≡ ⦗R GI⦘ ⨾ r) (Rab: r a b):
    ~ is_init a /\ ~ is_init b. 
  Proof.
    rewrite (same_relation_exp DOM_R) in Rab.
    apply seq_eqv_l in Rab. desc.
    split.
    { eapply read_or_fence_is_not_init; eauto. }
    apply IN_SB in Rab0. apply no_sb_to_init in Rab0.
    apply seq_eqv_r in Rab0. desc. auto.
  Qed. 

  Lemma REL_GLOBAL_RESTR GO rel
        (RWO_RESTR_IF_SBL:
           forall Go Gi, same_behavior_local Go Gi ->
                    rel Go ≡ restr_rel (RWO Gi) (rel Gi))
        (TID_RESTR_IF_TRE: forall G G' tid,
            thread_restricted_execution G tid G' ->
            rel G' ≡ ⦗Tid_ tid⦘ ⨾ rel G ⨾ ⦗Tid_ tid⦘)
        (REL_GO: rel GO ≡ GOi_rel rel)
        (REL_E: rel GI ≡ ⦗E GI⦘ ⨾ rel GI ⨾ ⦗E GI⦘)
        (IN_SB: rel GI ⊆ sb GI)
        (DOM_R: rel GI ≡ ⦗R GI⦘ ⨾ rel GI):
    rel GO ≡ restr_rel (RWO GI) (rel GI) .
  Proof.
    ins. rewrite REL_GO. unfold GOi_rel.
      split.
      { apply inclusion_bunion_l. ins. destruct x as [thread POi PIi GIi].
        red in H. desc. unfold hlpr_GO. simpl in *.
        rewrite REL_E, <- restr_relE, restr_restr.
        red. ins. desc. specialize (RWO_RESTR_IF_SBL _ _ SBL'). 
        apply RWO_RESTR_IF_SBL in H0.
        red in H0. desc.
        specialize (TID_RESTR_IF_TRE _ _ _ RESTR').
        apply TID_RESTR_IF_TRE in H0.
        apply seq_eqv_lr in H0. desc.
        apply REL_E in H3. apply seq_eqv_lr in H3. desc.
        specialize (@inter_subset_helper_ext _ (E GIi) (RWO GIi) (Tid_ thread ∩₁ RWO GI)) as inter_subset_helper_ext. 
        destruct RESTR'. 
        red. unfold set_inter. splits; auto; splits; auto.
        all: apply inter_subset_helper_ext; vauto;
          [apply RWO_RESTR; vauto | apply tr_acts_set; red; split; auto]. }
      red. ins. red.
      red in H. desc.
      apply REL_E in H. apply seq_eqv_lr in H. desc.  
      pose proof (@REL_NINIT _ x y IN_SB DOM_R H2) as [NINITx NINITy]. 
      destruct x; [vauto| ]. destruct y; [vauto| ].
      assert (thread0 = thread).
      { apply IN_SB in H2. apply sb_tid_init in H2. des; vauto. }
      subst thread0. 
      assert (IdentMap.In thread ProgI).
      { cdes ExecI. specialize (ExecI0 _ H). des; vauto. }
      assert (exists PIi, Some PIi = IdentMap.find thread ProgI) as [PIi THREADI].
      { apply find_iff_in. red in Compiled. destruct Compiled. auto. }
      assert (exists POi, Some POi = IdentMap.find thread ProgO) as [POi THREADO].
      { apply find_iff_in. cdes Compiled. apply SAME_THREADS. auto. }
      pose proof (restr_graph GI thread) as [GIi TRE]. 
      assert (is_thread_compiled POi PIi) as COMP.
      { cdes Compiled. eapply THREADS_COMPILED; eauto. }
      exists ({| htid := thread; hPO := POi; hPI := PIi; hSGI := GIi |}).
      splits; vauto.
      forward eapply thread_execs as [GOi FOO]; eauto.
      { apply program_execution_equiv in ExecI. cdes ExecI. eapply ExecI1; eauto. }
      exists GOi. splits; vauto.
      desc. specialize (RWO_RESTR_IF_SBL _ _ FOO0). 
      apply RWO_RESTR_IF_SBL. 
        
      pose proof (RWO_RESTR TRE) as RWO_RESTR.
      specialize (@inter_subset_helper_ext _ (E GIi) (RWO GIi) (Tid_ thread ∩₁ RWO GI)) as inter_subset_helper_ext. 
      destruct TRE. 
      red. splits.
      2, 3: apply (proj2 inter_subset_helper_ext); auto; [apply tr_acts_set; red; splits; auto | red; splits; auto].
      specialize_full TID_RESTR_IF_TRE; vauto. apply TID_RESTR_IF_TRE. 
      apply seq_eqv_lr. simpl.
      splits; auto.
  Qed. 
    
  Lemma thread_execs_helper: exists GO,
      ⟪ E_STRUCT: forall e : actid, E GO e -> is_init e \/ IdentMap.In (tid e) ProgO ⟫/\
      ⟪ SAME_INIT: E GO ∩₁ is_init ≡₁ E GI ∩₁ is_init⟫ /\
      ⟪ SAME_INIT_LABELS: forall l, lab GO (InitEvent l) = Astore Xpln Opln l 0 ⟫ /\
      ⟪ SAME_CO: co GI ≡ co GO⟫ /\
      ⟪ EXT_RF: rf GO ≡ restr_rel (RWO GI) (rf GI)⟫ /\
      ⟪ RESTR_SIM: forall tid POi
        (THREAD: Some POi = IdentMap.find tid ProgO)
        GOi (RESTR: thread_restricted_execution GO tid GOi)
        GIi (RESTR: thread_restricted_execution GI tid GIi),
          Othread_execution_sim tid POi GOi /\ same_behavior_local GOi GIi ⟫ /\
      ⟪DATA_SIM: data GO ≡ restr_rel (RWO GI) (data GI) ⟫ /\
      ⟪CTRL_SIM: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI) ⟫ /\ 
      ⟪ADDR_SIM: addr GO ≡ restr_rel (RWO GI) (addr GI) ⟫ /\
      ⟪NO_RMW: rmw GO ≡ ∅₂ ⟫ /\
      ⟪NO_RMWDEP: rmw_dep GO ≡ ∅₂ ⟫. 
  Proof.
    set (all_acts := set_bunion
                       hlpr_restr
                       (fun hlpr e => exists GOi, hlpr_GO GOi hlpr /\ E GOi e)).

    set (GOi_prop := fun thread GOi =>
                       exists POi GIi,
                         Some POi = IdentMap.find thread ProgO /\
                         thread_restricted_execution GI thread GIi /\
                         Othread_execution thread POi GOi /\
                         same_behavior_local GOi GIi).
    
    assert (set_finite all_acts) as FIN_EGO. 
    { red. exists (acts GI). ins.
      do 2 red in IN. destruct IN as [[tid POi PIi GIi] [HLPR_RESTR [GOi [HLPR_GO EGOx]]]].
      cut (E GIi x).
      { ins. red in HLPR_RESTR. desc. simpl in *.
        destruct RESTR'. rewrite (set_equiv_exp tr_acts_set) in H.
        red in H. desc. auto. }
      red in HLPR_GO. desc. simpl in *.
      red in SBL'. desc. rewrite (set_equiv_exp RESTR_EVENTS) in EGOx.
      red in EGOx. desc. auto. }
    apply set_finite_alt in FIN_EGO. destruct FIN_EGO as [GO_actsset EGO].
    assert (set_finite (E GI ∩₁ is_init)) as FIN_INIT.
    { red. exists (acts GI). ins. red in IN. desc. auto. }
    apply set_finite_alt in FIN_INIT. destruct FIN_INIT as [GO_initset INIT_GO].

  set (GO :=   {| acts := GO_actsset ++ GO_initset;
                    lab := lab GI;
                    rmw := GOi_rel rmw; 
                    data := GOi_rel data;
                    addr := GOi_rel addr;
                    ctrl := GOi_rel ctrl;
                    rmw_dep := GOi_rel rmw_dep;
                    rf := restr_rel (RWO GI) (rf GI);
                    co := co GI |}).     
    
  assert (forall e (E_ACT: In e GO_actsset), exists thread index GOi,
                 e = ThreadEvent thread index /\
                 GOi_prop thread GOi) as E_GO_STRUCT.
  { ins.
    apply EGO in E_ACT. subst all_acts.
    red in E_ACT. destruct E_ACT as [[thread' POi' PI' GI'] [THREAD [GOi [EGOi_prop EGOi]]]]. 
    red in EGOi_prop. red in THREAD. desc. simpl in *. 
    red in SBL'. desc. rewrite (set_equiv_exp RESTR_EVENTS) in EGOi.
    red in EGOi. desc. 
    destruct RESTR'. rewrite (set_equiv_exp tr_acts_set) in EGOi.
    red in EGOi. desc.
    destruct e.
    { subst. exfalso. apply programs_without_tid_init.
      apply find_iff_in. simpl in THREADI'. vauto. }
    simpl in EGOi1. subst thread'. do 2 eexists. exists GOi.
    splits; eauto. red. do 2 eexists. splits; vauto. }
  
  exists GO. splits.
  11: { subst GO. simpl. split; [| basic_solver].
        apply inclusion_bunion_l. intros thread _. 
        unfold restr_rel. red. ins. desc.
        cdes H. cdes SBL'. apply RESTR_RMWDEP in H0. auto. }
  10: { subst GO. simpl. split; [| basic_solver].
        apply inclusion_bunion_l. intros thread _. 
        unfold restr_rel. red. ins. desc.
        cdes H. cdes SBL'. apply RESTR_RMW in H0. auto. }
  9: { apply (@REL_GLOBAL_RESTR GO addr); vauto.
       { ins. cdes H. auto. }
       { ins. destruct H. auto. }
       { apply (wf_addrE WFI). }
       { apply (addr_in_sb WFI). }
       apply (seq_eqv_lr_l (wf_addrD WFI)). }
  8: { apply (@REL_GLOBAL_RESTR GO ctrl); vauto.
       { ins. cdes H. auto. }
       { ins. destruct H. auto. }
       { apply (wf_ctrlE WFI). }
       { apply (ctrl_in_sb WFI). }
       apply (wf_ctrlD WFI). }
  7: { apply (@REL_GLOBAL_RESTR GO data); vauto.
       { ins. cdes H. auto. }
       { ins. destruct H. auto. }
       { apply (wf_dataE WFI). }
       { apply (data_in_sb WFI). }
       apply (seq_eqv_lr_l (wf_dataD WFI)). }
  { subst GO. unfold acts_set. simpl. ins.
    destruct e; [by vauto| ].
    right. simpl.
    apply in_app_or in H. des.
    2: { apply INIT_GO in H. red in H. desc.
         unfold is_init in H0. vauto. }
    apply E_GO_STRUCT in H. desc. inversion H. subst.
    red in H0. desc. apply find_iff_in. eauto. }
  { subst GO. unfold acts_set. simpl.
    assert (forall {A: Type} (l1 l2: list A), (fun x => In x (l1 ++ l2)) ≡₁ (fun x => In x l1) ∪₁ (fun x => In x l2)) as IN_SET_UNION.
    { ins. apply set_equiv_exp_iff. ins. split.
      { ins. red. apply in_app_or. auto. }
      ins. red in H. apply in_or_app. auto. }
    rewrite IN_SET_UNION, set_inter_union_l.
    arewrite ((fun x : actid => In x GO_actsset) ∩₁ (fun a : actid => is_init a) ≡₁ ∅).
    { split; [| basic_solver]. red. ins. red in H. desc.
      apply E_GO_STRUCT in H. desc. subst. unfold is_init in H0. vauto. }
    remove_emptiness. rewrite <- set_interK with (s := is_init) at 2.
    rewrite <- set_interA. apply set_equiv_inter; [| basic_solver].
    symmetry. apply set_equiv_exp_iff. apply INIT_GO. }
  2: { vauto. }
  2: { vauto. }
  { simpl. destruct WFI. auto. }
  ins.
  assert (exists PIi, Some PIi = IdentMap.find tid ProgI) as [PIi THREADI].
  { apply find_iff_in. red in Compiled. destruct Compiled. apply H.
    apply find_iff_in. vauto. }
  assert (is_thread_compiled POi PIi) as COMP.
  { red in Compiled. destruct Compiled. red in H0. eapply H0; vauto. }
  assert (thread_execution tid PIi GIi) as EXECIi. 
  { apply program_execution_equiv in ExecI. destruct ExecI.
    apply H0; auto. }
  pose proof (thread_execs COMP EXECIi) as [SGO [OEXEC SBL]]. desc.
  cut (graphs_sim_weak SGO GOi).
  { ins. split.
    { red. red in OEXEC. desc.
      exists s. splits; vauto. }
    eapply sbl_sim; vauto. }
  assert (forall rel
            (RWO_RESTR_IF_SBL: forall Go Gi,
                same_behavior_local Go Gi ->
                rel Go ≡ restr_rel (RWO Gi) (rel Gi))
            (TID_RESTR_IF_TRE: forall G G' tid,
                thread_restricted_execution G tid G' ->
                rel G' ≡ ⦗Tid_ tid⦘ ⨾ rel G ⨾ ⦗Tid_ tid⦘)
            (REL_GO: rel GO ≡ GOi_rel rel)
            (REL_EQ_IF_GSW: forall GOi', graphs_sim_weak SGO GOi' -> rel SGO ≡ rel GOi'),
             rel SGO ≡ rel GOi) as INTRA_REL_HELPER. 
  { ins.
    rewrite (RWO_RESTR_IF_SBL _ _ SBL).
    rewrite (TID_RESTR_IF_TRE _ _ _ RESTR). rewrite REL_GO.  
    unfold GOi_rel.
    rewrite seq_bunion_l, seq_bunion_r.
    apply same_relation_exp_iff. ins. split.
    { intros [RELxy [RWOx RWOy]]. 
      exists ({| htid := tid; hPO := POi; hPI := PIi; hSGI := GIi |}).
      splits; vauto. apply seq_eqv_lr.
      rewrite (same_relation_exp (TID_RESTR_IF_TRE _ _ _ RESTR0)) in RELxy.
      apply seq_eqv_lr in RELxy. desc.
      splits; vauto. 
      exists SGO. splits.
      { unfold hlpr_GO. simpl. destruct SBL. desc. splits; vauto. }
      rewrite (same_relation_exp (RWO_RESTR_IF_SBL _ _ SBL)).
      red. splits; auto.
      rewrite (same_relation_exp (TID_RESTR_IF_TRE _ _ _ RESTR0)). 
      apply seq_eqv_lr. splits; auto. }
    { ins. red in H. destruct H as [[thread' POi' PIi' GIi'] [HLPR_RESTR BAR]].
      apply seq_eqv_lr in BAR. destruct BAR as [TIDx [BAR TIDy]].
      destruct BAR as [GOi' [[OEXEC' SBL'] REL'xy]].
      red in SBL'. 
      red in HLPR_RESTR. desc. simpl in *.
      cut (graphs_sim_weak SGO GOi').
      { ins. red in H.
        specialize (REL_EQ_IF_GSW _ H). 
        desc.
        apply (RWO_RESTR_IF_SBL _ _ SBL).
        apply (same_relation_exp REL_EQ_IF_GSW). auto. }
      cut (graphs_sim_weak GIi GIi').
      { ins.
        red in SBL'. desc. 
        eapply sbl_sim_rect; vauto.
        eapply wf_tre_intra_E; vauto. }
      eapply tre_sim_weak; vauto. 
      replace thread' with (tid x) in *; [congruence| ]. 
      rewrite (same_relation_exp (RWO_RESTR_IF_SBL _ _ SBL')) in REL'xy.
      red in REL'xy. desc.
      rewrite (same_relation_exp (TID_RESTR_IF_TRE _ _ _ RESTR')) in REL'xy. 
      apply seq_eqv_lr in REL'xy. desc. vauto. }
  }
  assert (E SGO ≡₁ E GOi) as E_EQUIV. 
  { symmetry. 
    rewrite tr_acts_set; eauto. subst GO. unfold acts_set at 1. simpl.
    arewrite ((fun x : actid => In x (GO_actsset ++ GO_initset)) ∩₁ Tid_ tid ≡₁ ((fun x : actid => In x (GO_actsset))  ∩₁ Tid_ tid)).
    { rewrite IN_SET_UNION. rewrite set_inter_union_l.
      arewrite ((fun x : actid => In x GO_initset) ∩₁ Tid_ tid ≡₁ ∅); [| basic_solver].
      split; [| basic_solver]. red. ins. red in H. desc.
      subst. apply INIT_GO in H. red in H. desc. destruct x; vauto.
      red. apply programs_without_tid_init. apply find_iff_in. vauto. }
    arewrite ((fun x : actid => In x GO_actsset) ≡₁ all_acts).
    { apply set_equiv_exp_iff. ins. symmetry. vauto. }
    unfold all_acts.
    rewrite <- set_bunion_inter_compat_r.
    unfold set_inter.
    arewrite ((⋃₁x ∈ hlpr_restr,
               fun x0 =>
                 (exists GOi0, hlpr_GO GOi0 x /\ E GOi0 x0) /\
                 Events.tid x0 = tid)
                ≡₁ (⋃₁x ∈ hlpr_restr,
                    fun x0 =>
                      (exists GOi0, hlpr_GO GOi0 x /\ E GOi0 x0 /\
                               Events.tid x0 = tid))) by basic_solver 100.
    apply set_equiv_exp_iff. ins. red. split.
    2: { ins. red. exists ({| htid := tid; hPO := POi; hPI := PIi; hSGI := GIi |}).
         splits; vauto.
         exists SGO. splits; vauto.
         red in SBL. desc.
         rewrite (set_equiv_exp RESTR_EVENTS) in H.
         red in H. desc.
         destruct RESTR0. rewrite (set_equiv_exp tr_acts_set) in H.
         red in H. desc. auto. }             
    intros EGOx. cut (E SGO x); [ins; vauto| ].
    red in EGOx.
    destruct EGOx as [[thread' POi' PIi' GIi'] [HLPR_RESTR [GOi' [HLPR_GO [EGOi'x TIDx]]]]]. 
    destruct x.
    { simpl in *. exfalso.
      apply programs_without_tid_init. apply find_iff_in. vauto. }
    simpl in *. subst tid. 
    red in HLPR_RESTR. red in HLPR_GO. desc. simpl in *. 
    red in SBL'. desc. 
    assert (thread' = thread).
    { rewrite (set_equiv_exp RESTR_EVENTS) in EGOi'x. 
      red in EGOi'x. desc.
      destruct RESTR'. rewrite (set_equiv_exp tr_acts_set) in EGOi'x.
      red in EGOi'x. desc. vauto. }
    subst thread'. assert (PIi' = PIi /\ POi' = POi) by (split; congruence).
    desc. subst PIi' POi'. clear THREADI' THREADO'. 
    cut (graphs_sim_weak SGO GOi').
    { ins. red in H. desc. apply H. auto. }
    cut (graphs_sim_weak GIi GIi').
    { ins.
      red in SBL. desc. 
      eapply sbl_sim_rect; vauto.
      eapply wf_tre_intra_E; vauto. }
    eapply tre_sim_weak; vauto. }      
  red. splits; auto. 
  { intros e ESGOx.
    red in SBL. desc. rewrite SAME_LAB; auto.
    destruct RESTR. rewrite tr_lab; [| by apply E_EQUIV].
    subst GO. simpl in *.
    destruct RESTR0. apply tr_lab0.
    rewrite (set_equiv_exp RESTR_EVENTS) in ESGOx. red in ESGOx. desc. auto. }
  all: try (by apply INTRA_REL_HELPER; vauto; ins; destruct H; desc; vauto).
  { apply INTRA_REL_HELPER.
    { ins. red in H. desc. rewrite RESTR_RMW.
      rewrite restr_relE. arewrite (rmw Gi ≡ rmw Gi ⨾ ⦗codom_rel (rmw Gi)⦘) by basic_solver.
      rewrite <- id_inter. unfold RWO. basic_solver. }
    { ins. destruct H. auto. }
    { subst GO. auto. }
    ins. cdes H. auto. }
  red in SBL. desc. rewrite RESTR_RMWDEP. destruct RESTR.
  rewrite tr_rmw_dep. subst GO. simpl. unfold GOi_rel.
  split; [basic_solver| ]. rewrite seq_bunion_l, seq_bunion_r.
  apply inclusion_bunion_l. ins. red. ins.
  apply seq_eqv_lr in H0. desc. subst. red in H1. desc.
  destruct x. simpl in *. red in H. desc. simpl in *.
  red in SBL'. desc. rewrite (same_relation_exp RESTR_RMWDEP0) in H3. auto.
  Qed. 
  
  
End BUILD_OMM_GRAPH. 