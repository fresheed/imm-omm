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
Require Import OCamlToimm_s_prog_bounded_properties. 
Require Import OCamlToimm_s_compcorrhelpers. 
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


Definition same_keys {A B: Type} (map1: IdentMap.t A) (map2: IdentMap.t B)
  := forall key, IdentMap.In key map1 <-> IdentMap.In key map2.

  (* Definition restrict (G: execution) (tid: thread_id): execution. *)
  (*   set (thread_local := fun x y => Events.tid x = tid /\ Events.tid y = tid).  *)
  (*   exact {| *)
  (*       acts := filterP (fun e => is_tid tid e) (acts G); *)
  (*       lab := lab G; (* TODO: restrict? *) *)
  (*       rmw := rmw G ∩ thread_local; *)
  (*       data := data G ∩ thread_local; *)
  (*       addr := addr G ∩ thread_local; *)
  (*       ctrl := ctrl G ∩ thread_local; *)
  (*       rmw_dep := rmw_dep G ∩ thread_local; *)
  (*       rf := ∅₂; *)
  (*       co := ∅₂; |}. *)
  (* Defined. *)
  (* Definition g2tsg' (G: execution): *)
  (*   exists (TSG: thread_separated_graph), True.  *)
  (*   set (events_tids := map (fun e => Events.tid e) (acts G)).  *)
  (*   assert (ListDec.decidable_eq thread_id) as DECIDE_TID.  *)
  (*   { unfold thread_id, Ident.t. red. ins. red.  *)
  (*     pose proof (DecidableTypeEx.Positive_as_DT.eq_dec x y).  *)
  (*     destruct H; auto. } *)
  (*   pose proof (ListDec.uniquify DECIDE_TID events_tids) as [tids TIDS_UNIQUE].  *)
  (*   set (Gis_list := map (fun tid => (tid, restrict G tid)) tids).  *)
  (*   (* TODO: remove rmw from tsg? *)     *)
  (*   exists {| *)
  (*       Gis := UsualFMapPositive.UsualPositiveMap.Properties.of_list Gis_list; *)
  (*       Einit_tsg := fun e => In e (filterP (fun e' => is_tid tid_init e') (acts G)); *)
  (*       rf_tsg := rf G; *)
  (*       co_tsg := co G; *)
  (*       rmw_tsg := rmw G |}.  *)
  (*   auto.  *)
  (* Defined. *)
 
Section OCamlMM_TO_IMM_S_PROG.
  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  Notation "'F' G" := (fun a => is_true (is_f G.(lab) a)) (at level 1).
  Notation "'ORlx' G" := (fun a => is_true (is_only_rlx G.(lab) a)) (at level 1).
  Notation "'Sc' G" := (fun a => is_true (is_sc G.(lab) a)) (at level 1). 
  Notation "'Acq' G" := (fun a => is_true (is_acq G.(lab) a)) (at level 1). 
  Notation "'Acqrel' G" := (fun a => is_true (is_acqrel G.(lab) a)) (at level 1). 

  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI) (* (WFL: Wf_local SGI) *):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI
           (* /\ Wf_local SGO *)
  . 
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
      apply is_terminal_pc_bounded in TERMINAL. 
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
        { replace BPI with (binstrs bsti_fin); auto. symmetry. 
          apply (@inclusion_t_ind _ (block_step tid) (fun x y => binstrs x = binstrs y)).
          { red. ins. eapply SAME_BINSTRS. eauto. }
          { red. ins. congruence. }
          apply t_step_rt. exists bsti_i. split.
          { apply bs_extract. auto. }
          apply OB_B. apply crt_num_steps. eexists. eauto. }

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

  (* Lemma same_beh_implies_similar_rels GO GI (SB: same_behavior GO GI): *)
  (*   ⟪ SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘⟫ /\ *)
  (*   (* ⟪ SC': Sc GO ≡₁ Sc GI ⟫ /\ *) *)
  (*   ⟪ SC': Sc GO ≡₁ RWO GI ∩₁ Sc GI ⟫ /\ *)
  (*   ⟪ FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI ⟫. *)
  (* Proof. *)
  (*   red in SB. des. red in SAME_LOCAL. desc. *)
  (*   splits. *)
  (*   { unfold Execution.sb. *)
  (*     rewrite !seqA. do 2 seq_rewrite <- id_inter. *)
  (*     rewrite set_interC.       *)
  (*     rewrite <- RESTR_EVENTS. auto. } *)
  (*   { admit. } *)
  (*   admit.  *)
  (* (*   red in SB. desc. red in SAME_LOCAL. desc.  *) *)
  (* (*   assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘). *) *)
  (* (*   { unfold Execution.sb.         *) *)
  (* (*     rewrite !seqA. do 2 seq_rewrite <- id_inter. *) *)
  (* (*     rewrite set_interC.  *) *)
  (* (*     rewrite RESTR_EVENTS.  *) *)
  (* (*     basic_solver. } *) *)
  (* (*   splits; auto.  *) *)
  (* (*   { rewrite SAME_LAB. auto. } *) *)
  (* (*   { unfold fr. rewrite SAME_CO. rewrite <- seqA. apply seq_more; [| basic_solver]. *) *)
  (* (*     rewrite EXT_RF.  basic_solver. } *) *)
  (*   (* Qed.  *) *)
  (* Admitted.  *)

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

  Lemma same_beh_implies_similar_intrarels GO GI (SB: same_behavior GO GI):
    ⟪DATA_SIM: data GO ≡ restr_rel (RWO GI) (data GI) ⟫ /\
    ⟪CTRL_SIM: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI) ⟫ /\ 
    ⟪ADDR_SIM: addr GO ≡ restr_rel (RWO GI) (addr GI) ⟫ /\
    ⟪SB_SIM: sb GO ≡ restr_rel (RWO GI) (sb GI) ⟫ /\
    ⟪NO_RMW: rmw GO ≡ ∅₂ ⟫ /\
    ⟪NO_RMWDEP: rmw_dep GO ≡ ∅₂ ⟫.
  Proof.
    
  Admitted.     

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

  Lemma RESTR_SEQ (r1 r2: relation actid) (D: actid -> Prop):
    restr_rel D r1 ⨾ restr_rel D r2 ⊆ restr_rel D (r1 ⨾ r2). 
  Proof. ins. basic_solver. Qed.

  (* TODO: generalize all of it*)
  Lemma W_SIM GO GI (SBL: same_behavior_local GO GI):
    E GO ∩₁ W GO ≡₁ E GO ∩₁ W GI.
  Proof. 
    red in SBL. apply set_equiv_exp_iff.
    ins. split.
    { ins. red in H. desc. red. split; auto.
      unfold is_w. rewrite <- (SAME_LAB); auto. }
    { ins. red in H. desc. red. split; auto.
      unfold is_w. rewrite (SAME_LAB); auto. }
  Qed.
  
  Lemma R_SIM GO GI (SBL: same_behavior_local GO GI):
    E GO ∩₁ R GO ≡₁ E GO ∩₁ R GI.
  Proof.
    red in SBL. apply set_equiv_exp_iff.
    ins. split.
    { ins. red in H. desc. red. split; auto.
      unfold is_r. rewrite <- (SAME_LAB); auto. }
    { ins. red in H. desc. red. split; auto.
      unfold is_r. rewrite (SAME_LAB); auto. }
  Qed. 

  Lemma RW_SIM GO GI (SBL: same_behavior_local GO GI)
    : E GO ∩₁ RW GO ≡₁ E GO ∩₁ RW GI.
  Proof. rewrite !set_inter_union_r. rewrite W_SIM, R_SIM; eauto. Qed. 

  
  Lemma SC_SIM GO GI (SBL: same_behavior_local GO GI):
    E GO ∩₁ Sc GO ≡₁ E GO ∩₁ Sc GI.
  Proof.
    red in SBL. apply set_equiv_exp_iff.
    ins. split.
    { ins. red in H. desc. red. split; auto.
      unfold is_sc, Events.mod. rewrite <- (SAME_LAB); auto. }
    { ins. red in H. desc. red. split; auto.
      unfold is_sc, Events.mod. rewrite (SAME_LAB); auto. }
  Qed. 

  Lemma Wf_subgraph GO GI (SAME_BEH: same_behavior GO GI) (WF: Wf GI): Wf GO.
  Proof.
    pose proof SAME_BEH as SAME_BEH'.
    red in SAME_BEH. desc. red in SAME_LOCAL. desc.
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { unfold Execution.sb.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC.
      rewrite RESTR_EVENTS.
      basic_solver. }
    (* pose proof (same_beh_implies_similar_rels SAME_BEH).  *)
    symmetry in SAME_CO.
    assert (forall (r1 r2 r3: relation actid), r1 ⊆ r2 -> r1 \ r3 ⊆ r2 \r3) as MINUS_INCL. 
    { ins. basic_solver. }
    assert (forall (r1 r3: relation actid) S1 S2, r1 ≡ ⦗S1⦘ ⨾ r1 ⨾ ⦗S2⦘ -> r1 \ r3 ≡ ⦗S1⦘ ⨾ (r1 \ r3) ⨾ ⦗S2⦘) as MINUS_EQUIV. 
    { ins. seq_rewrite H. basic_solver. }
    (* TODO: should we include addr, ctrl equality in same_behavior? *)
    pose proof (same_beh_implies_similar_intrarels SAME_BEH'). desc. 
    inversion WF. 
    (* assert (rf GO ≡ restr_rel (RWO GI) (rf GI)) as RF_SIM.  *)
    (* { rewrite EXT_RF. rewrite wf_rfD. rewrite restr_relE. *)
    (*   rewrite !seqA. *)
    (*   arewrite (⦗(RWO GI)⦘ ⨾ ⦗W GI⦘ ≡ ⦗W GI⦘). *)
    (*   { rewrite <- id_inter. apply eqv_rel_more. split; [basic_solver| ]. *)
    (*     apply set_subset_inter_r. split; auto. *)
    (*     unfold RWO.  *)
    (*     rewrite wf_rmwD. *)
    (*     red. ins. red. split; [basic_solver| ].  *)
    (*     red. ins. red in H0. desc. apply seq_eqv_lr in H0. desc. *)
    (*     type_solver. } *)
    (*   arewrite (⦗R GI⦘ ⨾ ⦗(RWO GI)⦘ ≡ ⦗R GI⦘ ⨾ ⦗set_compl (dom_rel (rmw GI))⦘); [| basic_solver]. *)
    (*   rewrite <- !id_inter. apply eqv_rel_more. *)
    (*   unfold RWO.  *)
    (*   seq_rewrite set_inter_minus_r. *)
    (*   arewrite (R GI ∩₁ RW GI ≡₁ R GI) by basic_solver. } *)
    assert (co GO ≡ ⦗E GO⦘ ⨾ co GO ⨾ ⦗E GO⦘) as ECO. 
    { rewrite RESTR_EVENTS, <- SAME_CO.
      rewrite !id_inter. rewrite seq_eqvC. rewrite seqA. rewrite seq_eqvC.
      seq_rewrite <- wf_coE.
      split; [| basic_solver].
      rewrite wf_coD at 1.
      assert (W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
      { apply inclusion_minus. split; [basic_solver |].
        rewrite wf_rmwD. type_solver. }
      apply seq_mori.
      { apply eqv_rel_mori. auto. }
      apply seq_mori; [basic_solver|].
      apply eqv_rel_mori. auto. }
    assert (rf GO ≡ ⦗E GO⦘ ⨾ rf GO ⨾ ⦗E GO⦘) as ERF. 
    { rewrite RESTR_RF, RESTR_EVENTS. fold (RWO GI).
      rewrite set_interC at 1. do 2 rewrite id_inter.
      rewrite !seqA. do 2 seq_rewrite <- restr_relE.
      rewrite restrC with (d' := (RWO GI)). rewrite restr_restr, set_interK.
      apply restr_rel_more; [basic_solver|].
      rewrite restr_relE. auto. }
    
    assert (DATA_INCL: data GO ⊆ sb GO).
    { rewrite DATA_SIM, SB_SIM. apply restr_rel_mori; basic_solver. }
    assert (ADDR_INCL: addr GO ⊆ sb GO).
    { rewrite ADDR_SIM, SB_SIM. apply restr_rel_mori; basic_solver. }
    assert (CTRL_INCL: ctrl GO ⊆ sb GO).
    { rewrite CTRL_SIM, SB_SIM. apply restr_rel_mori; basic_solver. }
    
    (* red in SAME_BEH'. desc.   *)
    split; vauto.
    all: try (seq_rewrite NO_RMW; basic_solver). 
    all: try (seq_rewrite NO_RMWDEP; basic_solver). 
    { ins. des.
      specialize (wf_index a b). forward eapply wf_index; auto.
      destruct RESTR_EVENTS as [EGO_EGI _]. red in EGO_EGI.
      splits; auto.
      { specialize (EGO_EGI a H). red in EGO_EGI. desc. auto. } 
      specialize (EGO_EGI b H0). red in EGO_EGI. desc. auto. }
    { rewrite (@SUPSET_RESTR _ (data GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite W_SIM, R_SIM; eauto. 
      rewrite set_interC with (s' := W GI). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗W GI⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite DATA_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      apply restr_rel_more; auto. red. splits; auto. red. splits; auto. }
    { rewrite (@SUPSET_RESTR _ (addr GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite R_SIM, RW_SIM; eauto. 
      rewrite set_interC with (s' := RW GI). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗RW GI⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite ADDR_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l. 
      apply restr_rel_more; auto. red. splits; auto. red. splits; auto. }
    { rewrite <- (seq_id_r (ctrl GO)) at 2.  
      rewrite (@SUPSET_RESTR _ (ctrl GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite R_SIM; eauto. (* TRUE_SIM. *)
      rewrite set_interC with (s' := (fun _ : actid => True)). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗fun _ : actid => True⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite CTRL_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      rewrite seq_id_r. 
      apply restr_rel_more; auto.
      red. splits; auto. }
    { rewrite CTRL_SIM, SB_SIM. rewrite RESTR_SEQ. apply restr_rel_mori; auto. }
    { rewrite ERF.
      rewrite RESTR_RF; eauto. 
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. rewrite W_SIM, R_SIM; eauto. 
      rewrite set_interC with (s' := R GI). rewrite !id_inter.
      rewrite !seqA. seq_rewrite <- !restr_relE.
      rewrite <- seqA with  (r3 := ⦗E GO⦘). rewrite <- seqA with  (r1 := ⦗W GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; [basic_solver|].
      rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      apply restr_rel_more; [basic_solver|]. auto.
      red. splits; auto. red. splits; auto. }
    { rewrite ERF. red. ins.
      apply seq_eqv_lr in H. desc.
      red.
      rewrite (same_relation_exp RESTR_RF) in H0. red in H0. desc. 
      replace (loc (lab GO) x) with (loc (lab GI) x).
      replace (loc (lab GO) y) with (loc (lab GI) y).
      apply wf_rfl; auto.
      all: unfold loc; rewrite SAME_LAB; auto. }
    { red. ins.
      rewrite (same_relation_exp ERF) in H. apply seq_eqv_lr in H. desc.
      rewrite (same_relation_exp RESTR_RF) in H0. red in H0. desc.
      replace (val (lab GO) a) with (val (lab GI) a).
      replace (val (lab GO) b) with (val (lab GI) b).
      apply wf_rfv; auto. 
      all: unfold val; rewrite SAME_LAB; auto. }
    { rewrite RESTR_RF. rewrite restr_relE. rewrite !transp_seq.
      rewrite !transp_eqv_rel. rewrite seqA, <- restr_relE.
      apply functional_restr. auto. }
    { rewrite ECO at 2.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. rewrite W_SIM; eauto. 
      rewrite set_interC at 2. do 2 rewrite id_inter.
      rewrite <- SAME_CO at 2. rewrite !seqA. seq_rewrite <- wf_coD.
      rewrite SAME_CO. apply ECO.
      red. splits; auto. }
    { rewrite ECO. red. ins.
      apply seq_eqv_lr in H. desc.
      red.
      symmetry in SAME_CO. 
      rewrite (same_relation_exp SAME_CO) in H0.
      replace (loc (lab GO) x) with (loc (lab GI) x).
      replace (loc (lab GO) y) with (loc (lab GI) y).
      apply wf_col; auto.
      all: unfold loc; rewrite SAME_LAB; auto. }
    { rewrite <- SAME_CO. auto. }
    { ins. specialize (wf_co_total ol).
      forward eapply (@is_total_more _ (E GI ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol)) (E GO ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol))).
      { apply set_equiv_inter; [| basic_solver].
        rewrite RESTR_EVENTS.
        unfold RWO. 
        rewrite set_interA. rewrite set_inter_minus_l.
        arewrite (RW GI ∩₁ W GI ≡₁ W GI) by basic_solver.
        rewrite empty_inter_minus_same; [auto| ]. 
        rewrite wf_rmwD. type_solver. }
      { eapply SAME_CO. }
      intros [impl _].
      arewrite (E GO ∩₁ W GO ∩₁ (fun x : actid => loc (lab GO) x = ol) ≡₁ E GO ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol)). 
      2: { apply impl. auto. }
      rewrite W_SIM; eauto. 
      apply set_equiv_exp_iff. ins. split.
      { ins. desc. red in H. desc. red in H. desc.
        red. split; [basic_solver|].
        rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. } 
      { ins. desc. red in H. desc. red in H. desc.
        red. split; [basic_solver|].
        rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. }
      red. splits; auto. }
    { rewrite <- SAME_CO. auto. }
    { ins.
      eapply SAME_INIT.
      red. splits; auto.
      apply wf_init. desc.
      exists b. split.
      { apply RESTR_EVENTS. auto. }
      rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. }
    intros. rewrite SAME_INIT_LAB. apply wf_init_lab.     
  Qed.

  
End OCamlMM_TO_IMM_S_PROG.



Section CorrectedDefinitions.

  Notation "'E' G" := G.(acts_set) (at level 1).

  Definition program_execution_corrected (prog : Prog.t) G :=
    (forall e : actid, E G e -> is_init e \/ IdentMap.In (tid e) prog) /\
    (forall (thread : IdentMap.key) (PIi : list Instr.t)
       (THREAD: Some PIi = IdentMap.find thread prog)
       Gi (THREAD_EXEC: thread_restricted_execution G thread Gi),
        thread_execution thread PIi Gi).

  Definition Oprogram_execution_corrected prog (OPROG: OCamlProgram prog) G :=
    (forall e (IN: G.(acts_set) e), is_init e \/ IdentMap.In (tid e) prog) /\
    (forall (thread : IdentMap.key) (POi : list Instr.t)
       (THREAD: Some POi = IdentMap.find thread prog)
       Gi (THREAD_EXEC: thread_restricted_execution G thread Gi),
        Othread_execution thread POi Gi).
  
  Lemma program_execution_equiv (prog : Prog.t) G:
    program_execution_corrected prog G <-> program_execution prog G.
  Proof. Admitted.

  Lemma Oprogram_execution_equiv prog G (OPROG: OCamlProgram prog):
    Oprogram_execution_corrected OPROG G <-> Oprogram_execution OPROG G.
  Proof. Admitted.

End CorrectedDefinitions.   

Section CompilationCorrectness.

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
  (* Notation "'Loc_' G l" := (fun x => loc (G.(lab) x) = l) (at level 1). *)
  Variable ProgO ProgI: Prog.Prog.t.
  Hypothesis Compiled: is_compiled ProgO ProgI.
  Hypothesis OCamlProgO: OCamlProgram ProgO.
  
  Variable GI: execution.
  Hypothesis WFI: Wf GI.
  Variable sc: relation actid. 
  Hypothesis ExecI: program_execution ProgI GI.
  Hypothesis IPC: imm_s.imm_psc_consistent GI sc.


  Lemma find_iff_in {A: Type} (M: IdentMap.t A) k: 
    IdentMap.In k M <-> exists elt, Some elt = IdentMap.find k M. 
  Proof.
    pose proof (@UsualFMapPositive.UsualPositiveMap.Facts.in_find_iff _ M k).
    pose proof OPT_VAL (IdentMap.find k M).
    eapply iff_stepl.
    - eapply H0. 
    - symmetry. eauto.
  Qed.

  Lemma events_continuos n tid: forall st (REACH: (step tid) ^^ n (init (instrs st)) st),
      forall i (INDEX: i < eindex st), E (G st) (ThreadEvent tid i).
  Proof.
    induction n.
    { intros st REACH. apply steps0 in REACH.
      rewrite <- REACH. unfold init, init_execution, acts_set.
      simpl. intros. omega. }
    intros.
    remember (ThreadEvent tid i) as ev.
    rewrite step_prev in REACH. destruct REACH as [st' [STEPS' STEP]].
    replace (instrs st) with (instrs st') in STEPS'.
    2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
    destruct (le_lt_dec (eindex st') i) as [INDEX' | INDEX'].
    2: { specialize (IHn st' STEPS' i INDEX').
         forward eapply (@preserve_event tid st' st); eauto. 
         { apply rt_step. auto. }
         intros. congruence. }
    do 2 (red in STEP; desc). subst.
    inversion ISTEP0.
    all: (rewrite UG; unfold acts_set; simpl).
    all: rewrite UINDEX in INDEX.
    (* get rid of steps which preserve graph *)
    all: try (exfalso; omega).
    (* one event addition *)
    1-4: (left; replace i with (eindex st'); auto; omega).
    (* two events addition *)
    all: cut (i = eindex st' \/ i = eindex st' + 1); [intros; des; vauto | omega]. 
  Qed.

  Lemma step_events_struct n tid:
    forall st (REACH: (step tid) ^^ n (init (instrs st)) st),
      E (G st) ⊆₁ Tid_ tid ∩₁ set_compl (fun e => is_init e). 
  Proof.
    induction n.
    { intros st REACH x. apply steps0 in REACH.
      rewrite <- REACH. unfold init, init_execution, acts_set. simpl. vauto. }
    intros st REACH. 
    rewrite step_prev in REACH. destruct REACH as [st' [STEPS' STEP]].
    replace (instrs st) with (instrs st') in STEPS'.
    2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
    specialize (IHn st' STEPS').
    do 2 (red in STEP; desc).
    assert (OR_SET: forall {A: Type} (X Y Z: A -> Prop), (fun e => X e \/ Y e) ⊆₁ Z <-> X ∪₁ Y ⊆₁ Z).
    { intros. basic_solver. }
    inversion ISTEP0.
    all: rewrite UG. 
    all: try auto.
    all: unfold add, acts_set; simpl.
    (* one event addition *)
    1-4: apply set_subset_union_l; splits; [ basic_solver | auto ]. 
    (* two event addition*)
    all: apply set_subset_union_l; splits; [basic_solver | ].
    all: apply set_subset_union_l; splits; [ basic_solver | auto ].
  Qed. 
    

  (* Lemma omm_premises_thread_local TSG (OMM_PREM_THREADS: forall tid Gi (THREAD_Gi: Some Gi = IdentMap.find tid (Gis TSG)), omm_premises_hold Gi): *)
  (*   omm_premises_hold (tsg2g TSG).  *)
  (* Proof. *)
  (*   remember (tsg2g TSG) as G. *)
  (*   (* assert (merge : relation actid -> thread_separated_graph -> relation actid). *) *)
  (*   (* { admit. } *) *)
  (*   (* assert (forall (P: execution -> actid -> Prop), *) *)
  (*   (*            P G ≡₁ fun e => exists tid Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ *) *)
  (*   (*                                   P Gi e) as EV_PROPS_UNION by admit.  *) *)
  (*   (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_w G.(lab) a))). *) *)
  (*   (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_r G.(lab) a))).  *) *)
  (*   (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_sc G.(lab) a))). *) *)
  (*   (* assert (forall (r1 r2: relation actid), codom_rel (r1 ∪ r2) ≡₁ codom_rel r1 ∪₁ codom_rel r2). *) *)
  (*   (* { ins. basic_solver. } *) *)
  (*   assert (E G ≡₁ set_bunion (fun _ => True) (fun tid e => exists Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ E (Gi) e)) as E_BUNION by admit.      *)
  (*   (* red. splits. *) *)
  (*   (* { seq_rewrite H. rewrite H1.  *) *)
  (*   (*   rewrite (EV_PROPS_UNION (fun G a => is_true (is_f G.(lab) a))). *) *)
  (*   (* assert (E G ≡₁ fun e => exists tid Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ *) *)
  (*   (*                                E Gi e) by admit. *) *)
    
    
  (* Admitted.   *)

  Lemma programs_without_tid_init: ~ (IdentMap.In tid_init ProgI).
  Proof. Admitted.

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

  Lemma init_equiv: Tid_ tid_init ∩₁ E GI ≡₁ is_init ∩₁ E GI.
  Proof.
    split.
    2: { rewrite is_init_tid. auto. }
    red. ins. red in H. desc. red. split; auto.
    red in ExecI. destruct ExecI as [E_STRUCT _].
    destruct (E_STRUCT _ H0); auto.
    destruct x; vauto.
    exfalso. simpl in *. subst.
    apply programs_without_tid_init. auto. 
  Qed. 
  
  Lemma immediate_sb_restr G Gi thread (TRE: thread_restricted_execution G thread Gi) (NINIT: thread <> tid_init):
    immediate (sb Gi) ≡ ⦗Tid_ thread⦘ ⨾ immediate (sb G) ⨾ ⦗Tid_ thread⦘.
  Proof.
    destruct TRE. 
    apply same_relation_exp_iff. red. ins. split.
    { unfold immediate. intros [SB SB_IMM]. desc.
      red in SB. apply seq_eqv_lr in SB. destruct SB as [E'x [ESBxy E'y]]. 
      rewrite (set_equiv_exp tr_acts_set) in E'x, E'y. unfold set_inter in E'x, E'y. desc.  
      apply seq_eqv_lr. splits; auto.
      { red. apply seq_eqv_lr. splits; auto. }
      subst. destruct x; vauto.
      destruct y; vauto. simpl in *. desc. subst. 
      ins. unfold sb in R1, R2. apply seq_eqv_lr in R1. apply seq_eqv_lr in R2. desc.  
      unfold sb in *. apply SB_IMM with (c := c); auto.
      { apply seq_eqv_lr. splits; auto; rewrite (set_equiv_exp tr_acts_set); red; split; vauto.
        destruct c; vauto. simpl. red in R0. desc. auto. } 
      { apply seq_eqv_lr. splits; auto; rewrite (set_equiv_exp tr_acts_set); red; split; vauto.
        destruct c; vauto. simpl. red in R0. desc. auto. } }
    { ins. unfold sb in *. apply seq_eqv_lr in H. desc. subst. 
      red in H0. destruct H0 as [SBxy SB_IMMxy].
      apply seq_eqv_lr in SBxy. destruct SBxy as [Ex [ESBxy Ey]]. 
      assert (E Gi x) as E'x.
      { apply tr_acts_set. red. splits; vauto. }
      assert (E Gi y) as E'y.
      { apply tr_acts_set. red. splits; vauto. }
      red. split.
      { apply seq_eqv_lr. splits; auto. }
      ins. apply seq_eqv_lr in R1. apply seq_eqv_lr in R2. desc.
      rewrite (set_equiv_exp tr_acts_set) in R5. red in R5. desc.  
      apply SB_IMMxy with (c := c); apply seq_eqv_lr; splits; auto. }
  Qed.

  Lemma bunion_more_alt: forall (A B : Type) (x y : A -> Prop),
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
  
  Lemma omm_premises_thread_local:
    (forall tid Pi (THREAD: Some Pi = IdentMap.find tid ProgI)
       Gi (THREAD_Gi: thread_restricted_execution GI tid Gi),
        omm_premises_hold Gi) -> omm_premises_hold GI.
  Proof.
    intros THREADS_OMM. red in ExecI. destruct ExecI as [E_STRUCT RESTRS].
    red. 
    assert (E GI ≡₁ set_bunion (fun thread => IdentMap.In thread ProgI \/ thread = tid_init) (fun thread => Tid_ thread ∩₁ E GI)).
    { split; [| basic_solver].
      rewrite set_bunion_inter_compat_r. 
      apply set_subset_inter_r. split; [| basic_solver].
      red. ins. red. specialize (E_STRUCT _ H).
      des.
      { unfold is_init in E_STRUCT. simpl in E_STRUCT. destruct x; vauto.
        eexists; vauto. }
      destruct x.
      { simpl in E_STRUCT. apply programs_without_tid_init in E_STRUCT. vauto. }
      simpl in *. 
      assert (exists Pi, Some Pi = IdentMap.find thread ProgI) as [Pi THREAD]. 
      { apply find_iff_in. auto. }
      eexists. splits; vauto. }
    assert (forall r thread (SAME_TID: r ⊆ same_tid), r ⨾ ⦗Tid_ thread⦘ ≡ ⦗Tid_ thread⦘ ⨾ r ⨾ ⦗Tid_ thread⦘) as TID_INFER.
    { ins. split; [|basic_solver].
      red in SAME_TID. red. ins.
      apply seq_eqv_r in H0. desc.
      apply seq_eqv_lr. splits; auto. rewrite <- H1. apply SAME_TID. auto. }
    assert (forall {A: Type} S S' (r: relation A), S ∩₁ S' ∩₁ codom_rel r ≡₁ S ∩₁ S' ∩₁ codom_rel (r ⨾ ⦗S⦘)) as CODOM_MOVE_HELPER. 
    { ins. basic_solver 100. }
    assert (forall {A: Type} (S1 S2 S3 S4: A -> Prop), S1 ≡₁ S3 -> S2 ≡₁ S4 -> S1 ≡₁ S2 -> S3 ≡₁ S4) as same_relation_goal. 
    { ins. rewrite <- H0, <- H1. auto. }
    assert (forall {A: Type} (S1 S2 S3 S4: A -> Prop), S1 ≡₁ S3 -> S2 ≡₁ S4 -> S1 ⊆₁ S2 -> S3 ⊆₁ S4) as inclusion_goal. 
    { ins. rewrite <- H0, <- H1. auto. }
    assert (forall {A: Type} (S1 S2 S3: A -> Prop), S1 ∩₁ S2 ≡₁ S3 -> S1 ∩₁ S2 ≡₁ S1 ∩₁ S3) as INTER_HELPER. 
    { ins. rewrite <- set_interK with (s := S1). rewrite !set_interA, H0. basic_solver. }
    assert (forall {A: Type} (D: A -> Prop) r, immediate (restr_rel D r) ≡ restr_rel D (immediate (restr_rel D r))) as REFACTOR_RESTR_IMM. 
    { ins. basic_solver. }
    assert (forall G, immediate (sb G) ≡ ⦗E G⦘ ⨾ immediate (sb G)) as E_SB. 
    { ins. unfold sb. basic_solver. }
    assert (forall G, immediate (sb G) ≡  immediate (sb G) ⨾ ⦗E G⦘) as SB_E. 
    { ins. unfold sb. basic_solver. }
      
    splits.
    { rewrite (seq_eqv_lr_r (wf_rmwE WFI)). repeat rewrite <- seqA with (r3 := ⦗E GI⦘).
      rewrite codom_eqv1.
      rewrite set_interC with (s' := E GI).
      rewrite H. repeat rewrite <- set_bunion_inter_compat_r.
      apply set_equiv_bunion; auto.
      intros thread THREAD. des.
      { assert (exists PI, Some PI = IdentMap.find thread ProgI) as [PI THREADI].
        { apply find_iff_in. auto. }
        specialize (RESTRS _ _ THREADI). destruct RESTRS as [GIi [TEi TREi]]. 
        specialize (THREADS_OMM _ _ THREADI _ TREi). 
        destruct TREi.
        rewrite CODOM_MOVE_HELPER.
        rewrite set_interC with (s := Tid_ thread). rewrite <- tr_acts_set.
        rewrite set_interA. apply INTER_HELPER. rewrite <- set_interA.
        red in THREADS_OMM. desc. generalize WSCFACQRMW. apply same_relation_goal.
        { rewrite !set_interA. apply inter_subset_helper. ins.
          unfold set_inter, is_w, is_sc, Events.mod.
          rewrite tr_lab; vauto. }
        apply codom_rel_more. 
        rewrite !seqA. rewrite TID_INFER; [| apply (wf_rmwt WFI)].
        rewrite <- seq_eqvK with (dom := Tid_ thread) at 1. rewrite !seqA, <- tr_rmw.
        rewrite <- !seqA. apply seq_more; [| basic_solver].
        rewrite TID_INFER.
        2: { arewrite (immediate (sb GI) ⊆ sb GI).
             arewrite ((fun a => is_f_acq (lab GI) a) ⊆₁ (fun e => ~ is_init e)).
             { red. ins. eapply read_or_fence_is_not_init; eauto.
               unfold is_f_acq in H0. desc. basic_solver. }
             unfold sb. seq_rewrite <- id_inter.
             red. ins. apply seq_eqv_lr in H0. desc. red in H0. desc.
             unfold ext_sb in H1. destruct x; vauto. destruct y; desc; vauto. }
        rewrite (E_SB GI), (E_SB GIi). 
        rewrite <- !seqA. arewrite ((⦗Tid_ thread⦘ ⨾ ⦗fun a : actid => is_f_acq (lab GI) a⦘) ⨾ ⦗E GI⦘ ≡ (⦗Tid_ thread⦘ ⨾ ⦗fun a : actid => is_f_acq (lab GI) a⦘) ⨾ ⦗E GI⦘ ⨾ ⦗Tid_ thread⦘) by basic_solver.
        do 3 seq_rewrite <- id_inter.
        apply seq_more.
        { apply eqv_rel_more.
          rewrite set_interC with (s' := E GI), <- set_interA, <- tr_acts_set.
          rewrite set_interC. apply inter_subset_helper. ins.
          unfold is_f_acq, is_f, is_acq, Events.mod. rewrite tr_lab; auto. }
        apply immediate_sb_restr; vauto.
        red. ins. apply programs_without_tid_init. congruence. }
      subst. rewrite init_equiv.
      apply same_relation_goal with (S1 := ∅) (S2 := ∅); [| | basic_solver]. 
      { split; [basic_solver|].
        arewrite (is_init ∩₁ E GI ∩₁ W GI ∩₁ Sc GI ⊆₁ is_init ∩₁ Sc GI) by basic_solver.
        rewrite (init_pln WFI). unfold is_sc, is_only_pln. type_solver. }
      split; [basic_solver| ].
      arewrite ((fun a : actid => is_init a) ∩₁ E GI ⊆₁ (fun a : actid => is_init a)) by basic_solver.
      rewrite set_interC, <- codom_eqv1. rewrite !seqA.
      arewrite (rmw GI ⨾ ⦗fun a : actid => is_init a⦘ ⊆ ∅₂).
      2: { remove_emptiness. basic_solver. }
      rewrite (rmw_in_sb WFI). unfold sb. rewrite !seqA, <- id_inter.
      red. ins. apply seq_eqv_lr in H0. desc. red in H2. desc. destruct x; vauto; destruct y; vauto. }
    { assert (forall r (ST: r ⊆ same_tid), r ≡ bunion (fun _ => True) (fun t => restr_rel (Tid_ t) r)) as SAME_TID_SEPARATION. 
      { ins. split; try basic_solver. red in ST.
        red. ins. pose proof (ST _ _ H0) as SAME. red in SAME. 
        red. exists (tid x). split; auto. red. splits; auto. }
      rewrite SAME_TID_SEPARATION; [| apply (wf_rmwt WFI)].
      rewrite seq_bunion_l, seq_bunion_r.
      apply bunion_more_alt; [auto| ].
      intros thread.
      rewrite (wf_rmwE WFI), <- restr_relE, restr_restr.
      destruct (classic (thread = tid_init)) as [INIT | NINIT].
      { subst. rewrite set_interC, init_equiv.
        rewrite restr_relE. arewrite (⦗(fun a : actid => is_init a) ∩₁ E GI⦘
  ⨾ rmw GI ≡ ∅₂); [| basic_solver].
        split; [| basic_solver].
        rewrite (rmw_from_non_init WFI). basic_solver. }
      destruct (IdentMap.Properties.F.In_dec ProgI thread) as [THREAD | NTHREAD].
      2: { arewrite (E GI ∩₁ Tid_ thread ≡₁ ∅); [| basic_solver].
           split; [|basic_solver]. red. ins. red in H0. desc. subst.
           destruct (E_STRUCT _ H0); destruct x; vauto. }
      apply find_iff_in in THREAD. destruct THREAD as [PI THREADI].
      specialize_full RESTRS; eauto. destruct RESTRS as [GIi [TEi TREi]].      
      specialize_full THREADS_OMM; eauto. red in THREADS_OMM. desc.
      rewrite <- restr_relE, restr_restr.
      arewrite (E GI ∩₁ Tid_ thread ∩₁ Sc GI ≡₁ E GI ∩₁ Tid_ thread ∩₁ Sc GIi).
      { destruct TREi. rewrite <- tr_acts_set.
        apply inter_subset_helper. ins. unfold is_sc, Events.mod.
        rewrite tr_lab; vauto. }
      rewrite set_interC with (s' := Sc GIi). rewrite <- restr_restr with (d' := Sc GIi).
      rewrite set_interC. do 2 rewrite <- restr_restr. 
      apply restr_rel_more; [basic_solver| ].  
      rewrite restrC.
      destruct TREi. rewrite restr_relE, <- tr_rmw. rewrite restr_relE. auto. } 
    { rewrite SB_E. rewrite <- !seqA, codom_eqv1. rewrite set_interC with (s' := E GI). 
      rewrite H. repeat rewrite <- set_bunion_inter_compat_r.
      eapply set_subset_bunion.
      { edestruct set_equiv_refl2; eauto. }
      intros thread THREAD. des.
      { assert (exists PI, Some PI = IdentMap.find thread ProgI) as [PI THREADI].
        { apply find_iff_in. auto. }
        specialize (RESTRS _ _ THREADI). destruct RESTRS as [GIi [TEi TREi]]. 
        specialize (THREADS_OMM _ _ THREADI _ TREi). 
        destruct TREi.
        rewrite CODOM_MOVE_HELPER.
        rewrite set_interC with (s := Tid_ thread). rewrite <- tr_acts_set.
        rewrite <- set_interK with (s := E GIi) at 1. 
        rewrite set_interA. apply set_subset_inter; [basic_solver| ].  
        red in THREADS_OMM. desc. generalize WRLXF. apply inclusion_goal.
        { apply inter_subset_helper. ins.
          unfold is_orlx_w, is_w, is_only_rlx, Events.mod.
          rewrite tr_lab; vauto. }
        apply codom_rel_more. 
        rewrite TID_INFER.
        2: { arewrite (immediate (sb GI) ⊆ sb GI).
             arewrite ((fun a => is_f_acqrel (lab GI) a) ⊆₁ (fun e => ~ is_init e)).
             { red. ins. eapply read_or_fence_is_not_init; eauto.
               unfold is_f_acqrel in H0. desc. basic_solver. }
             unfold sb. seq_rewrite <- id_inter.
             red. ins. apply seq_eqv_lr in H0. desc. red in H0. desc.
             unfold ext_sb in H1. destruct x; vauto. destruct y; desc; vauto. }
        rewrite (E_SB GI), (E_SB GIi). 
        rewrite <- !seqA. arewrite ((⦗Tid_ thread⦘ ⨾ ⦗fun a : actid => is_f_acqrel (lab GI) a⦘) ⨾ ⦗E GI⦘ ≡ (⦗Tid_ thread⦘ ⨾ ⦗fun a : actid => is_f_acqrel (lab GI) a⦘) ⨾ ⦗E GI⦘ ⨾ ⦗Tid_ thread⦘) by basic_solver.
        do 3 seq_rewrite <- id_inter.
        apply seq_more.
        { apply eqv_rel_more.
          rewrite set_interC with (s' := E GI), <- set_interA, <- tr_acts_set.
          rewrite set_interC. apply inter_subset_helper. ins.
          unfold is_f_acqrel, is_f, is_acqrel, Events.mod. rewrite tr_lab; auto. }
        apply immediate_sb_restr; vauto.
        red. ins. apply programs_without_tid_init. congruence. }
      subst.
      arewrite (Tid_ tid_init ∩₁ E GI ∩₁ (fun a : actid => is_orlx_w (lab GI) a) ⊆₁ ∅); [| basic_solver]. 
      rewrite init_equiv. rewrite (init_pln WFI).
      rewrite set_interC, <- set_interA.
      unfold is_orlx_w, is_w, is_only_pln, is_only_rlx. mode_solver. }
    { rewrite SB_E. rewrite <- !seqA, codom_eqv1. rewrite set_interC with (s' := E GI). 
      rewrite H. repeat rewrite <- set_bunion_inter_compat_r.
      eapply set_subset_bunion.
      { edestruct set_equiv_refl2; eauto. }
      intros thread THREAD. des.
      { assert (exists PI, Some PI = IdentMap.find thread ProgI) as [PI THREADI].
        { apply find_iff_in. auto. }
        specialize (RESTRS _ _ THREADI). destruct RESTRS as [GIi [TEi TREi]]. 
        specialize (THREADS_OMM _ _ THREADI _ TREi). 
        destruct TREi.
        rewrite CODOM_MOVE_HELPER.
        rewrite set_interC with (s := Tid_ thread). rewrite <- tr_acts_set.
        rewrite <- set_interK with (s := E GIi) at 1. 
        do 2 rewrite set_interA. apply set_subset_inter; [basic_solver| ].  
        red in THREADS_OMM. desc. generalize RSCF. apply inclusion_goal.
        { rewrite set_interA. apply inter_subset_helper. ins.
          unfold set_inter, is_r, is_sc, Events.mod.
          rewrite tr_lab; vauto. }
        apply codom_rel_more. 
        rewrite TID_INFER.
        2: { arewrite (immediate (sb GI) ⊆ sb GI).
             arewrite ((fun a => is_f_acq (lab GI) a) ⊆₁ (fun e => ~ is_init e)).
             { red. ins. eapply read_or_fence_is_not_init; eauto.
               unfold is_f_acq in H0. desc. basic_solver. }
             unfold sb. seq_rewrite <- id_inter.
             red. ins. apply seq_eqv_lr in H0. desc. red in H0. desc.
             unfold ext_sb in H1. destruct x; vauto. destruct y; desc; vauto. }
        rewrite (E_SB GI), (E_SB GIi). 
        rewrite <- !seqA. arewrite ((⦗Tid_ thread⦘ ⨾ ⦗fun a : actid => is_f_acq (lab GI) a⦘) ⨾ ⦗E GI⦘ ≡ (⦗Tid_ thread⦘ ⨾ ⦗fun a : actid => is_f_acq (lab GI) a⦘) ⨾ ⦗E GI⦘ ⨾ ⦗Tid_ thread⦘) by basic_solver.
        do 3 seq_rewrite <- id_inter.
        apply seq_more.
        { apply eqv_rel_more.
          rewrite set_interC with (s' := E GI), <- set_interA, <- tr_acts_set.
          rewrite set_interC. apply inter_subset_helper. ins.
          unfold is_f_acq, is_f, is_acq, Events.mod. rewrite tr_lab; auto. }
        apply immediate_sb_restr; vauto.
        red. ins. apply programs_without_tid_init. congruence. }
      subst.
      arewrite (Tid_ tid_init ∩₁ E GI ∩₁ R GI ∩₁ Sc GI ⊆₁ ∅); [| basic_solver].
      rewrite init_equiv. rewrite (init_pln WFI).
      unfold is_orlx_w, is_w, is_only_pln, is_only_rlx. mode_solver. }
  Qed. 
    
  Lemma GI_omm_premises : omm_premises_hold GI.
  Proof.
    apply omm_premises_thread_local.
    ins.
    apply program_execution_equiv in ExecI. red in ExecI.
    (* bug? desf hangs here *)
    destruct ExecI as [EVENTS THREAD_EXEC]. clear ExecI.
    red in Compiled. destruct Compiled as [SAME_KEYS THREADS_COMP]. 
    assert (exists POi, is_thread_compiled POi Pi) as [POi POi_COMP].
    { assert (exists POi, Some POi = IdentMap.find tid ProgO) as [POi POi_THREAD]. 
      { apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. }
      exists POi. eapply THREADS_COMP; eauto. } 
    eapply GI_1thread_omm_premises; eauto.
  Qed. 
    
  (* currently rlx fences are used as default value for label function *)
  (* it forces us to (temporarily?) assert that there are no actual rlx fence nodes in a graph *)
  Lemma only_nontrivial_fences_workaround:
    F GI ≡₁ (fun a => is_true (is_f GI.(lab) a)). 
  Proof. Admitted.

  (* Definition option_default {A: Type} (opt: option A) (default: A) := *)
  (*   match opt with *)
  (*   | Some a => a *)
  (*   | None => default *)
  (*   end.  *)

  (* Lemma locations_separated_compiled ProgO ProgI (COMP: is_compiled ProgO ProgI) *)
  (*       (LOC_SEP: locations_separated ProgO): locations_separated ProgI. *)

  Lemma comp_corr_result oinstr block0 block BPI_corr
        (COMP: is_instruction_compiled oinstr block0)
        (CORR: block_corrected BPI_corr block0 block):
    block0 = block \/ exists cond adr, block = [Instr.ifgoto cond adr].
  Proof.
    inversion COMP; subst.
    6: { right.
         red in CORR. inversion CORR. subst. inversion H3. subst.
         inversion H1; subst igt; eauto. }
    all: left.
    1, 5:  by (red in CORR; inversion CORR; subst; inversion H3; subst;
      inversion H1; vauto).
    all: by (red in CORR; inversion CORR; subst;
             inversion H3; inversion H5; subst;
             inversion H1; inversion H2; subst; vauto). 
  Qed. 

  Lemma ORIG_INSTR instri (AT_LOC: instr_locs instri <> [])
        PO PI (COMP: is_thread_compiled PO PI) (IN_PI: In instri PI):
    exists instro, In instro PO /\ instr_locs instri = instr_locs instro /\
              instr_mode instri = instr_mode instro.
  Proof.
    red in COMP. desc. red in COMP. desc. (* red in COMP. desc. *)
    subst.
    apply itbc_implies_itbcw in COMP. 
    remember (length (flatten BPI)) as comp_length.
    generalize dependent PO. generalize dependent BPI. generalize dependent comp_length. 
    set (P := fun (comp_length : nat) => forall (BPI : list (list Instr.t)),
                  In instri (flatten BPI) ->
                  comp_length = length (flatten BPI) ->
                  forall PO : list Instr.t,
                    itbc_weak PO BPI ->
                    exists instro : Instr.t,
                      In instro PO /\
                      instr_locs instri = instr_locs instro /\
                      instr_mode instri = instr_mode instro).
    apply (strong_induction P). intros comp_length IH.
    red. ins. 
    destruct BPI as [| block BPI']; [vauto| ].
    red in H1. destruct H1 as [BPI0 [BPI_corr [COMP0 CORR]]]. 
    assert (exists block0 BPI0', BPI0 = block0 :: BPI0').
    { destruct BPI0; vauto. apply Forall2_length in CORR. vauto. }
    desc. subst.
    assert (exists oinstr PO', PO = oinstr :: PO').
    { destruct PO; vauto. apply Forall2_length in COMP0. vauto. }
    desc. subst.
    simpl in H. apply in_app_or in H. des.
    { inversion_clear COMP0. inversion_clear CORR.
      forward eapply comp_corr_result as CC_RESULT; eauto.
      des.
      { subst.
        inversion H0; subst. 
        - red in H. des; [| done]. subst. exists ld. splits; vauto.
        - red in H. des; [| by vauto | done]; subst.
          exists st. splits; vauto.
        - red in H. des; [| by vauto | done]; subst.
          exists ld. splits; vauto.
        - red in H. des; [| by vauto | done]; subst.
          exists exc. splits; vauto.
        - red in H. des; [| done]. subst. exists asn. splits; vauto.
        - red in H. des; [| done]. subst. exists igt. splits; vauto. }      
      subst. red in H. des; [| done]. subst.
      simpl in AT_LOC. vauto. }
    specialize (IH (length (flatten BPI'))). specialize_full IH. 
    { simpl. rewrite app_length. cut (length block > 0); [ins; omega| ].
      forward eapply (@COMPILED_NONEMPTY_weak (oinstr :: PO') (block :: BPI')) as COMP_NONEMPTY. 
      { red. eexists. eexists. splits; eauto. }
      inversion COMP_NONEMPTY. destruct block; vauto. simpl. omega. }
    red in IH. specialize (IH BPI' H eq_refl PO').
    specialize_full IH.
    { red. exists BPI0'. exists BPI_corr.
      inversion CORR. inversion COMP0. subst.
      splits; vauto. }
    desc. exists instro. splits; vauto.
  Qed. 
    
  Lemma locations_separated_compiled: locations_separated ProgI.
  Proof.
    red in OCamlProgO. destruct OCamlProgO as [OINSTRS LOC_SEP_O].  (* TODO: <<>> into OCamlProg *)
    unfold locations_separated. unfold locations_separated in LOC_SEP_O. 
    ins. specialize (LOC_SEP_O loc).
    desc. eexists. splits; eauto.
    intros tid PI THREADI instr INSTR_PI LOC_INSTR.
    red in Compiled. destruct Compiled as [SAME_KEYS COMP]. 
    assert (exists PO, Some PO = IdentMap.find tid ProgO) as [PO THREADO].
    { apply find_iff_in, SAME_KEYS, find_iff_in. eauto. }
    specialize (LOC_SEP_O0 _ _ (eq_sym THREADO)).
    forward eapply ORIG_INSTR as ORIG_INSTR; eauto.
    { red. ins. rewrite H in LOC_INSTR. vauto. }
    clear Compiled. 
    desc. rewrite ORIG_INSTR1. eapply LOC_SEP_O0; eauto. congruence. 
  Qed. 

  Lemma E_restr_iff G Gi tid e (TRE: thread_restricted_execution G tid Gi)
    (TID: Events.tid e = tid):
    E G e <-> E Gi e.
  Proof.
    destruct TRE.
    rewrite (proj1 (@set_equiv_exp_iff _ _ _) tr_acts_set).
    unfold set_inter. subst. intuition. 
  Qed. 
    
  Definition event_instr_prop st thread Pi :=
    forall ind (Est: E (G st) (ThreadEvent thread ind)) l (LOC: Some l = loc (lab (G st)) (ThreadEvent thread ind)),
    exists instr,
      In instr Pi /\
      In l (instr_locs instr) /\
      (Some (Events.mod (lab (G st)) (ThreadEvent thread ind)) = instr_mode instr).

  Lemma ordr_ordw_eq instr cas reg lexpr ordr ordw xmod (INSTR: instr = Instr.update cas xmod ordr ordw reg lexpr) Pi (COMP: exists PO, is_thread_compiled PO Pi) (IN: In instr Pi):
    ordr = ordw.
  Proof.
    desc. red in COMP. desc. red in COMP. desc. subst Pi.
    apply in_flatten_iff in IN. destruct IN as [block [BLOCK_IN INSTR_BLOCK]].
    red in COMP. desc.
    apply In_nth_error in BLOCK_IN. desc.
    symmetry in BLOCK_IN.
    assert (exists block0, Some block0 = nth_error BPI0 n) as [block0 BLOCK0_IN]. 
    { apply OPT_VAL, nth_error_Some.
      erewrite Forall2_length; eauto. 
      apply nth_error_Some, OPT_VAL. eauto. }
    assert (exists oinstr, Some oinstr = nth_error PO n) as [oinstr OINSTR_IN]. 
    { apply OPT_VAL, nth_error_Some.
      erewrite Forall2_length; eauto. 
      apply nth_error_Some, OPT_VAL. eauto. }
    assert (is_instruction_compiled oinstr block0) as COMP_INSTR by (eapply Forall2_index; eauto). 
    assert (block_corrected BPI0 block0 block) as CORR_BLOCK by (eapply Forall2_index; eauto).
    forward eapply comp_corr_result as CC_RESULT; eauto. des. 
    { subst. inversion COMP_INSTR.
      all: try (subst; simpl in INSTR_BLOCK; des; vauto). 
      inversion COMP_INSTR. subst exc. vauto. }
    subst. simpl in INSTR_BLOCK; des; vauto. 
  Qed. 

  Lemma EIP_steps st thread n_steps (REACH: (step thread) ^^ n_steps (init (instrs st)) st) (COMP: exists PO, is_thread_compiled PO (instrs st)):
    event_instr_prop st thread (instrs st).
  Proof.
    generalize dependent st. induction n_steps.
    { ins. red in REACH. desc. rewrite <- REACH. simpl.
      red. ins. }
    ins. red. ins.
    red in REACH. destruct REACH as [st_prev [REACH_PREV STEP]].
    assert (wf_thread_state thread st_prev) as WFTprev.
    { eapply wf_thread_state_steps with (s := init (instrs st)); [apply wf_thread_state_init| ]; eauto.
      apply crt_num_steps. eauto. }
    assert (wf_thread_state thread st) as WFT.
    { eapply wf_thread_state_step; eauto. }
    assert (instrs st_prev = instrs st) as INSTRS_SAME.
    { apply steps_same_instrs. eexists. apply rt_step. eauto. }
    rewrite <- INSTRS_SAME in REACH_PREV. 
    assert (ind < eindex st) as LT.
    { destruct WFT. specialize (acts_rep _ Est). desc.
      inversion REP. subst. vauto. }
    destruct COMP as [PO COMP]. 
    destruct (Nat.lt_ge_cases ind (eindex st_prev)) as [LTprev | GEprev]. 
    { assert (E (G st_prev) (ThreadEvent thread ind)) as Eprev.
      { destruct WFTprev. apply acts_clos. auto. }
      specialize_full IHn_steps; eauto. 
      { exists PO. congruence. }
      red in IHn_steps. specialize_full IHn_steps; eauto.
      { unfold loc. erewrite <- step_preserves_lab; eauto. }
      desc. eexists. splits; eauto.
      { congruence. }
      unfold Events.mod. erewrite step_preserves_lab; eauto. }
    assert (forall S' (EXT: E (G st) ≡₁ E (G st_prev) ∪₁ S'), S' (ThreadEvent thread ind)) as EVENT_EXT.
    { ins. rewrite (set_equiv_exp EXT) in Est. red in Est. des; auto.
      destruct WFTprev. specialize (acts_rep _ Est). desc.
      inversion REP. omega. }
    (* TODO: refactor *)
    do 2 (red in STEP; desc). inversion ISTEP0.
    1,2: by omega. 
    { exists instr.
      forward eapply (@step_1_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      apply EVENT_EXT in E_EXT. inversion E_EXT. subst.
      splits.
      { apply nth_error_In with (n := pc st_prev). congruence. }
      { move LOC at bottom. move UG at bottom. 
        unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
        rewrite upds in LOC. inversion LOC. subst.
        destruct lexpr; vauto. simpl.
        destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
      simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
      rewrite upds. auto. }
    { exists instr.
      forward eapply (@step_1_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      apply EVENT_EXT in E_EXT. inversion E_EXT. subst.
      splits.
      { apply nth_error_In with (n := pc st_prev). congruence. }
      { move LOC at bottom. move UG at bottom. 
        unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
        rewrite upds in LOC. inversion LOC. subst.
        destruct lexpr; vauto. simpl.
        destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
      simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
      rewrite upds. auto. }
    { exists instr.
      forward eapply (@step_1_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      apply EVENT_EXT in E_EXT. inversion E_EXT. subst.
      rewrite UG in LOC. simpl in LOC.
      unfold loc in LOC. rewrite upds in LOC. vauto. }
    { exists instr.
      forward eapply (@step_1_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      apply EVENT_EXT in E_EXT. inversion E_EXT. subst.
      splits.
      { apply nth_error_In with (n := pc st_prev). congruence. }
      { move LOC at bottom. move UG at bottom. 
        unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
        rewrite upds in LOC. inversion LOC. subst.
        destruct lexpr; vauto. simpl.
        destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
      simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
      rewrite upds. auto. }
    { exists instr.
      forward eapply (@step_2_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      rewrite set_unionA in E_EXT. apply EVENT_EXT in E_EXT.
      red in E_EXT. destruct E_EXT as [E_EXT | E_EXT].
      { inversion E_EXT. subst.
        splits.
        { apply nth_error_In with (n := pc st_prev). congruence. }
        { move LOC at bottom. move UG at bottom. 
          unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
          rewrite updo in LOC; [| intros C; inversion C; omega].
          rewrite upds in LOC. inversion LOC. subst.
          destruct lexpr; vauto. simpl.
          destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
        simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
        rewrite updo; [| intros C; inversion C; omega].
        rewrite upds. auto. }
      { forward eapply (ordr_ordw_eq II) as ORD_EQ; eauto. 
        { apply nth_error_In with (n := pc st_prev). congruence. }        
        inversion E_EXT. subst.
        splits.
        { apply nth_error_In with (n := pc st_prev). congruence. }
        { move LOC at bottom. move UG at bottom. 
          unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
          rewrite upds in LOC. inversion LOC. subst.
          destruct lexpr; vauto. simpl.
          destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
        simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
        rewrite upds. auto. } }      
{ exists instr.
      forward eapply (@step_2_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      rewrite set_unionA in E_EXT. apply EVENT_EXT in E_EXT.
      red in E_EXT. destruct E_EXT as [E_EXT | E_EXT].
      { inversion E_EXT. subst.
        splits.
        { apply nth_error_In with (n := pc st_prev). congruence. }
        { move LOC at bottom. move UG at bottom. 
          unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
          rewrite updo in LOC; [| intros C; inversion C; omega].
          rewrite upds in LOC. inversion LOC. subst.
          destruct lexpr; vauto. simpl.
          destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
        simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
        rewrite updo; [| intros C; inversion C; omega].
        rewrite upds. auto. }
      { forward eapply (ordr_ordw_eq II) as ORD_EQ; eauto. 
        { apply nth_error_In with (n := pc st_prev). congruence. }        
        inversion E_EXT. subst.
        splits.
        { apply nth_error_In with (n := pc st_prev). congruence. }
        { move LOC at bottom. move UG at bottom. 
          unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
          rewrite upds in LOC. inversion LOC. subst.
          destruct lexpr; vauto. simpl.
          destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
        simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
        rewrite upds. auto. } }
{ exists instr.
      forward eapply (@step_2_label_ext_helper st_prev st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      simpl in LBL_EXT. desc. 
      rewrite set_unionA in E_EXT. apply EVENT_EXT in E_EXT.
      red in E_EXT. destruct E_EXT as [E_EXT | E_EXT].
      { inversion E_EXT. subst.
        splits.
        { apply nth_error_In with (n := pc st_prev). congruence. }
        { move LOC at bottom. move UG at bottom. 
          unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
          rewrite updo in LOC; [| intros C; inversion C; omega].
          rewrite upds in LOC. inversion LOC. subst.
          destruct loc_expr; vauto. simpl.
          destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
        simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
        rewrite updo; [| intros C; inversion C; omega].
        rewrite upds. auto. }
      { forward eapply (ordr_ordw_eq II) as ORD_EQ; eauto. 
        { apply nth_error_In with (n := pc st_prev). congruence. }        
        inversion E_EXT. subst.
        splits.
        { apply nth_error_In with (n := pc st_prev). congruence. }
        { move LOC at bottom. move UG at bottom. 
          unfold loc in LOC. rewrite UG in LOC. simpl in LOC.
          rewrite upds in LOC. inversion LOC. subst.
          destruct loc_expr; vauto. simpl.
          destruct (Const.eq_dec (RegFile.eval_value (regf st_prev) r) Const.zero); vauto. }
        simpl. f_equal. unfold Events.mod. rewrite UG. unfold add. simpl.
        rewrite upds. auto. } } 
  Qed. 

            
  Lemma instr_of_event:
    forall e (Ee: E GI e) (NINITe: ~ is_init e) l (LOC: Some l = loc (lab GI) e),
    exists instr tid Pi,
      Some Pi = IdentMap.find tid ProgI /\
      In instr Pi /\ In l (instr_locs instr)
      /\ Some (Events.mod GI.(lab) e) = instr_mode instr. 
  Proof.
    ins.
    red in ExecI. destruct ExecI as [E_STRUCT EXEC]. 
    specialize (E_STRUCT _ Ee). des; vauto.
    destruct e; vauto.
    simpl in E_STRUCT. apply find_iff_in in E_STRUCT. destruct E_STRUCT as [Pi THREAD].
    specialize_full EXEC; eauto. destruct EXEC as [Gi [TEi TREi]].
    red in TEi. desc. subst.
    cut (event_instr_prop s thread Pi).
    { intros EIP. unfold event_instr_prop in EIP.
      assert (E (ProgToExecution.G s) (ThreadEvent thread index)).
      { forward eapply (E_restr_iff (ThreadEvent thread index) TREi); vauto.
        intuition. }
      forward eapply (EIP index); eauto. 
      { destruct TREi.
        unfold loc. rewrite tr_lab; auto.
        fold (loc (lab GI) (ThreadEvent thread index)). vauto. }
      ins. desc. repeat eexists; eauto.
      unfold Events.mod. erewrite <- tr_lab; eauto. }
    assert (Pi = instrs s) as INSTR_EQ.
    { replace Pi with (instrs (init Pi)) by auto.
      apply steps_same_instrs. eauto. }
    rewrite INSTR_EQ. apply crt_num_steps in STEPS. desc.
    eapply EIP_steps; vauto.
    red in Compiled. destruct Compiled as [SAME_KEYS COMP].
    assert (exists PO, Some PO = IdentMap.find thread ProgO) as [PO THREAD_O].
    { apply find_iff_in, SAME_KEYS, find_iff_in. eauto. } 
    red in COMP. specialize_full COMP; eauto. 
  Qed. 

  Lemma GI_locations_separated: 
    let Loc_ := fun l e => loc (lab GI) e = Some l in
    forall l : location,
      E GI ∩₁ Loc_ l \₁ (fun a : actid => is_init a) ⊆₁ ORlx GI \/
      E GI ∩₁ Loc_ l \₁ (fun a : actid => is_init a) ⊆₁ Sc GI.
  Proof.
    pose proof instr_of_event as LOC_MAP.
    simpl. ins.
    destruct (classic (E GI ∩₁ (fun e : actid => loc (lab GI) e = Some l) \₁
                         (fun a : actid => is_init a) ⊆₁ ORlx GI \/
                       E GI ∩₁ (fun e : actid => loc (lab GI) e = Some l) \₁
                         (fun a : actid => is_init a) ⊆₁ Sc GI)) as [|DECIDE]; auto. 
    exfalso. apply not_or_and in DECIDE. desc.
    assert (forall (r1 r2: actid -> Prop), ~ r1 ⊆₁ r2 -> exists e, r1 e /\ ~ r2 e) as NON_SUBSET. 
    { ins. unfold set_subset in H.
      apply not_all_ex_not in H. desc. exists n. apply imply_to_and. auto. }
    apply NON_SUBSET in DECIDE. apply NON_SUBSET in DECIDE0. clear NON_SUBSET. 
    destruct DECIDE as [e e_props]. destruct DECIDE0 as [e0 e0_props].
    destruct e_props as [[[Ee Le] NINITe] NRLXe]. 
    destruct e0_props as [[[Ee0 Le0] NINITe0] NSC0].
    symmetry in Le, Le0.
    pose proof (LOC_MAP e Ee NINITe l Le) as [instr [tid [PI [THREAD_PI [INSTR_PI INSTR_L]]]]].
    pose proof (LOC_MAP e0 Ee0 NINITe0 l Le0) as [instr0 [tid0 [PI0 [THREAD_PI0 [INSTR0_PI0 INSTR0_L]]]]].
    desc.
    pose proof (locations_separated_compiled) as IMM_LOC_SEP. red in IMM_LOC_SEP. specialize (IMM_LOC_SEP l). 
    destruct IMM_LOC_SEP as [m [OMMm PROPSm]].
    pose proof (PROPSm tid PI (eq_sym THREAD_PI) instr INSTR_PI INSTR_L) as INSTR_m. 
    pose proof (PROPSm tid0 PI0 (eq_sym THREAD_PI0) instr0 INSTR0_PI0 INSTR0_L) as INSTR0_m.
    unfold is_only_rlx in NRLXe. unfold is_sc in NSC0.
    replace (Events.mod (lab GI) e) with m in *; [| congruence]. 
    replace (Events.mod (lab GI) e0) with m in *; [| congruence].
    type_solver. 
  Qed. 

  (* Lemma ORLX_W_ALT G: *)
  (*   .  *)
  (* Proof. unfold set_inter, is_orlx_w. basic_solver. Qed. *)
  
  (* Lemma F_ACQREL_ALT G: *)
  (*   W G ∩₁ ORlx G ≡₁ fun x : actid => is_orlx_w (lab G) x.  *)
  (* Proof. unfold set_inter, is_orlx_w. basic_solver. Qed. *)
  
  Lemma imm_implies_omm:
    ocaml_consistent GI.
  Proof.
    pose proof GI_omm_premises as GI_OMM_PREM. red in GI_OMM_PREM. desc.
    pose proof GI_locations_separated. 
    eapply (@OCamlToimm_s.imm_to_ocaml_consistent GI); eauto.
    { rewrite set_interA.
      arewrite (W GI ∩₁ ORlx GI ≡₁ fun x : actid => is_orlx_w (lab GI) x). 
      { unfold set_inter, is_orlx_w. basic_solver. }
      arewrite ((fun a : actid => is_f (lab GI) a) ∩₁ Acqrel GI ≡₁ fun a : actid => is_f_acqrel (lab GI) a).
      { unfold set_inter, is_f_acqrel. basic_solver. }
      auto. }
    1, 2: arewrite ((fun a : actid => is_f (lab GI) a) ∩₁ Acq GI ≡₁ fun a : actid => is_f_acq (lab GI) a) by unfold set_inter, is_f_acq; basic_solver.
  Qed.

  Lemma IdentMap_explicit {A B: Type} (P: IdentMap.key -> A -> Prop) (orig: IdentMap.t B):
    (exists (imap: IdentMap.t A),
        same_keys imap orig
        /\ forall key value (KEY: Some value = IdentMap.find key imap), P key value)
    <-> forall key (KEY: IdentMap.In key orig), exists value, P key value. 
  Proof. Admitted. 
    
  (* Lemma build_GOi_map TSGI (WFG: Wf (tsg2g TSGI)) (TSG_EXECI : program_execution_tsg ProgI TSGI): *)
  (*   exists GOis, same_keys GOis (Gis TSGI) /\ *)
  (*           forall tid GOi (THREAD_GRAPH: Some GOi = IdentMap.find tid GOis) *)
  (*             GIi (THREAD: Some GIi = IdentMap.find tid (Gis TSGI)) *)
  (*             Po (THREAD_O: Some Po = IdentMap.find tid ProgO), *)
  (*             same_behavior_local GOi GIi /\ *)
  (*             Othread_execution tid Po GOi.  *)
  (* Proof. *)
  (*   set (P := fun tid GOi => *)
  (*               forall GIi (THREAD: Some GIi = IdentMap.find tid (Gis TSGI)) *)
  (*                 Po (THREAD_O: Some Po = IdentMap.find tid ProgO), *)
  (*                 same_behavior_local GOi GIi /\ *)
  (*                 Othread_execution tid Po GOi).  *)
  (*   apply (@IdentMap_explicit execution execution P (Gis TSGI)). *)
  (*   intros tid THREAD. *)
  (*   red in TSG_EXECI. desc. *)
  (*   red in Compiled. destruct Compiled as [SAME_THREADS THREADS_COMPILED]. clear Compiled. *)
  (*   assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI].  *)
  (*   { apply find_iff_in. apply SAME_KEYS. auto. } *)
  (*   assert (exists Po, Some Po = IdentMap.find tid ProgO) as [Po THREAD_PROGO].  *)
  (*   { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. } *)
  (*   apply find_iff_in in THREAD. destruct THREAD as [Gi THREAD_EXEC].  *)
  (*   specialize (THREAD_GRAPH_EXEC tid Pi THREAD_PROGI Gi THREAD_EXEC).  *)
  (*   forward eapply thread_execs; eauto. *)
  (*   (* { pose proof (proj1 (Wf_tsg (tsg2g TSGI))). apply H in WFG. desc. *) *)
  (*   (*   eapply WFG. rewrite (proj2 tsg_g_bijection). eauto. } *) *)
  (*   ins. unfold P. destruct H as [GOi GOi_PROPS]. *)
  (*   exists GOi. ins. *)
  (*   (* TODO: correct this duplication? *) *)
  (*   replace GIi with Gi; [| congruence]. replace Po0 with Po; [| congruence]. *)
  (*   desc. split; auto.  *)
  (* Qed.  *)

  (* Lemma TSGO_exists TSGI (WFG: Wf (tsg2g TSGI)) (TSG_EXECI : program_execution_tsg ProgI TSGI): *)
  (*   exists TSGO, *)
  (*   Oprogram_execution_tsg TSGO OCamlProgO /\ *)
  (*   co_tsg TSGO ≡ co_tsg TSGI /\ *)
  (*   rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘ /\ *)
  (*   (forall tid : IdentMap.key, *)
  (*       IdentMap.In tid (Gis TSGO) -> *)
  (*       forall GOi GIi : execution, *)
  (*         Some GOi = IdentMap.find tid (Gis TSGO) -> *)
  (*         Some GIi = IdentMap.find tid (Gis TSGI) -> same_behavior_local GOi GIi).  *)
  (* Proof. *)
  (*   pose proof (build_GOi_map WFG TSG_EXECI) as [GOis [SAME_TIDS GOis_PROPS]].  *)
  (*   set (TSGO := {| Gis := GOis; *)
  (*                   Einit_tsg := Einit_tsg TSGI; *)
  (*                   rf_tsg := rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘; *)
  (*                   co_tsg := co_tsg TSGI; *)
  (*                   rmw_tsg := ∅₂; |} ). *)
  (*   exists TSGO. *)
  (*   destruct Compiled as [SAME_THREADS THREADS_COMPILED]. clear Compiled. *)
  (*   splits; [| basic_solver | subst TSGO; basic_solver |].  *)
  (*   { red. ins.  *)
  (*     specialize (SAME_THREADS tid). *)
  (*     assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI].  *)
  (*     { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. } *)
  (*     assert (exists GIi, Some GIi = IdentMap.find tid (Gis TSGI)) as [Gi THREAD_EXECI]. *)
  (*     { red in TSG_EXECI. desc. red in SAME_KEYS. specialize (SAME_KEYS tid). *)
  (*       apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. } *)
  (*     assert (exists GOi, Some GOi = IdentMap.find tid (Gis TSGO)) as [GOi THREAD_EXECO]. *)
  (*     { simpl. apply find_iff_in, SAME_TIDS, find_iff_in. eauto. } *)
  (*     forward eapply GOis_PROPS; eauto. *)
  (*     ins. desc. eauto. } *)
  (*   ins. *)
  (*   assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI].  *)
  (*   { red in TSG_EXECI. desc. red in SAME_KEYS. apply find_iff_in. *)
  (*     apply SAME_KEYS. apply find_iff_in. eauto. } *)
  (*   assert (exists Po, Some Po = IdentMap.find tid ProgO) as [Po THREAD_PROGO].  *)
  (*   { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. } *)
  (*   forward eapply GOis_PROPS; eauto. ins. desc. auto.  *)
  (* Qed.  *)
    
  Definition  thread_execs_fun tid PIi (THREADI: Some PIi = IdentMap.find tid ProgI):
    inhabited {GOi | forall POi (COMP: Some POi = IdentMap.find tid ProgO), Othread_execution tid POi GOi}.
    apply exists_to_inhabited_sig. 
    assert (exists Po, Some Po = IdentMap.find tid ProgO). 
    { (* apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. *) admit.  }
    desc.
  Admitted.

  Definition merge (GOis: list execution): execution.
  Admitted.

  (* Lemma sbl_restricted GO (OEXEC: Oprogram_execution_corrected OCamlProgO GO) *)
  (*       (* (BY_THREADS: forall tid GOi GIi *) *)
  (*       (*                (RESTRO: thread_restricted_execution GO tid GOi) *) *)
  (*       (*                (RESTRI: thread_restricted_execution GI tid GIi), *) *)
  (*           (* same_behavior_local GOi GIi): *):  *)
  (*   same_behavior_local GO GI. *)
  (* Proof. *)
  (*   red. splits. *)
  (*   { apply program_execution_equiv in ExecI. red in ExecI. *)
  (*     destruct ExecI as [INIT EXEC]. clear ExecI. *)
  (*     destruct OEXEC as [INIT' EXEC']. *)
  (* Definition enum_type := exists tid PO PI SGI, *)
  (*     is_thread_compiled PO PI /\ thread_execution tid PI SGI.  *)

  (* Definition build_result_type (ei: enum_type): Prop. *)
  (*   unfold enum_type in *.  *)
  
  Lemma set_finite_alt {A: Type} (S: A -> Prop) (FIN: set_finite S):
    exists findom, forall x, S x <-> In x findom.
  Proof.
    destruct FIN as [lst FIN].
    exists (filterP S lst). ins. split.
    { ins. apply in_filterP_iff. split; auto. }
    ins. apply in_filterP_iff in H. desc. auto. 
  Qed. 
  
  Lemma thread_execs_helper: exists GO,
      ⟪ E_STRUCT: forall e : actid, E GO e -> is_init e \/ IdentMap.In (tid e) ProgO ⟫/\
      ⟪ SAME_INIT: E GO ∩₁ is_init ≡₁ E GI ∩₁ is_init⟫ /\
      (* ⟪ SAME_INIT_LABELS: forall e (INIT: (E GO ∩₁ is_init) e), lab GO e = lab GI e⟫ /\ *)
      ⟪ SAME_INIT_LABELS: forall l, lab GO (InitEvent l) = Astore Xpln Opln l 0 ⟫ /\
      ⟪ SAME_CO: co GI ≡ co GO⟫ /\
      ⟪ EXT_RF: rf GO ≡ restr_rel (RWO GI) (rf GI)⟫ /\
      ⟪ RESTR_SIM: forall tid POi
        (THREAD: Some POi = IdentMap.find tid ProgO)
        GOi (RESTR: thread_restricted_execution GO tid GOi)
        GIi (RESTR: thread_restricted_execution GI tid GIi),
        Othread_execution tid POi GOi /\ same_behavior_local GOi GIi ⟫.
  Proof.
(*     red in ExecI. destruct ExecI. *)
(*     set (enum_type := exists tid PO PI SGI, *)
(*               is_thread_compiled PO PI /\ thread_execution tid PI SGI).  *)
(*     set (foo := set_bunion (fun enum_item: enum_type => True) (fun enum_item (_: actid) => True)). *)
    
(*     assert (forall (ei: enum_type), exists SGO: execution, True). *)
(*     { intros ei. destruct ei. proj_sig1 *)
(* ) *)
(*     thread_execs *)
(*     assert (set_finite (fun thread => IdentMap.In thread ProgI)) as FIN_THREADS by admit. *)
(*     assert (set_finite (fun GOi => exists tid POi *)
(*                                   (THREAD: Some POi = IdentMap.find tid ProgO) *)
(*                                   GIi (RESTR: thread_restricted_execution GI tid GIi), *)
(*                             Othread_execution tid POi GOi /\ same_behavior_local GOi GIi)). *)
    (*     { apply set_finite_more with (x := (fun thread : IdentMap.key => IdentMap.In thread ProgI)).  *)
    set (GOi_prop := fun thread GOi =>
                       exists POi GIi,
                         Some POi = IdentMap.find thread ProgO /\
                         thread_restricted_execution GI thread GIi /\
                         Othread_execution thread POi GOi /\ 
                         same_behavior_local GOi GIi). 
    set (all_acts := set_bunion
                       (fun thread => IdentMap.In thread ProgI)
                       (fun thread e => exists GOi, GOi_prop thread GOi /\ E GOi e)).
    assert (set_finite all_acts) as FIN_EGO. 
    { admit. }
    apply set_finite_alt in FIN_EGO. destruct FIN_EGO as [GO_actsset EGO].
    assert (set_finite (E GI ∩₁ is_init)) as FIN_INIT.
    { admit. }
    apply set_finite_alt in FIN_INIT. destruct FIN_INIT as [GO_initset INIT_GO].
    set (GOi_rel := fun (rel: execution -> relation actid) =>
                      bunion
                        (fun thread => IdentMap.In thread ProgI)
                        (fun thread x y => exists GOi, GOi_prop thread GOi /\ (rel GOi x y))). 
    
    set (GO :=   {| acts := GO_actsset ++ GO_initset;
                    lab := fun _ => Afence Opln;
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
      red in E_ACT. destruct E_ACT as [thread [THREAD [GOi [EGOi_prop EGOi]]]].
      red in EGOi_prop. desc.
      red in EGOi_prop2. desc. rewrite (set_equiv_exp RESTR_EVENTS) in EGOi.
      red in EGOi. desc. 
      destruct EGOi_prop0. rewrite (set_equiv_exp tr_acts_set) in EGOi.
      red in EGOi. desc.
      destruct e.
      { subst. simpl in THREAD. apply programs_without_tid_init in THREAD. vauto. }
      simpl in EGOi1. subst. do 3 eexists; eauto. split; eauto.
      vauto. }

    exists GO. splits.
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
    { admit. }
    ins.
    pose proof thread_execs.  
  Admitted.

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
      
  Lemma into_restr G e (Ee: E G e):
    is_init e \/
    (exists tid Gi ind,
        ⟪ TRE: thread_restricted_execution G tid Gi ⟫ /\
        ⟪ EGi: E Gi e ⟫ /\
        ⟪ SAME_TID: e = ThreadEvent tid ind ⟫).
  Proof.
    destruct e; auto. right.
    pose proof (restr_graph G thread). desc.
    exists thread. exists Gi. exists index. split; auto.
    destruct H. split; auto. 
    apply (set_equiv_exp tr_acts_set). red. split; auto.
  Qed.

  Lemma tid_restr G Gi e tid (Gie: E Gi e)
        (TRE: thread_restricted_execution G tid Gi): 
    Events.tid e = tid.
  Proof.
    destruct TRE. apply (set_equiv_exp tr_acts_set) in Gie.
    red in Gie. desc. auto.
  Qed. 

  Lemma GO_exists: exists GO,
      Oprogram_execution_corrected OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    pose proof thread_execs_helper as T_E_H. 
    desc.
    exists GO. split.
    { red. split; auto. 
      ins. specialize (RESTR_SIM _ _ THREAD Gi THREAD_EXEC).
      pose proof (restr_graph GI thread) as [GIi RESTRI]. 
      desc. specialize (RESTR_SIM GIi RESTRI). desc. auto. }
    red. splits; auto.
    { red. splits. 
      2: { ins. pose proof EGOx as EGOx_. apply into_restr in EGOx.
           destruct EGOx.
           { destruct x; vauto. destruct WFI. congruence. }
         desc. subst. rename Gi into GOi. 
         replace (lab GO (ThreadEvent tid ind)) with (lab GOi (ThreadEvent tid ind)).
         2: { destruct TRE. intuition. }
         specialize (E_STRUCT (ThreadEvent tid ind) EGOx_).
         destruct E_STRUCT; vauto. 
         simpl in H.
         apply find_iff_in in H. destruct H as [POi THREADO]. 
         specialize (RESTR_SIM tid POi THREADO _ TRE).
         pose proof (restr_graph GI tid). desc.
         specialize (RESTR_SIM Gi H). desc.
         replace (lab GI (ThreadEvent tid ind)) with (lab Gi (ThreadEvent tid ind)).
         2: { destruct H. apply tr_lab.
              destruct RESTR_SIM0. red in H.
              apply (set_equiv_exp H) in EGi.
              red in EGi. desc. auto. }
         red in RESTR_SIM0. desc. apply SAME_LAB. auto. }
      assert (forall S, S ≡₁ S ∩₁ (fun a : actid => is_init a) ∪₁ S ∩₁ (fun a : actid => ~ is_init a)) as INIT_SPLIT.
      { ins. rewrite <- set_inter_union_r.
        arewrite ((fun a : actid => is_init a) ∪₁ (fun a : actid => ~ is_init a) ≡₁ fun e => True).
        { apply set_equiv_exp_iff. ins. destruct x; simpl; vauto. }
        basic_solver. }
      rewrite INIT_SPLIT. rewrite INIT_SPLIT with (S := E GI ∩₁ RWO GI).
      apply set_equiv_union.
      { rewrite set_interA.
        arewrite (RWO GI ∩₁ (fun a : actid => is_init a) ≡₁ fun a : actid => is_init a); auto.
        split; [basic_solver| ]. red. ins. red. split; auto.
        red. red. split.
        { red. right. apply init_w; auto. }
        red. ins. red in H0. desc.
        rewrite (same_relation_exp (rmw_from_non_init WFI)) in H0.
        apply seq_eqv_l in H0. desc. vauto. } 

    apply set_equiv_exp_iff. ins.
    red. split.
    { intros [EGOx NINITx]. red.
      pose proof (into_restr _ _ EGOx). 
      destruct H; vauto.       
      desc. rename Gi into GOi.
      specialize (E_STRUCT x EGOx). destruct E_STRUCT; vauto.
      simpl in H. apply find_iff_in in H. destruct H as [PO THREADO]. 
      assert (exists GIi, thread_restricted_execution GI tid GIi) by apply restr_graph. desc.  
      forward eapply RESTR_SIM as [OTHREADEXEC SAME_BEHL]; eauto.
      split; vauto. split.  
      { eapply E_restr_iff; eauto.
        red in SAME_BEHL. desc. 
        apply (set_equiv_exp RESTR_EVENTS) in EGi.
        red in EGi. desc. auto. }
      red in SAME_BEHL. desc.
      apply (set_equiv_exp RESTR_EVENTS) in EGi.
      desc. red in EGi. desc. red in EGi0. desc. auto.       
      red. red in EGi0. desc. split.
      { replace (RW GI (ThreadEvent tid ind)) with (RW GIi (ThreadEvent tid ind)); auto. 
        destruct H. unfold is_r, is_w, set_union. 
        rewrite tr_lab; auto. }
      cut (~ dom_rel (rmw GIi) (ThreadEvent tid ind)); vauto. 
      red. ins. red in H0. 
      forward eapply H0; auto.  
      unfold dom_rel. unfold dom_rel in H1. desc. exists y.
      destruct H. apply (same_relation_exp tr_rmw).
      apply seq_eqv_lr. splits; auto.
      apply (hahn_inclusion_exp (rmw_in_sb WFI)) in H1.
      apply sb_tid_init in H1. simpl in H1. destruct H1; vauto. }
    ins. red in H. desc. split; auto. 
    destruct x; vauto. 
    pose proof (restr_graph GO thread) as [GOi TRE]. 
    eapply E_restr_iff; eauto.     
    { assert (exists PIi, Some PIi = IdentMap.find thread ProgI).
      { apply find_iff_in.
        red in ExecI. destruct ExecI as [IMM_EVENTS _].
        specialize (IMM_EVENTS (ThreadEvent thread index)). specialize_full IMM_EVENTS.
        { red in H. desc. auto. }
        des; vauto. }
      assert (exists POi, Some POi = IdentMap.find thread ProgO) as [POi THREADO]. 
      { apply find_iff_in. red in Compiled. destruct Compiled.
        apply H2. apply find_iff_in. auto. }
      assert (exists GIi, thread_restricted_execution GI thread GIi) as [GIi TREI] by apply restr_graph.      
      forward eapply RESTR_SIM as [OEXEC SAME_BEHL]; eauto.
      destruct SAME_BEHL. apply (set_equiv_exp H2).
      pose proof TREI as TREI_. destruct TREI. 
      assert (E GIi (ThreadEvent thread index)) as EGIi. 
      { red in H. desc. 
        apply (@E_restr_iff _ _ _ _ TREI_); auto. }
      red. split; auto.       
      red. red in H0. desc. split. 
      { red in H. desc. do 2 red in H4. desc. 
        replace (RW GIi (ThreadEvent thread index)) with (RW GI (ThreadEvent thread index)); auto.
        unfold is_r, is_w, set_union. 
        rewrite tr_lab; auto. }
      red in H. desc. do 2 red in H4. desc. 
      red. ins. apply H5. 
      red in H6. desc. apply (same_relation_exp tr_rmw) in H6. apply seq_eqv_lr in H6. desc. subst. vauto. } }
    { rewrite SAME_CO. auto. }
    ins. destruct WFI. congruence. 
  Qed. 

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI)
        (ExecO: Oprogram_execution OCamlProgO GO):
    ocaml_consistent GO.
  Proof.
    (* pose proof (same_beh_implies_similar_rels SB). *)
    pose proof (same_beh_implies_similar_intrarels SB) as SIMILAR_INTRA. 
    pose proof (Wf_subgraph SB WFI) as WFO. 
    red in SB. desc. red in SAME_LOCAL. desc.
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { (* TODO: extract and remove duplicate *)
      unfold Execution.sb.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC.
      rewrite RESTR_EVENTS.
      basic_solver. }
    
    assert (HBO': hbo GO ⊆ hbo GI).
    { unfold OCaml.hb.
      apply clos_trans_mori.
      apply union_mori; [rewrite SB'; basic_solver | ].
      destruct WFO. rewrite wf_coE, wf_rfE at 1.
      repeat rewrite <- restr_relE.
      rewrite union_restr, restr_restr.
      arewrite (E GO ∩₁ Sc GO ≡₁ E GO ∩₁ Sc GI).
      { (* TODO: generalize with ..._SIM *)
        apply set_equiv_exp_iff.
        ins. split.
        { ins. red in H. desc. red. split; auto.
          unfold is_sc, Events.mod. rewrite <- (SAME_LAB); auto. }
        { ins. red in H. desc. red. split; auto.
          unfold is_sc, Events.mod. rewrite (SAME_LAB); auto. } }
      apply restr_rel_mori; [basic_solver| ].
      rewrite SAME_CO, RESTR_RF. basic_solver. }
    red. red in OMM_I.
    splits; auto.
    { red.
      rewrite R_SIM.
      2: { red. splits; eauto. }
      rewrite RESTR_EVENTS, RESTR_RF. fold (RWO GI). 
      desc. red in Comp.
      rewrite restr_relE, <- seqA.
      rewrite set_interC, <- set_interA. rewrite set_interC with (s := R GI).
      arewrite (E GI ∩₁ R GI ⊆₁ codom_rel (rf GI)).
      rewrite <- seqA. rewrite codom_eqv1.
      apply set_subset_inter; [| basic_solver].      
      red. ins. red in H. destruct H as [w RFwx]. red. exists w.
      apply seq_eqv_l. split; auto. red. red.
      cut (W GI w).
      { ins. split; [basic_solver| ].
        pose proof wf_rmwD WFI.
        red. ins. red in H1. desc.
        rewrite (@same_relation_exp) in H1; [| eapply H0].
        apply seq_eqv_lr in H1. desc. type_solver. }
      pose proof (wf_rfD WFI).
      pose proof (same_relation_exp_iff (rf GI) (⦗W GI⦘ ⨾ rf GI ⨾ ⦗R GI⦘)) as [IMPL _].
      specialize (IMPL H w x). destruct IMPL. specialize (H0 RFwx).
      apply seq_eqv_lr in H0. desc. auto. }
    { red. arewrite (rmw GO ≡ ∅₂); basic_solver. }
    { rewrite HBO', SAME_CO. desc.  auto. }
    { unfold fr. rewrite HBO', SAME_CO. 
      arewrite (rf GO ⊆ rf GI) by rewrite RESTR_RF; auto. 
      auto. desc. auto. }    
    assert (W_RMW: W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
    { rewrite set_minusE.
      apply set_subset_inter_r. split; [basic_solver| ].
      rewrite (WFI.(wf_rmwD)).
      rewrite dom_eqv1. rewrite set_compl_inter.
      unionR left. type_solver. }
    arewrite (rfe GO ⊆ rfe GI).
    { unfold rfe. rewrite SB', RESTR_RF.
      fold (RWO GI). rewrite <- restr_relE.
      rewrite <- restr_minus. basic_solver. }
    assert (FR' : fr GO ≡ restr_rel (RWO GI) (fr GI)).
    { unfold Execution.fr. rewrite RESTR_RF.
      repeat rewrite restr_relE. do 2 rewrite transp_seq.
      rewrite transp_eqv_rel. 
      rewrite SAME_CO.
      rewrite !seqA. do 2 (apply seq_more; [basic_solver| ]).
      rewrite (wf_coD WFI), !seqA.
      rewrite seq_eqvC.
      rewrite <- seqA. 
      arewrite (⦗RWO GI⦘ ⨾ ⦗W GI⦘ ≡ ⦗W GI⦘); [| basic_solver]. 
      rewrite <- id_inter. apply eqv_rel_more.
      split; [basic_solver| ].
      apply set_subset_inter_r. split; [| basic_solver].
      auto. }
    
    rewrite <- restr_relE.
    arewrite (restr_rel Sc GO (coe GO ∪ fre GO) ≡ restr_rel (E GO ∩₁ Sc GO) (coe GO ∪ fre GO)).
    { split; try basic_solver.
      red. ins. red in H. desc.
      assert (E GO x /\ E GO y).
      { red in H. des. 
        { red in H. red in H. desc.
          apply (same_relation_exp (wf_coE WFO)) in H.
          apply seq_eqv_lr in H. desc; auto. }
        red in H. red in H. desc.
        apply (same_relation_exp (wf_frE WFO)) in H.
        apply seq_eqv_lr in H. desc; auto. }
      desc. red. splits; red; splits; auto. }
    seq_rewrite SC_SIM .
    2: { red. splits; eauto. }
    arewrite (E GO ∩₁ Sc GI ⊆₁ Sc GI) by basic_solver. 
        
    arewrite (fre GO ⊆ fre GI).
    { unfold fre. rewrite SB', FR'. fold (RWO GI).
      apply inclusion_minus_l.
      rewrite fri_union_fre at 1.
      rewrite <- union_restr.
      apply union_mori.
      { rewrite <- restr_relE.
        apply restr_rel_mori; [basic_solver| ].
        arewrite (fri GI ⊆ sb GI). basic_solver. }
      apply inclusion_restr. }
    
    arewrite (coe GO ≡ coe GI).
    { unfold coe.      
      rewrite SB', SAME_CO. fold (RWO GI). 
      seq_rewrite <- restr_relE. 
      rewrite (WFI.(wf_coD)). rewrite <- restr_relE.      
      rewrite <- restr_minus_alt. rewrite <- restr_minus_alt. 
      rewrite restr_minus. rewrite restr_minus. 
      rewrite restr_restr.
      arewrite ((RW GI \₁ dom_rel (rmw GI)) ∩₁ W GI ≡₁ W GI); auto.       
      rewrite set_inter_minus_l.
      arewrite (RW GI ∩₁ W GI ≡₁ W GI) by basic_solver.
      split; [basic_solver | ].
      rewrite WFI.(wf_rmwD).
      rewrite dom_eqv1.
      red. ins. red. split; auto.
      red. ins. type_solver. }
    
    arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
    rewrite restr_relE. 
    desc. auto. 
  Qed. 
  
  Theorem compilation_correctness: exists (GO: execution),
      ⟪WFO: Wf GO ⟫ /\
      ⟪ExecO: Oprogram_execution OCamlProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.
    pose proof GO_exists as [GO [OMM_EXEC SAME_BEH]].
    exists GO.
    pose proof (Wf_subgraph SAME_BEH WFI) as WFO.
    apply Oprogram_execution_equiv in OMM_EXEC. 
    splits; auto.    
    apply graph_switch; auto.
    apply (imm_implies_omm). 
  Qed.  

End CompilationCorrectness.       