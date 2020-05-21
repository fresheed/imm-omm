(******************************************************************************)
(** * ocaml MM is weaker than IMM_S   *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Omega.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCaml.
Require Import OCamlToimm_s.
Require Import OCamlToimm_s_prog. 
Require Import OCamlToimm_s_prog_compilation. 
Require Import OCamlToimm_s_prog_pair_step. 
Require Import OCamlToimm_s_prog_bounded_properties. 
Require Import OCamlToimm_s_prog_build_graph. 
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

  Lemma same_beh_implies_similar_intrarels GO GI (SB: same_behavior GO GI):
    ⟪DATA_SIM: data GO ≡ restr_rel (RWO GI) (data GI) ⟫ /\
    ⟪CTRL_SIM: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI) ⟫ /\ 
    ⟪ADDR_SIM: addr GO ≡ restr_rel (RWO GI) (addr GI) ⟫ /\
    ⟪SB_SIM: sb GO ≡ restr_rel (RWO GI) (sb GI) ⟫.
    (* ⟪NO_RMW: rmw GO ≡ ∅₂ ⟫ /\ *)
    (* ⟪NO_RMWDEP: rmw_dep GO ≡ ∅₂ ⟫. *)
  Proof.
    cdes SB. cdes SAME_LOCAL. splits; auto. 
    unfold sb. rewrite RESTR_EVENTS. basic_solver. 
  Qed. 

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
    inversion WF. 
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
    assert (sb GO ≡ restr_rel (RWO GI) (sb GI)) as SB_SIM. 
    { unfold sb. rewrite RESTR_EVENTS. basic_solver. }

    assert (DATA_INCL: data GO ⊆ sb GO).
    { rewrite RESTR_DATA, SB_SIM. apply restr_rel_mori; basic_solver. }
    assert (ADDR_INCL: addr GO ⊆ sb GO).
    { rewrite RESTR_ADDR, SB_SIM. apply restr_rel_mori; basic_solver. }
    assert (CTRL_INCL: ctrl GO ⊆ sb GO).
    { rewrite RESTR_CTRL, SB_SIM. apply restr_rel_mori; basic_solver. }
    
    (* red in SAME_BEH'. desc.   *)
    split; vauto.
    all: try (seq_rewrite RESTR_RMW; basic_solver). 
    all: try (seq_rewrite RESTR_RMWDEP; basic_solver). 
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
      rewrite RESTR_DATA. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      apply restr_rel_more; auto. red. splits; auto. red. splits; auto. }
    { rewrite (@SUPSET_RESTR _ (addr GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite R_SIM, RW_SIM; eauto. 
      rewrite set_interC with (s' := RW GI). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗RW GI⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite RESTR_ADDR. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l. 
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
      rewrite RESTR_CTRL. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      rewrite seq_id_r. 
      apply restr_rel_more; auto.
      red. splits; auto. }
    { rewrite RESTR_CTRL, SB_SIM. rewrite RESTR_SEQ. apply restr_rel_mori; auto. }
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

  Hypothesis programs_without_tid_init: ~ (IdentMap.In tid_init ProgI).
  
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

  Lemma SAME_TID_SEPARATION r (ST: r ⊆ same_tid):
    r ≡ bunion (fun _ => True) (fun t => restr_rel (Tid_ t) r).  
  Proof.
    ins. split; try basic_solver. red in ST.
    red. ins. pose proof (ST _ _ H) as SAME. red in SAME. 
    red. exists (tid x). split; auto. red. splits; auto.
  Qed.

  Lemma sim_graphs_omm G1 G2 (SIM: graphs_sim_weak G1 G2)
        (RMW_E2: rmw G2 ≡ restr_rel (E G2) (rmw G2))
        (OMM1: omm_premises_hold G1):
    omm_premises_hold G2.
  Proof.
    cdes OMM1. cdes SIM.
    assert (forall {A: Type} (S1 S2 S1' S2': relation A)
              (EQ1: S1 ≡ S1') (EQ2: S2 ≡ S2') (EQ': S1' ≡ S2'),
               S1 ≡ S2) as EQV_HELPER.
    { ins. by rewrite EQ1, EQ2. }
    assert (forall {A: Type} (S1 S2 S1' S2': A -> Prop)
              (EQ1: S1 ≡₁ S1') (EQ2: S2 ≡₁ S2') (EQ': S1' ≡₁ S2'),
               S1 ≡₁ S2) as SET_EQV_HELPER.
    { ins. by rewrite EQ1, EQ2. }
    assert (forall {A: Type} (S1 S2 S1' S2': A -> Prop)
              (EQ1: S1 ≡₁ S1') (EQ2: S2 ≡₁ S2') (EQ': S1' ⊆₁ S2'),
               S1 ⊆₁ S2) as SET_INCL_HELPER.
    { ins. by rewrite EQ1, EQ2. }
    assert (sb G1 ≡ sb G2) as SB_EQ.
    { unfold sb. cdes SIM. rewrite SIM0. auto. }
    assert (forall S r G, ⦗S⦘ ⨾ immediate (sb G) ⨾ r ≡ ⦗E G ∩₁ S⦘ ⨾ immediate (sb G) ⨾ r) as IMM_E_HELPER.
    { ins. split; [| basic_solver].
      rewrite <- !seqA. apply seq_mori; [| basic_solver].
      rewrite set_interC, id_inter, seqA. apply seq_mori; [basic_solver| ].
      unfold sb. basic_solver 10. }
    Ltac by_same_lab SIM0 SIM1 :=
      rewrite <- SIM0; apply inter_subset_helper; ins;
      unfold is_orlx_w, is_only_rlx, is_w, is_r, is_sc, is_f_acqrel, is_f_acq, is_f, is_acqrel, is_acq, Events.mod, set_inter;
      by rewrite SIM1.
    red. splits.
    { eapply (SET_EQV_HELPER _ _ _ _ _ _ _ WSCFACQRMW).
      Unshelve.
      { rewrite !set_interA. by_same_lab SIM0 SIM1. }
      apply codom_rel_more.
      rewrite IMM_E_HELPER with (G := G1). rewrite IMM_E_HELPER.
      rewrite <- SB_EQ, <- SIM2.
      apply seq_more; [| basic_solver]. apply eqv_rel_more.
      by_same_lab SIM0 SIM1. }
    { eapply (EQV_HELPER _ _ _ _ _ _ _ RMWSC).
      Unshelve.
      { by symmetry. }
      rewrite SIM2. rewrite RMW_E2.
      rewrite <- !restr_relE.
      rewrite !restr_restr. apply restr_rel_more; [| basic_solver].
      by_same_lab SIM0 SIM1. }
    { eapply (SET_INCL_HELPER _ _ _ _ _ _ _ WRLXF).
      Unshelve. 
      { by_same_lab SIM0 SIM1. }
      apply codom_rel_more.
      rewrite <- (seq_id_r (immediate (sb G1))), <- (seq_id_r (immediate (sb G2))). 
      rewrite IMM_E_HELPER with (G := G1). rewrite IMM_E_HELPER.
      rewrite <- SB_EQ. 
      apply seq_more; [| basic_solver]. apply eqv_rel_more.
      by_same_lab SIM0 SIM1. }
    { eapply (SET_INCL_HELPER _ _ _ _ _ _ _ RSCF).
      Unshelve. 
      { rewrite !set_interA. by_same_lab SIM0 SIM1. }
      apply codom_rel_more.
      rewrite <- (seq_id_r (immediate (sb G1))), <- (seq_id_r (immediate (sb G2))). 
      rewrite IMM_E_HELPER with (G := G1). rewrite IMM_E_HELPER.
      rewrite <- SB_EQ. 
      apply seq_more; [| basic_solver]. apply eqv_rel_more.
      by_same_lab SIM0 SIM1. }
  Qed.
  
  Lemma omm_premises_thread_local:
    (forall tid Pi (THREAD: Some Pi = IdentMap.find tid ProgI),
        exists Gi, thread_restricted_execution GI tid Gi /\
              omm_premises_hold Gi)
    -> omm_premises_hold GI.
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
    assert (forall GIi thread PIi (TREi: thread_restricted_execution GI thread GIi)
              (THREADI: Some PIi = IdentMap.find thread ProgI),
               omm_premises_hold GIi) as OMM_GIi.
    { ins. specialize (THREADS_OMM _ _ THREADI). desc.
      pose proof (tre_sim_weak THREADS_OMM TREi).
      assert (rmw GIi ≡ restr_rel (E GIi) (rmw GIi)).
      { destruct TREi. rewrite tr_rmw.
        rewrite <- restr_relE. rewrite restr_restr.
        rewrite tr_acts_set. rewrite set_interC, set_interA, set_interK.
        rewrite <- restr_restr. apply restr_rel_more; [basic_solver| ].
        rewrite restr_relE. apply wf_rmwE; eauto. } 
        
      eapply sim_graphs_omm; eauto. } 

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
        specialize (OMM_GIi _ _ _ TREi THREADI). 
        destruct TREi.
        rewrite CODOM_MOVE_HELPER.
        rewrite set_interC with (s := Tid_ thread). rewrite <- tr_acts_set.
        rewrite set_interA. apply INTER_HELPER. rewrite <- set_interA.
        red in OMM_GIi. desc. generalize WSCFACQRMW. apply same_relation_goal.
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
    { rewrite SAME_TID_SEPARATION; [| apply (wf_rmwt WFI)].
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
      specialize_full THREADS_OMM; eauto.
      specialize (OMM_GIi _ _ _ TREi THREADI).
      red in OMM_GIi. desc.
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
        specialize (OMM_GIi _ _ _ TREi THREADI). 
        (* specialize (THREADS_OMM _ _ THREADI _ TREi).  *)
        destruct TREi.
        rewrite CODOM_MOVE_HELPER.
        rewrite set_interC with (s := Tid_ thread). rewrite <- tr_acts_set.
        rewrite <- set_interK with (s := E GIi) at 1. 
        rewrite set_interA. apply set_subset_inter; [basic_solver| ].  
        red in OMM_GIi. desc. generalize WRLXF. apply inclusion_goal.
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
        specialize (OMM_GIi _ _ _ TREi THREADI). 
        (* specialize (THREADS_OMM _ _ THREADI _ TREi).  *)
        destruct TREi.
        rewrite CODOM_MOVE_HELPER.
        rewrite set_interC with (s := Tid_ thread). rewrite <- tr_acts_set.
        rewrite <- set_interK with (s := E GIi) at 1. 
        do 2 rewrite set_interA. apply set_subset_inter; [basic_solver| ].  
        red in OMM_GIi. desc. generalize RSCF. apply inclusion_goal.
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
    (* bug? desf hangs here *)
    destruct ExecI as [EVENTS THREAD_EXEC]. clear ExecI.
    red in Compiled. destruct Compiled as [SAME_KEYS THREADS_COMP]. 
    assert (exists POi, is_thread_compiled POi Pi) as [POi POi_COMP].
    { assert (exists POi, Some POi = IdentMap.find tid ProgO) as [POi POi_THREAD]. 
      { apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. }
      exists POi. eapply THREADS_COMP; eauto. }
    forward eapply THREAD_EXEC; eauto. 
    ins. desc. exists pe. split; auto. 
    eapply GI_1thread_omm_premises; eauto.
  Qed. 
    
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

  Lemma ordr_ordw_eq instr cas reg rex lexpr ordr ordw xmod (INSTR: instr = Instr.update cas rex xmod ordr ordw reg lexpr) Pi (COMP: exists PO, is_thread_compiled PO Pi) (IN: In instr Pi):
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

  Lemma gsw_trans G1 G2 G3 (SIM1: graphs_sim_weak G1 G2)
        (SIM2: graphs_sim_weak G2 G3):
    graphs_sim_weak G1 G3.
  Proof.
    red in SIM1, SIM2. desc.
    red.
    assert (E G1 ≡₁ E G3) as E_EQV.
    { eapply set_equiv_rel_Transitive; eauto. }
    splits; auto.
    { ins. rewrite SIM8; auto. apply SIM0. apply SIM1. auto. }
    all: eapply same_rel_Transitive; eauto.
  Qed. 
        
  
  (* Lemma sbl_helper tid POi PIi GO GOi GIi SGO *)
  (*       (THREAD: Some POi = IdentMap.find tid ProgO) *)
  (*       (THREADI : Some PIi = IdentMap.find tid ProgI) *)
  (*       (COMP: is_thread_compiled POi PIi) *)
  (*       (RESTR: thread_restricted_execution GO tid GOi) *)
  (*       (RESTR0: thread_restricted_execution GI tid GIi) *)
  (*       (EXECIi: thread_execution tid PIi GIi) *)
  (*       (H: Othread_execution tid POi SGO) *)
  (*       (H0: same_behavior_local SGO GIi): *)
  (*   same_behavior_local GOi GIi. *)
  (* Proof. *)
  (*     red. splits. *)
  (*     { pose proof H0 as SBL. destruct RESTR. *)
  (*       red in H0. desc. rewrite <- RESTR_EVENTS.  *)
  (*       rewrite tr_acts_set. subst GO. unfold acts_set. simpl. *)
  (*       arewrite ((fun x : actid => In x (GO_actsset ++ GO_initset)) ∩₁ Tid_ tid ≡₁ ((fun x : actid => In x (GO_actsset))  ∩₁ Tid_ tid)) by admit. *)
  (*       arewrite ((fun x : actid => In x GO_actsset) ≡₁ all_acts). *)
  (*       { apply set_equiv_exp_iff. ins. symmetry. vauto. } *)
  (*       unfold all_acts.  *)
  (*       rewrite <- set_bunion_inter_compat_r. *)
  (*       unfold set_inter. *)
  (*       arewrite ((⋃₁x ∈ hlpr_restr, *)
  (*   fun x0 : actid => *)
  (*   (exists GOi0 : execution, hlpr_GO GOi0 x /\ E GOi0 x0) /\ *)
  (*   Events.tid x0 = tid) ≡₁ (⋃₁x ∈ hlpr_restr, *)
  (*   fun x0 : actid => *)
  (*   (exists GOi0 : execution, hlpr_GO GOi0 x /\ E GOi0 x0 /\ *)
  (*                        Events.tid x0 = tid))) by basic_solver 100.  *)
  (*       apply set_equiv_exp_iff. ins. red. split. *)
  (*       2: { ins. red. exists ({| htid := tid; hPO := POi; hPI := PIi; hSGI := GIi |}). *)
  (*            splits; vauto. *)
  (*            exists SGO. splits; vauto. *)
  (*            admit. } *)
  (*       { ins. cut (E SGO x); [ins; vauto| ]. *)
  (*         red in H0. desc. subst. *)
  (*         destruct y. red in H0. red in H1. desc. simpl in *. *)
  (*         destruct x. *)
  (*         { simpl in *. exfalso. *)
  (*           apply programs_without_tid_init. apply find_iff_in. vauto. } *)
  (*         simpl in *. *)
  (*         assert (htid0 = thread). *)
  (*         { red in H3. desc. rewrite (set_equiv_exp RESTR_EVENTS0) in H2. *)
  (*           red in H2. desc. *)
  (*           destruct H5. rewrite (set_equiv_exp tr_acts_set0) in H2. *)
  (*           red in H2. desc. vauto. } *)
  (*         subst htid0. assert (hPI0 = PIi /\ hPO0 = POi) by (split; congruence). *)
  (*         desc. subst hPI0 hPO0. clear H4 H0. *)
  (*         cut (graphs_sim_weak SGO GOi0). *)
  (*         { ins. red in H0. desc. apply H0. auto. } *)
  (*         cut (graphs_sim_weak GIi hSGI0). *)
  (*         { ins. eapply sbl_sim_rect; vauto. *)
  (*           eapply wf_tre_intra_E; vauto. } *)
  (*         eapply tre_sim_weak; vauto. } } *)
  

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

  (* Lemma sbl_thread_local GO: *)
  (*   (forall tid Pi (THREAD: Some Pi = IdentMap.find tid ProgI) *)
  (*      Gi (THREAD_Gi: thread_restricted_execution GI tid Gi) *)
  (*      Go (THREAD_Go: thread_restricted_execution GO tid Go), *)
  (*       same_behavior_local Go Gi) -> same_behavior_local GO GI.  *)
  (* Proof. *)
  (*   intros LOCAL. red.  *)
    
  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    pose proof thread_execs_helper as T_E_H.
    specialize_full T_E_H; vauto. 
    desc.
    exists GO.    
    split.  
    { red. split; auto. 
      ins. symmetry in INTHREAD. 
      specialize (RESTR_SIM _ _ INTHREAD). desc. 
      desc. exists GOi. split; auto. }
    red. splits; auto.
    2: { rewrite SAME_CO. auto. }
    2: { ins. destruct WFI. congruence. }
    red. splits; auto.   
    2: { ins. (* pose proof EGOx as EGOx_. *)
         specialize (E_STRUCT _ EGOx). des.  
         { destruct x; vauto. destruct WFI. congruence. }
         destruct x.
         { destruct WFI. congruence. }
         simpl in *. apply find_iff_in in E_STRUCT. destruct E_STRUCT as [POi THREADO]. 
         specialize (RESTR_SIM _ _ THREADO). destruct RESTR_SIM as [GIi [GOi [TREo [TREi [OEXEC SBL]]]]].
         assert (E GOi (ThreadEvent thread index)) as EGOix.
         { destruct TREo. apply  tr_acts_set. split; auto. }
         replace (lab GO (ThreadEvent thread index)) with (lab GOi (ThreadEvent thread index)).
         2: { destruct TREo. auto. }
         replace (lab GI _) with (lab GIi (ThreadEvent thread index)).
         2: { destruct TREi. apply tr_lab.
              apply tr_acts_set. split; auto. 
              cdes SBL. apply RESTR_EVENTS in EGOix. red in EGOix. desc.
              apply tr_acts_set in EGOix. red in EGOix. desc. auto. }
         cdes SBL. desc. apply SAME_LAB. auto. }
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
      specialize (E_STRUCT x EGOx). destruct E_STRUCT; vauto.
      destruct x; vauto. simpl in *. apply find_iff_in in H. destruct H as [POi THREADO]. 
      specialize (RESTR_SIM _ _ THREADO). destruct RESTR_SIM as [GIi [GOi [TREo [TREi [OEXEC SBL]]]]].
      assert (E GOi (ThreadEvent thread index)) as EGOix.
      { destruct TREo. apply tr_acts_set. vauto. }
      assert (E GIi (ThreadEvent thread index)) as EGIix.
      { cdes SBL. apply RESTR_EVENTS in EGOix. red in EGOix. desc. auto. }
      split; vauto. split.
      { eapply E_restr_iff; eauto. }        
      (* apply (set_equiv_exp RESTR_EVENTS) in EGOix.  *)
      cdes SBL. apply RESTR_EVENTS in EGOix. red in EGOix. desc.
      do 2 red in EGOix0. desc.  
      red. split.
      { cdes TREi. 
        replace (RW GI _) with (RW GIi (ThreadEvent thread index)); vauto. 
        unfold is_r, is_w, set_union.
        destruct TREi. rewrite tr_lab; auto. }
      red. ins. apply EGOix1.
      destruct TREi.
      apply (dom_rel_more tr_rmw).
      apply dom_eqv1. split; auto.
      red in H. desc.
      red. exists y. apply seq_eqv_r. split; auto. 
      apply (hahn_inclusion_exp (rmw_in_sb WFI)) in H.
      apply sb_tid_init in H. simpl in H. destruct H; vauto. }
    ins. red in H. desc. split; auto. 
    destruct x; vauto.
    red in H. desc.
    red in ExecI. destruct ExecI as [IMM_EVENTS _].
    specialize (IMM_EVENTS _ H). des; vauto. simpl in IMM_EVENTS.
    apply find_iff_in in IMM_EVENTS. destruct IMM_EVENTS as [PIi THREADI]. 
    assert (exists POi, Some POi = IdentMap.find thread ProgO) as [POi THREADO]. 
    { apply find_iff_in. red in Compiled. destruct Compiled.
      apply H2. apply find_iff_in. eauto. }
    specialize (RESTR_SIM _ _ THREADO). destruct RESTR_SIM as [GIi [GOi [TREo [TREi [OEXEC SBL]]]]].
    eapply E_restr_iff; eauto.
    assert (E GIi (ThreadEvent thread index)) as EGIi. 
    { destruct TREi. apply tr_acts_set. split; auto. }
    cdes SBL. apply RESTR_EVENTS. split; auto.
    do 2 red in H1. desc.  
    red. split. 
    { unfold is_r, is_w, set_union.
      destruct TREi. rewrite tr_lab; auto. }
    red. ins. apply H2.
    destruct TREi. apply (dom_rel_more tr_rmw) in H3.
    generalize H3. basic_solver. 
  Qed. 

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI)
        (ExecO: Oprogram_execution OCamlProgO GO):
    ocaml_consistent GO.
  Proof.
    pose proof (Wf_subgraph SB WFI) as WFO. 
    cdes SB. cdes SAME_LOCAL. 
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
      rewrite <- restr_union, restr_restr.
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
      rewrite restr_union.
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
    splits; auto.    
    apply graph_switch; auto.
    apply (imm_implies_omm). 
  Qed.  

End CompilationCorrectness.       