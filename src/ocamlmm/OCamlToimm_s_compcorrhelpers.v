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


Section CompCorrHelpers.
    
  Definition f_acq_matcher :=
    fun lbl => match lbl with
            | Afence mode => mode_le Oacq mode
            | _ => false
            end.
  Definition is_f_acq := fun {A: Type} (labfun: A -> label) ev =>
                           is_f labfun ev && is_acq labfun ev. 
             
  Lemma f_acq_pl: processes_lab (@is_f_acq actid) f_acq_matcher. 
  Proof.
    red. intros. unfold is_f_acq, is_f, is_acq, f_acq_matcher, mode_le, Events.mod. 
    type_solver. 
  Qed. 

  Definition f_acqrel_matcher :=
    fun lbl => match lbl with
            | Afence mode => mode_le Oacqrel mode
            | _ => false
            end.
  Definition is_f_acqrel := fun {A: Type} (labfun: A -> label) ev =>
                           is_f labfun ev && is_acqrel labfun ev. 
             
  Lemma f_acqrel_pl: processes_lab (@is_f_acqrel actid) f_acqrel_matcher. 
  Proof.
    red. intros. unfold is_f_acqrel, is_f, is_acqrel, f_acqrel_matcher, mode_le, Events.mod. 
    type_solver. 
  Qed. 

  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  Notation "'F' G" := (fun a => is_true (is_f G.(lab) a)) (at level 1).
  Notation "'AcqF' G" := (fun a => is_true (is_f_acq G.(lab) a)) (at level 1).
  Notation "'AcqrelF' G" := (fun a => is_true (is_f_acqrel G.(lab) a)) (at level 1).
  Notation "'ORlx' G" := (fun a => is_true (is_only_rlx G.(lab) a)) (at level 1).
  Notation "'ORlxW' G" := (fun a => is_true (is_orlx_w G.(lab) a)) (at level 1).
  Notation "'Sc' G" := (fun a => is_true (is_sc G.(lab) a)) (at level 1). 
  Notation "'Acq' G" := (fun a => is_true (is_acq G.(lab) a)) (at level 1). 
  Notation "'Acqrel' G" := (fun a => is_true (is_acqrel G.(lab) a)) (at level 1). 
  Notation "'R_ex' G" := (fun a => is_true (R_ex G.(lab) a)) (at level 1).
  Notation "'hbo'" := (OCaml.hb). 
  Notation "'same_loc' G" := (same_loc G.(lab)) (at level 1).
  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

  Definition omm_premises_hold G :=
    (* separated *)
    (* let Loc_ := fun l x => loc G.(lab) x = Some l in *)
    (* ⟪ LSM : forall l, (Loc_ l \₁ is_init ⊆₁ (ORlx G)  \/  Loc_ l \₁ is_init ⊆₁ (Sc G)) ⟫ /\ *)
    ⟪ WSCFACQRMW : E G ∩₁ W G ∩₁ Sc G ≡₁ codom_rel (⦗AcqF G⦘ ⨾ immediate (sb G) ⨾ rmw G) ⟫ /\
    ⟪ RMWSC  : rmw G ≡ ⦗Sc G⦘ ⨾ rmw G⨾ ⦗Sc G⦘ ⟫ /\
    ⟪ WRLXF : E G ∩₁ ORlxW G ⊆₁ codom_rel (⦗AcqrelF G⦘ ⨾ immediate (sb G)) ⟫ /\
    ⟪ RSCF  : E G ∩₁ R G ∩₁ Sc G ⊆₁ codom_rel (⦗AcqF G⦘ ⨾ immediate (sb G)) ⟫.

  Hint Resolve r_pl w_pl acq_pl acqrel_pl sc_pl orlx_w_pl f_acqrel_pl f_acq_pl : label_ext.
  
  Definition step0 st1 st2 tid :=
    ⟪STEP: step tid st1 st2 ⟫ /\
    ⟪ADD0: G st2 = G st1⟫. 
        
  Definition step1 st1 st2 tid index label :=
    ⟪STEP: step tid st1 st2 ⟫ /\
    ⟪ADD1: exists foo bar baz bazz, G st2 = add (G st1) tid index label foo bar baz bazz⟫.

  Definition step2 st1 st2 tid index label1 label2 :=
    ⟪STEP: step tid st1 st2 ⟫ /\
    ⟪ADD1: exists foo bar baz bazz, G st2 = add_rmw (G st1) tid index label1 label2 foo bar baz bazz⟫.

  Lemma step1_index_exact st1 st2 tid index label (STEP1: step1 st1 st2 tid index label):
    index = eindex st1 /\ eindex st2 = eindex st1 + 1. 
  Proof.
    red in STEP1. desc.
    assert (forall G a b c d e f g, G <> add G a b c d e f g) as ADD_NEQ.
    { ins. red. ins. unfold add in H.
      apply (@f_equal _ _ acts) in H. simpl in H.
      apply (@f_equal _ _ (@length _)) in H. simpl in H. omega. }
    assert (forall G a b c d e f g a' b' c' d' e' f' g' h',
               add_rmw G a' b' c' d' e' f' g' h' <> add G a b c d e f g) as ADD_RMW_NEQ.
    { ins. red. ins. unfold add, add_rmw in H.
      apply (@f_equal _ _ acts) in H. simpl in H.
      apply (@f_equal _ _ (@length _)) in H. simpl in H. omega. }
    do 2 (red in STEP; desc).
    inversion ISTEP0.
    all: try (rewrite UG in ADD1; apply ADD_NEQ in ADD1; by vauto).
    all: try (rewrite UG in ADD1; apply ADD_RMW_NEQ in ADD1; by vauto).
    all: split; auto. 
    all: rewrite ADD1 in UG; apply (@f_equal _ _ acts) in UG; simpl in UG.
    all: inversion UG; auto.
  Qed. 
        
  Lemma step2_index_exact st1 st2 tid index label1 label2 (STEP1: step2 st1 st2 tid index label1 label2):
    index = eindex st1 /\ eindex st2 = eindex st1 + 2. 
  Proof.
    red in STEP1. desc.
    assert (forall G a b c d e f g h, G <> add_rmw G a b c d e f g h) as ADD_RMW_NEQ.
    { ins. red. ins. unfold add in H.
      apply (@f_equal _ _ acts) in H. simpl in H.
      apply (@f_equal _ _ (@length _)) in H. simpl in H. omega. }
    assert (forall G a b c d e f g a' b' c' d' e' f' g' h',
               add G a b c d e f g <> add_rmw G a' b' c' d' e' f' g' h') as ADD_RMW_ADD_NEQ.
    { ins. red. ins. unfold add, add_rmw in H.
      apply (@f_equal _ _ acts) in H. simpl in H.
      apply (@f_equal _ _ (@length _)) in H. simpl in H. omega. }
    do 2 (red in STEP; desc).
    inversion ISTEP0.
    all: try (rewrite UG in ADD1; apply ADD_RMW_NEQ in ADD1; by vauto).
    all: try (rewrite UG in ADD1; apply ADD_RMW_ADD_NEQ in ADD1; by vauto).
    all: split; auto. 
    all: rewrite ADD1 in UG; apply (@f_equal _ _ acts) in UG; simpl in UG.
    all: inversion UG; auto.
  Qed. 
        
  (* Lemma step2_index_increase st1 st2 tid index label1 label2 (STEP2: step2 st1 st2 tid index label1 label2): *)
  (*   eindex st1 < eindex st2. *)
  (* Proof. *)
  (*   red in STEP2. desc. *)
  (*   assert (forall G a b c d e f g h, G <> add_rmw G a b c d e f g h) as ADD_RMW_NEQ.  *)
  (*   { ins. red. ins. unfold add_rmw in H. *)
  (*     apply (@f_equal _ _ acts) in H. simpl in H. *)
  (*     apply (@f_equal _ _ (@length _)) in H. simpl in H. omega. }  *)
  (*   do 2 (red in STEP; desc). *)
  (*   inversion ISTEP0. *)
  (*   all: try (rewrite UG in ADD1; apply ADD_RMW_NEQ in ADD1; by vauto). *)
  (*   all: omega. *)
  (* Qed.  *)
        


  Lemma immediate_sb_repr st thread (WFT: wf_thread_state thread st):
    immediate (sb (G st)) ≡ (fun e1 e2 =>
                               exists ind, e1 = ThreadEvent thread ind /\
                                      e2 = ThreadEvent thread (ind + 1) /\
                                      ind + 1 < eindex st). 
  Proof.
    split.
    { red. ins. red in H. desc.
      unfold sb in H. apply seq_eqv_lr in H. destruct H as [Ex [ESBxy Ey]]. 
      destruct y.
      { red in ESBxy. destruct x; vauto. }
      assert (thread0 = thread); [| subst thread0]. 
      { destruct WFT. specialize (acts_rep _ Ey). desc. vauto. }
      destruct x.
      { destruct WFT. specialize (acts_rep _ Ex). desc. vauto. }
      red in ESBxy. desc. subst.
      exists index0. splits; auto.
      2: { destruct WFT. specialize (acts_rep _ Ey). desc. inversion REP.
           subst. omega. }
      f_equal.
      destruct (NPeano.Nat.eq_decidable index (index0 + 1)); auto.
      assert (E (G st) (ThreadEvent thread (index0 + 1))) as E'.
      { destruct WFT. specialize (acts_clos (index0 + 1)).
        apply acts_clos.
        specialize (acts_rep _ Ey). desc. inversion REP. omega. }
      exfalso. apply (H0 (ThreadEvent thread (index0 + 1))).
      all: red; apply seq_eqv_lr; splits; auto; red; splits; [auto| omega]. }
    red. ins. desc. subst. 
    assert (E (G st) (ThreadEvent thread ind)) as Ex. 
    { destruct WFT. specialize (acts_clos ind).
      subst. apply acts_clos. omega. }
    assert (E (G st) (ThreadEvent thread (ind + 1))) as Ey. 
    { destruct WFT. specialize (acts_clos (ind + 1)).
      subst. apply acts_clos. omega. }
    red. split.
    { apply seq_eqv_lr. splits; auto. red. split; [auto| omega]. }
    ins. apply seq_eqv_lr in R1. apply seq_eqv_lr in R2. desc. 
    destruct c; vauto. red in R4. red in R0. desc. subst. omega. 
  Qed. 
    
  Lemma singl_rel_event_repr thread ind:
    singl_rel (ThreadEvent thread ind) (ThreadEvent thread (ind + 1)) ≡
              (fun e1 e2 => e1 = ThreadEvent thread ind /\
                         e2 = ThreadEvent thread (ind + 1)). 
  Proof. basic_solver. Qed. 

  Lemma step_1_label_ext_helper st1 st2 tid new_label index        
        (STEP1: step1 st1 st2 tid index new_label)
        n (REACH: (step tid) ^^ n (init (instrs st1)) st1):
    let lbl_ext (S: (actid -> label) -> actid -> bool)
                (matcher : label -> bool) :=
        S (lab (G st2)) ≡₁ S (lab (G st1)) ∪₁ (if matcher new_label then eq (ThreadEvent tid index) else ∅) in
    ⟪E_EXT: E (G st2) ≡₁ E (G st1) ∪₁ eq (ThreadEvent tid index) ⟫ /\
    ⟪RMW_EXT: rmw (G st2) ≡ rmw (G st1) ⟫ /\
    ⟪SB_EXT: E (G st1) ≡₁ ∅ \/ immediate (sb (G st2)) ≡ immediate (sb (G st1)) ∪ singl_rel (ThreadEvent tid (index - 1)) (ThreadEvent tid index) ⟫ /\
    ⟪R_EXT: lbl_ext (@is_r actid) r_matcher ⟫ /\
    ⟪W_EXT: lbl_ext (@is_w actid) w_matcher ⟫ /\
    ⟪W_ORLX_EXT: lbl_ext (@is_orlx_w actid) orlx_w_matcher ⟫ /\
    ⟪F_ACQ_EXT: lbl_ext (@is_f_acq actid) f_acq_matcher ⟫ /\
    ⟪F_ACQREL_EXT: lbl_ext (@is_f_acqrel actid) f_acqrel_matcher ⟫ /\
    ⟪SC_EXT: lbl_ext (@is_sc actid) sc_matcher⟫ .
  Proof.
    forward eapply step1_index_exact; eauto. ins. destruct H as [H EINDEX2].  subst. 
    red in STEP1. desc. 
    pose proof label_set_step as LBL_STEP.
    specialize LBL_STEP with (st1 := st1) (st2 := st2) (tid := tid).
    assert (E (G st2) ≡₁ E (G st1) ∪₁ eq (ThreadEvent tid (eindex st1))) as E_EXT. 
    { desc. rewrite ADD1. unfold acts_set. basic_solver. }
    simpl. splits; auto. 
    { desc. rewrite ADD1. basic_solver. }
    { assert (wf_thread_state tid st1) as WFT.
      { eapply wf_thread_state_steps with (s := init (instrs st1)); [apply wf_thread_state_init| ].
        apply crt_num_steps. eauto. }
      destruct (gt_0_eq (eindex st1)).
      2: { left. split; [| basic_solver]. red. ins. red in H0.
           destruct WFT. specialize (acts_rep x H0). desc. omega. }
      right.
      assert (wf_thread_state tid st1) as WFT1. 
      { eapply wf_thread_state_steps with (s := init (instrs st1)); [apply wf_thread_state_init| ].
        apply crt_num_steps. eauto. }
      assert (wf_thread_state tid st2) as WFT2.
      { eapply wf_thread_state_step; eauto. }
      rewrite (immediate_sb_repr WFT1), (immediate_sb_repr WFT2); eauto.
      replace (eindex st1) with ((eindex st1 - 1) + 1) at 2 by omega.
      rewrite EINDEX2. 
      rewrite singl_rel_event_repr.
      split.
      { red. ins. desc. subst. destruct (Nat.lt_decidable (ind + 1) (eindex st1)).
        { red. left. eexists. splits; eauto. }
        red. right. splits.
        all: f_equal; omega. }
      red. ins. red in H0. des.
      { subst. eexists. splits; eauto. omega. }
      subst. eexists. splits; eauto. omega. }
    all: apply LBL_STEP; eauto with label_ext.
    all: eapply nonnop_bounded; eauto with label_ext; vauto.
  Qed. 
              
  Lemma step_2_label_ext_helper st1 st2 tid new_label1 new_label2 index        
        (STEP2: step2 st1 st2 tid index new_label1 new_label2)
        n (REACH: (step tid) ^^ n (init (instrs st1)) st1):
    let ev1 := (ThreadEvent tid index) in
    let ev2 := (ThreadEvent tid (index + 1)) in
    let lbl_ext2 (S: (actid -> label) -> actid -> bool)
                (matcher : label -> bool) :=
        S (lab (G st2)) ≡₁ S (lab (G st1)) ∪₁ (if matcher new_label1 then eq ev1 else ∅) ∪₁ (if matcher new_label2 then eq ev2 else ∅) in
    ⟪E_EXT: E (G st2) ≡₁ E (G st1) ∪₁ eq ev1 ∪₁ eq ev2 ⟫ /\
    ⟪RMW_EXT: rmw (G st2) ≡ rmw (G st1) ∪ singl_rel ev1 ev2 ⟫ /\
    ⟪SB_EXT: E (G st1) ≡₁ ∅ \/ immediate (sb (G st2)) ≡ immediate (sb (G st1)) ∪ singl_rel (ThreadEvent tid (index - 1)) ev1 ∪ singl_rel ev1 ev2 ⟫ /\
    ⟪R_EXT: lbl_ext2 (@is_r actid) r_matcher ⟫ /\
    ⟪W_EXT: lbl_ext2 (@is_w actid) w_matcher ⟫ /\
    ⟪W_ORLX_EXT: lbl_ext2 (@is_orlx_w actid) orlx_w_matcher ⟫ /\
    ⟪F_ACQ_EXT: lbl_ext2 (@is_f_acq actid) f_acq_matcher ⟫ /\
    ⟪F_ACQREL_EXT: lbl_ext2 (@is_f_acqrel actid) f_acqrel_matcher ⟫ /\
    ⟪SC_EXT: lbl_ext2 (@is_sc actid) sc_matcher⟫ .
  Proof.
    forward eapply step2_index_exact; eauto. ins. destruct H as [H EINDEX2].  subst. 
    red in STEP2. desc. 
    pose proof label_set_rmw_step as LBL_STEP.
    specialize LBL_STEP with (st1 := st1) (st2 := st2) (tid := tid).
    assert (E (G st2) ≡₁ E (G st1) ∪₁ eq (ThreadEvent tid (eindex st1)) ∪₁ eq (ThreadEvent tid (eindex st1 + 1))) as E_EXT. 
    { desc. rewrite ADD1. unfold acts_set. basic_solver. }
    simpl. splits; auto. 
    { desc. rewrite ADD1. unfold add_rmw. simpl. basic_solver. }
    { assert (wf_thread_state tid st1) as WFT1. 
      { eapply wf_thread_state_steps with (s := init (instrs st1)); [apply wf_thread_state_init| ].
        apply crt_num_steps. eauto. }
      assert (wf_thread_state tid st2) as WFT2.
      { eapply wf_thread_state_step; eauto. }
      destruct (gt_0_eq (eindex st1)).
      2: { left. split; [| basic_solver]. red. ins. red in H0.
           destruct WFT1. specialize (acts_rep x H0). desc. omega. }
      right.
      rewrite (immediate_sb_repr WFT1), (immediate_sb_repr WFT2); eauto.
      replace (eindex st1) with ((eindex st1 - 1) + 1) at 2 by omega. 
      do 2 rewrite singl_rel_event_repr.
      rewrite EINDEX2. split.
      { rewrite unionA. red. ins. desc. subst.
        destruct (Const.lt_ge_cases (ind + 1) (eindex st1)).
        { red. left. eexists. splits; eauto. }
        red. right. destruct (NPeano.Nat.eq_decidable (ind + 1) (eindex st1)).
        { red. left. splits; vauto; f_equal; omega. }
        red. right. splits; vauto; f_equal; omega. }
      red. ins. destruct H0 as [[SB1 | SB'] | SB''].
      { desc. eexists. splits; eauto. omega. }
      { desc. subst. eexists. splits; eauto. omega. }
      desc. subst. eexists. splits; eauto. omega.
      }
    (* { apply LBL_STEP.  *)
    all: apply LBL_STEP; eauto with label_ext.
    all: eapply nonnop_bounded; eauto with label_ext; vauto.
  Qed. 
  
  Lemma unique_restr x y (r: relation actid) (Rxy: r x y):
    ⦗eq x⦘ ⨾ r ⨾ ⦗eq y⦘ ≡ singl_rel x y.
  Proof.
    ins. rewrite seq_eqv_lr. split.
    { red. ins. desc. red. splits; auto. }
    red. ins. red in H. desc. splits; vauto.
  Qed.

  Lemma EXTSB_IRR e:
    ⦗eq e⦘ ⨾ ext_sb ⨾ ⦗eq e⦘ ≡ ∅₂.
  Proof. 
    split; [| basic_solver]. rewrite seq_eqv_lr. red. ins.
    desc. subst. red in H0. destruct y; vauto. desc. omega.
  Qed. 

  Lemma EXTSB_MON e1 e2 (GT: index e1 > index e2):
    ⦗eq e1⦘ ⨾ ext_sb ⨾ ⦗eq e2⦘ ≡ ∅₂. 
  Proof.
    split; [| basic_solver]. rewrite seq_eqv_lr. red. ins.
    desc. subst. destruct x.
    { simpl in GT. omega. }
    destruct y; vauto. simpl in H0. simpl in GT. desc. omega.
  Qed. 

  Lemma step_11_label_ext_helper st1 st2 st3 tid new_label1 new_label2 index1 index2
        (IND1: index1 >= eindex st1) (IND2: index2 >= eindex st2)
        (STEP11: step1 st1 st2 tid index1 new_label1)
        (STEP12: step1 st2 st3 tid index2 new_label2)
        n (REACH: (step tid) ^^ n (init (instrs st1)) st1):
    let ev1 := (ThreadEvent tid index1) in
    let ev2 := (ThreadEvent tid index2) in
    let lbl_ext2 (S: (actid -> label) -> actid -> bool)
                (matcher : label -> bool) :=
        S (lab (G st3)) ≡₁ S (lab (G st1)) ∪₁ (if matcher new_label1 then eq ev1 else ∅) ∪₁ (if matcher new_label2 then eq ev2 else ∅) in
    ⟪E_EXT: E (G st3) ≡₁ E (G st1) ∪₁ eq ev1 ∪₁ eq ev2 ⟫ /\
    ⟪RMW_EXT: rmw (G st3) ≡ rmw (G st1) ⟫ /\
    ⟪SB_EXT: (E (G st1) ≡₁ ∅ /\ sb (G st3) ≡ singl_rel ev1 ev2) \/
             immediate (sb (G st3)) ≡ immediate (sb (G st1)) ∪ singl_rel (ThreadEvent tid (index1 - 1)) ev1 ∪ singl_rel ev1 ev2 ⟫ /\
    ⟪R_EXT: lbl_ext2 (@is_r actid) r_matcher ⟫ /\
    ⟪W_EXT: lbl_ext2 (@is_w actid) w_matcher ⟫ /\
    ⟪W_ORLX_EXT: lbl_ext2 (@is_orlx_w actid) orlx_w_matcher ⟫ /\
    ⟪F_ACQ_EXT: lbl_ext2 (@is_f_acq actid) f_acq_matcher ⟫ /\
    ⟪F_ACQREL_EXT: lbl_ext2 (@is_f_acqrel actid) f_acqrel_matcher ⟫ /\
    ⟪SC_EXT: lbl_ext2 (@is_sc actid) sc_matcher⟫ .
  Proof.
    forward eapply (@step1_index_exact st1 st2) as [H EINDEX2]; eauto.
    forward eapply (@step1_index_exact st2 st3) as [H' EINDEX3]; eauto.
    ins. subst. 
    forward eapply (@step_1_label_ext_helper st1 st2 tid) as STEP1; eauto.
    red in STEP11. desc.
    forward eapply (@step_1_label_ext_helper st2 st3 tid new_label2 (eindex st2)) as STEP2; eauto.
    { Unshelve. 2: exact (S n). replace (instrs st2) with (instrs st1).      
      2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
      apply step_prev. exists st1. split; auto. }
    simpl in *. desc. simpl. splits.
    4: { rewrite R_EXT, R_EXT0. auto. }
    4: { rewrite W_EXT, W_EXT0. auto. }
    4: { rewrite W_ORLX_EXT, W_ORLX_EXT0. auto. }
    4: { rewrite F_ACQ_EXT, F_ACQ_EXT0. auto. }
    4: { rewrite F_ACQREL_EXT, F_ACQREL_EXT0. auto. }
    4: { rewrite SC_EXT, SC_EXT0. auto. }
    { rewrite E_EXT, E_EXT0. auto. }
    { rewrite RMW_EXT, RMW_EXT0. auto. }
    { clear W_EXT. clear W_EXT0. clear W_ORLX_EXT. clear W_ORLX_EXT0. clear F_ACQ_EXT. clear F_ACQ_EXT0. clear F_ACQREL_EXT. clear F_ACQREL_EXT0. clear SC_EXT. clear SC_EXT0. clear R_EXT. clear R_EXT0. clear RMW_EXT. clear RMW_EXT0.
      destruct SB_EXT as [NO_E2 | E2_ADD].
      { exfalso. generalize E_EXT0. rewrite NO_E2. basic_solver. }
      desc.
      destruct SB_EXT0 as [NO_E1 | E1_ADD].
      { left. split; auto.
        unfold sb. rewrite E_EXT, E_EXT0, NO_E1. remove_emptiness.
        rewrite id_union. rewrite seq_union_l, !seq_union_r.
        repeat rewrite EXTSB_IRR.
        rewrite EXTSB_MON with (e1 := (ThreadEvent tid (eindex st2))). 
        2: { simpl. omega. }
        remove_emptiness.
        apply unique_restr. red. split; [auto| omega]. }
      right. rewrite E2_ADD, E1_ADD.
      replace (eindex st2 - 1) with (eindex st1); auto. omega. }
    Qed.          

  Lemma comm_helper tid index S:
    eq (ThreadEvent tid index) ∩₁ S ≡₁ S ∩₁ eq (ThreadEvent tid index).
  Proof. by ins; apply set_interC. Qed. 

  Ltac discr_new_body := rewrite label_set_bound_inter; [| by eauto | by omega | by (eauto with label_ext) | by vauto].
  Ltac discr_new := discr_new_body || (rewrite comm_helper; discr_new_body). 
  Ltac discr_E_body := rewrite E_bound_inter; [| by eauto | by omega]. 
  Ltac discr_E := discr_E_body || (rewrite comm_helper; discr_E_body). 
  Ltac discr_events := rewrite diff_events_empty; [| by omega].
  Ltac same_events := rewrite set_interK.
  Ltac simplify_updated_sets := repeat (discr_new || discr_E || discr_events || same_events); remove_emptiness.

  Ltac unfold_clear_updated st := repeat match goal with
                            | H: ?eset ≡₁ ?eset' |- _ => try rewrite H; clear H
                            | H: ?erel ≡ ?erel' |- _ => try rewrite H; clear H
                                         end.
  Ltac expand_sets_only := try rewrite !set_inter_union_r; remove_emptiness; try rewrite !set_inter_union_l; remove_emptiness. 
  Ltac expand_rels := try rewrite !seq_union_l; remove_emptiness; try rewrite !seq_union_r; try expand_sets_only. 
  Ltac by_IH IH := red in IH; desc; vauto. 
        
  Lemma step_12_label_ext_helper st1 st2 st3 tid new_label1 new_label21 new_label22 index1 index2
        (IND1: index1 >= eindex st1) (IND2: index2 >= eindex st2)
        (STEP11: step1 st1 st2 tid index1 new_label1)
        (STEP12: step2 st2 st3 tid index2 new_label21 new_label22)
        n (REACH: (step tid) ^^ n (init (instrs st1)) st1):
    let ev1 := (ThreadEvent tid index1) in
    let ev2 := (ThreadEvent tid index2) in
    let ev3 := (ThreadEvent tid (index2 + 1)) in
    let lbl_ext3 (S: (actid -> label) -> actid -> bool)
                (matcher : label -> bool) :=
        S (lab (G st3)) ≡₁ S (lab (G st1)) ∪₁
          (if matcher new_label1 then eq ev1 else ∅) ∪₁
          (if matcher new_label21 then eq ev2 else ∅) ∪₁
          (if matcher new_label22 then eq ev3 else ∅) in
    ⟪E_EXT: E (G st3) ≡₁ E (G st1) ∪₁ eq ev1 ∪₁ eq ev2  ∪₁ eq ev3 ⟫ /\
    ⟪RMW_EXT: rmw (G st3) ≡ rmw (G st1) ∪ singl_rel ev2 ev3⟫ /\
    ⟪SB_EXT: (E (G st1) ≡₁ ∅ /\ sb (G st3) ≡ singl_rel ev1 ev2 ∪ singl_rel ev2 ev3 ∪ singl_rel ev1 ev3) \/
             immediate (sb (G st3)) ≡ immediate (sb (G st1)) ∪ singl_rel (ThreadEvent tid (index1 - 1)) ev1 ∪ singl_rel ev1 ev2  ∪ singl_rel ev2 ev3 ⟫ /\
    ⟪R_EXT: lbl_ext3 (@is_r actid) r_matcher ⟫ /\
    ⟪W_EXT: lbl_ext3 (@is_w actid) w_matcher ⟫ /\
    ⟪W_ORLX_EXT: lbl_ext3 (@is_orlx_w actid) orlx_w_matcher ⟫ /\
    ⟪F_ACQ_EXT: lbl_ext3 (@is_f_acq actid) f_acq_matcher ⟫ /\
    ⟪F_ACQREL_EXT: lbl_ext3 (@is_f_acqrel actid) f_acqrel_matcher ⟫ /\
    ⟪SC_EXT: lbl_ext3 (@is_sc actid) sc_matcher⟫ .
  Proof.
    forward eapply (@step1_index_exact st1 st2) as [H EINDEX2]; eauto.
    forward eapply (@step2_index_exact st2 st3) as [H' EINDEX3]; eauto.
    ins. subst. 
    forward eapply (@step_1_label_ext_helper st1 st2 tid) as STEP1; eauto.
    red in STEP11. desc.
    forward eapply (@step_2_label_ext_helper st2 st3 tid new_label21 new_label22 (eindex st2)) as STEP2; eauto.
    { Unshelve. 2: exact (S n). replace (instrs st2) with (instrs st1).      
      2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
      apply step_prev. exists st1. split; auto. }
    simpl in *. desc. simpl. splits.
    4: { rewrite R_EXT, R_EXT0. auto. }
    4: { rewrite W_EXT, W_EXT0. auto. }
    4: { rewrite W_ORLX_EXT, W_ORLX_EXT0. auto. }
    4: { rewrite F_ACQ_EXT, F_ACQ_EXT0. auto. }
    4: { rewrite F_ACQREL_EXT, F_ACQREL_EXT0. auto. }
    4: { rewrite SC_EXT, SC_EXT0. auto. }
    { rewrite E_EXT, E_EXT0. auto. }
    { rewrite RMW_EXT, RMW_EXT0. auto. }
    { clear W_EXT. clear W_EXT0. clear W_ORLX_EXT. clear W_ORLX_EXT0. clear F_ACQ_EXT. clear F_ACQ_EXT0. clear F_ACQREL_EXT. clear F_ACQREL_EXT0. clear SC_EXT. clear SC_EXT0. clear R_EXT. clear R_EXT0. clear RMW_EXT. clear RMW_EXT0.
      destruct SB_EXT as [NO_E2 | E2_ADD].
      { exfalso. generalize E_EXT0. rewrite NO_E2. basic_solver. }
      desc.
      destruct SB_EXT0 as [NO_E1 | E1_ADD].
      { left. split; auto.
        unfold sb. rewrite E_EXT, E_EXT0, NO_E1. remove_emptiness.
        rewrite id_union. repeat rewrite id_union. expand_rels. 
        rewrite EINDEX2. 
        repeat rewrite EXTSB_IRR.
        rewrite EXTSB_MON with (e1 := (ThreadEvent tid (eindex st1 + 1))). 
        2: { simpl. omega. }
        rewrite EXTSB_MON with (e1 := (ThreadEvent tid (eindex st1 + 1 + 1))). 
        2: { simpl. omega. }
        rewrite EXTSB_MON with (e1 := (ThreadEvent tid (eindex st1 + 1 + 1))). 
        2: { simpl. omega. }
        remove_emptiness.
        repeat rewrite unique_restr.
        2-4: by (simpl; split; [auto | omega]).
        basic_solver. }
      right. rewrite E2_ADD, E1_ADD.
      replace (eindex st2 - 1) with (eindex st1); auto. omega. }
    Qed.
      
  Lemma singl_rel_restr {A: Type} (x y: A):
    singl_rel x y ≡ ⦗eq x⦘ ⨾ singl_rel x y ⨾ ⦗eq y⦘. 
  Proof. ins. basic_solver. Qed. 

  Lemma rel_endpoints_dom {A: Type} (D C EL ER : A -> Prop) r (DOM: r ≡ ⦗D⦘ ⨾ r ⨾ ⦗C⦘):
    ⦗EL⦘ ⨾ r ⨾ ⦗ER⦘ ≡ ⦗EL ∩₁ D⦘ ⨾ r ⨾ ⦗ER ∩₁ C⦘.
  Proof.
    rewrite set_interC with (s' := C). 
    do 2 rewrite id_inter. rewrite !seqA.
    seq_rewrite <- DOM. basic_solver.
  Qed.

  Lemma compilation_injective PO1 PO2 BPI (COMP1: is_thread_block_compiled PO1 BPI) (COMP2: is_thread_block_compiled PO2 BPI):
    PO1 = PO2.
  Proof. Admitted. 

  Lemma GI_1thread_omm_premises_block bst tid PO 
        (COMP: is_thread_block_compiled PO (binstrs bst)) 
        (BLOCK_STEPS: (omm_block_step tid)＊ (binit (binstrs bst)) bst):
    omm_premises_hold (bG bst).
  Proof.
    apply crt_num_steps in BLOCK_STEPS. destruct BLOCK_STEPS as [n_steps BLOCK_STEPS].
    generalize dependent bst. induction n_steps.
    { ins. red in BLOCK_STEPS. desc. rewrite <- BLOCK_STEPS. simpl.
      red. simpl. splits; basic_solver. }
    ins. red in BLOCK_STEPS. destruct BLOCK_STEPS as [bst_prev [STEPS_PREV STEP_NEXT]].
    assert (binstrs bst = binstrs bst_prev) as BINSTRS_SAME.
    { red in STEP_NEXT. desc. auto. }
    specialize (IHn_steps bst_prev).
    specialize_full IHn_steps; [congruence| congruence |]. 
    red in STEP_NEXT. desc. 
    assert (PO0 = PO); [| subst PO0]. 
    { eapply compilation_injective; eauto. congruence. }
    red in BLOCK_STEP. desc.
    remember (bpc bst_prev) as b. remember (bst2st bst_prev) as st_prev.
    assert (exists oinstr, is_instruction_compiled oinstr block) as [oinstr COMP_BLOCK].
    { eapply resulting_block_compiled; eauto. eapply COMPILED_NONEMPTY. eauto. }
    assert (forall i block_i, Some block_i = nth_error block i -> Some block_i = nth_error (instrs st_prev) (pc st_prev + i)) as BLOCK_CONTENTS. 
    { ins. forward eapply (@near_pc block_i block i H bst_prev); eauto.
      { congruence. }
      apply nth_error_Some, OPT_VAL. exists block. congruence. }
    assert (forall i instr (BLOCK_I: Some instr = nth_error block i) instr' (OTHER: Some instr' = nth_error (instrs st_prev) (pc st_prev + i)) (NEQ: instr <> instr'), False).
    { ins. specialize (BLOCK_CONTENTS _ _ BLOCK_I). congruence. }
    assert (exists k, (step tid) ^^ k (init (instrs st_prev)) st_prev) as [k REACH].
    { apply crt_num_steps. subst st_prev. apply ommblocks_imply_steps.
      apply crt_num_steps. eexists. rewrite BINSTRS_SAME0. eauto. }
    assert (forall st', (step tid) st_prev st' -> (step tid) ^^ (k + 1) (init (instrs st')) st') as REACH'. 
    { ins. replace (instrs st') with (instrs st_prev).
      2: { apply steps_same_instrs. eexists. apply rt_step. basic_solver. }
      rewrite Nat.add_1_r. apply step_prev. eexists. splits; eauto. }   
    assert (wf_thread_state tid st_prev) as WFT.
    { apply wf_thread_state_steps with (s := init (instrs st_prev)); [apply wf_thread_state_init| ]. 
      apply crt_num_steps. eauto. }
    (* assert (forall G, W G ∩₁ ORlx G ≡₁ fun x : actid => is_orlx_w (lab G) x) as ORLX_W_ALT.  *)
    (* { unfold set_inter, is_orlx_w. basic_solver. } *)
    assert (forall {A: Type} (D: A -> Prop) r, immediate (restr_rel D r) ≡ restr_rel D (immediate (restr_rel D r))) as RESTR_IMM. 
    { ins. basic_solver. }

    inv COMP_BLOCK; simpl in *.
    all: remember (bst2st bst_prev) as st_prev.
    { apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP0.
      do 2 (red in BLOCK_STEP0; desc).
      forward eapply (BLOCK_CONTENTS 0 ld) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 ld eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      assert (instr = ld). 
      { cut (Some instr = Some ld); [ins; vauto| ].
        rewrite ISTEP, INSTR. rewrite Nat.add_0_r.
        vauto. }
      subst instr. inversion H0. subst ord. subst reg. subst lexpr. 
      remember (Aload false Orlx (RegFile.eval_lexpr (regf st_prev) loc) val) as lbl. 
      remember (bst2st bst) as st.
      replace (init (flatten (binstrs bst_prev))) with (init (instrs st_prev)) in * by vauto. 
      red.
      replace (bG bst) with (G st) by vauto.
      forward eapply step_1_label_ext_helper as LBL_EXT; eauto.
      { red. splits; eauto. red. eexists. red. splits; eauto. }
      simpl in LBL_EXT. desc. 
      assert (forall max_event index (IND: index >= eindex st_prev),
                 singl_rel max_event (ThreadEvent tid (eindex st_prev)) ⨾ rmw (G st_prev) ≡ ∅₂) as SB_RMW_HELPER. 
      { split; [| basic_solver].
        rewrite rmw_bibounded; vauto. 
        red. ins. red in H1. desc. red in H1. desc. subst.
        simpl in H2. omega. }
      subst lbl. simpl in *.
      des.
      { assert (sb (G st) ≡ ∅₂) as NO_SB.
        { split; [| basic_solver]. unfold Execution.sb.
          rewrite E_EXT, SB_EXT. remove_emptiness.
          rewrite seq_eqv_lr. red. ins. desc.
          subst. unfold ext_sb in H2. desc. omega. }
        assert (immediate (sb (G st)) ≡ ∅₂) as NO_ISB.
        { generalize NO_SB. basic_solver. }
        rewrite SB_EXT in *. clear SB_EXT. 
        splits.
        all: unfold_clear_updated st; expand_rels; simplify_updated_sets.
        2: by_IH IHn_steps. 
        all: basic_solver. }
      splits.
      { unfold_clear_updated st. expand_rels. simplify_updated_sets.
        rewrite SB_RMW_HELPER; eauto. remove_emptiness.
        by_IH IHn_steps. }
      { unfold_clear_updated st. expand_rels. simplify_updated_sets.
        by_IH IHn_steps. }
      { unfold_clear_updated st. expand_rels. simplify_updated_sets.
        rewrite codom_union. apply set_subset_union_r. left. 
        by_IH IHn_steps. }
      { unfold_clear_updated st. expand_rels. simplify_updated_sets.
        rewrite codom_union. apply set_subset_union_r. left.
        by_IH IHn_steps. } }
    { apply (same_relation_exp (@seqA _ _ _ _)) in BLOCK_STEP0.
      apply (same_relation_exp (seq_id_l (step tid ⨾ step tid))) in BLOCK_STEP0.
      red in BLOCK_STEP0. destruct BLOCK_STEP0 as [st_prev' [STEP1 STEP2]]. 
      do 2 (red in STEP1; desc). do 2 (red in STEP2; desc).
      forward eapply (BLOCK_CONTENTS 0 f) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 f eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      assert (instr = f). 
      { cut (Some instr = Some f); [ins; vauto| ].
        rewrite ISTEP, INSTR. rewrite Nat.add_0_r.
        vauto. }
      rewrite <- INSTRS, UPC in *.      
      subst instr. inversion H0. subst ord. (* subst reg. subst lexpr.  *)
      forward eapply (BLOCK_CONTENTS 1 st) as INSTR'; eauto.
      inversion ISTEP2.
      all: try (forward eapply (@H 1 st eq_refl instr0); by vauto).
      assert (instr0 = st). 
      { cut (Some instr0 = Some st); [ins; vauto| ].
        rewrite ISTEP1. vauto. }
      subst instr0. inversion H1. subst ord. subst lexpr. subst expr.
      subst x. subst l. subst v.  
      
      remember (Afence Oacqrel) as lbl. 
      remember (Astore Xpln Orlx (RegFile.eval_lexpr (regf st_prev') loc)) as lbl'.
      rename st into st_.
      remember (bst2st bst) as st.
      replace (init (flatten (binstrs bst_prev))) with (init (instrs st_prev)) in * by vauto. 
      red.
      replace (bG bst) with (G st) by vauto.
      forward eapply (@step_11_label_ext_helper st_prev st_prev' st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      { red. splits; eauto. red. eexists. red. splits.
        { congruence. }
        exists st_. splits; eauto. rewrite INSTR'. f_equal; vauto. } 

      rewrite Heqlbl, Heqlbl' in LBL_EXT. simpl in LBL_EXT. desc. 
      remember (ThreadEvent tid (eindex st_prev)) as ev.
      remember (ThreadEvent tid (eindex st_prev')) as ev'. 
      destruct SB_EXT as [[NO_E SB_TRIVIAL] | SB_EXT]. 
      { assert (immediate (sb (G st)) ≡ singl_rel ev ev') as IMM_SB. 
        { rewrite SB_TRIVIAL. split; [basic_solver| ].
          red. ins. red. split; auto.
          ins. red in H2, R1, R2. desc. subst.
          inversion R2. rewrite UINDEX in H3. simpl in H3. omega. }
        rewrite NO_E in *. (* clear NO_E. *)
        subst ev ev'. rewrite UINDEX in *. 
        splits. all: try rewrite IMM_SB.
        { rewrite E_EXT, RMW_EXT. 
          rewrite wft_rmwE; eauto. fold (acts_set (G st_prev)). rewrite NO_E.
          unfold_clear_updated st; expand_rels; simplify_updated_sets.          
          basic_solver 10. }
        { unfold_clear_updated st; expand_rels; simplify_updated_sets.
          by_IH IHn_steps. }
        { unfold_clear_updated st; expand_rels; simplify_updated_sets.
          basic_solver 10. }
        { unfold_clear_updated st; expand_rels; simplify_updated_sets.
          basic_solver. }
      } 
      
      splits.
      { subst ev ev'. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        assert (forall x d, singl_rel x (ThreadEvent tid (eindex st_prev + d)) ⨾ rmw (G st_prev) ≡ ∅₂).
        { ins. rewrite wft_rmwE; eauto. fold (acts_set (G st_prev)).
          rewrite singl_rel_restr. rewrite !seqA. rewrite <- seqA with (r2 := ⦗E (G st_prev)⦘).
          rewrite <- id_inter. simplify_updated_sets. basic_solver. }
        rewrite <- Nat.add_0_r with (n := (eindex st_prev)) at 4. 
        repeat rewrite H2. remove_emptiness.
        rewrite id_union. expand_rels.
        unfold sb at 2. rewrite <- restr_relE, RESTR_IMM, restr_relE.
        rewrite !seqA. rewrite <- seqA with (r1 := ⦗eq (ThreadEvent tid (eindex st_prev))⦘).
        rewrite <- id_inter. simplify_updated_sets.
        by_IH IHn_steps. }
      { unfold_clear_updated st; expand_rels; simplify_updated_sets.
        by_IH IHn_steps. }
      { subst ev ev'. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        apply set_subset_union_l. split; [| basic_solver 10]. 
        rewrite id_union. expand_rels.
        repeat rewrite codom_union. 
        repeat (apply set_subset_union_r; left).
        by_IH IHn_steps. }
      { subst ev ev'. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite id_union. expand_rels.
        repeat rewrite codom_union. 
        repeat (apply set_subset_union_r; left).
        by_IH IHn_steps. } }
    { apply (same_relation_exp (@seqA _ _ _ _)) in BLOCK_STEP0.
      apply (same_relation_exp (seq_id_l (step tid ⨾ step tid))) in BLOCK_STEP0.
      red in BLOCK_STEP0. destruct BLOCK_STEP0 as [st_prev' [STEP1 STEP2]]. 
      do 2 (red in STEP1; desc). do 2 (red in STEP2; desc).
      forward eapply (BLOCK_CONTENTS 0 f) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 f eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      assert (instr = f). 
      { cut (Some instr = Some f); [ins; vauto| ].
        rewrite ISTEP, INSTR. rewrite Nat.add_0_r.
        vauto. }
      rewrite <- INSTRS, UPC in *.      
      subst instr. inversion H0. subst ord. (* subst reg. subst lexpr.  *)
      forward eapply (BLOCK_CONTENTS 1 ld) as INSTR'; eauto.
      inversion ISTEP2.
      all: try (forward eapply (@H 1 ld eq_refl instr0); by vauto).
      assert (instr0 = ld). 
      { cut (Some instr0 = Some ld); [ins; vauto| ].
        rewrite ISTEP1. vauto. }
      subst instr0. inversion H1. subst ord. subst lexpr. subst reg.
      (* subst x. *)
      subst l.
      (* subst val.   *)
      
      remember (Afence Oacq) as lbl. 
      remember (Aload false Osc (RegFile.eval_lexpr (regf st_prev') loc) val) as lbl'.
      remember (bst2st bst) as st.
      replace (init (flatten (binstrs bst_prev))) with (init (instrs st_prev)) in * by vauto. 
      red.
      replace (bG bst) with (G st) by vauto.
      forward eapply (@step_11_label_ext_helper st_prev st_prev' st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      { red. splits; eauto. red. eexists. red. splits.
        { congruence. }
        exists ld. splits; eauto. rewrite INSTR'. f_equal; vauto. } 

      rewrite Heqlbl, Heqlbl' in LBL_EXT. simpl in LBL_EXT. desc. 
      remember (ThreadEvent tid (eindex st_prev)) as ev.
      remember (ThreadEvent tid (eindex st_prev')) as ev'. 
      destruct SB_EXT as [[NO_E SB_TRIVIAL] | SB_EXT]. 
      { assert (immediate (sb (G st)) ≡ singl_rel ev ev') as IMM_SB. 
        { rewrite SB_TRIVIAL. split; [basic_solver| ].
          red. ins. red. split; auto.
          ins. red in H2, R1, R2. desc. subst.
          inversion R2. rewrite UINDEX in H3. simpl in H3. omega. }
        rewrite NO_E in *. (* clear NO_E. *)
        subst ev ev'. rewrite UINDEX in *. 
        splits. all: try rewrite IMM_SB.
        { rewrite E_EXT, RMW_EXT. 
          rewrite wft_rmwE; eauto. fold (acts_set (G st_prev)). rewrite NO_E.
          unfold_clear_updated st; expand_rels; simplify_updated_sets.          
          basic_solver 10. }
        { unfold_clear_updated st; expand_rels; simplify_updated_sets.
          rewrite wft_rmwE at 2; eauto. fold (acts_set (G st_prev)).
          rewrite !seqA. repeat seq_rewrite <- id_inter.
          unfold_clear_updated st; expand_rels; simplify_updated_sets.
          repeat rewrite id_inter. rewrite !seqA.
          unfold acts_set. seq_rewrite <- wft_rmwE; eauto. 
          by_IH IHn_steps. }
        { unfold_clear_updated st; expand_rels; simplify_updated_sets.
          basic_solver 10. }
        { unfold_clear_updated st; expand_rels; simplify_updated_sets.
          basic_solver 10. }
      } 
      
      splits.
      { subst ev ev'. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite set_interA with (s'' := eq (ThreadEvent tid (eindex st_prev + 1))). simplify_updated_sets. 
        rewrite singl_rel_restr. rewrite singl_rel_restr with (y := (ThreadEvent tid (eindex st_prev + 1))). 
        rewrite wft_rmwE; eauto. fold (acts_set (G st_prev)).
        rewrite !seqA. repeat seq_rewrite <- id_inter.
        simplify_updated_sets.
        repeat rewrite eqv_empty. remove_emptiness.
        rewrite id_union, seq_union_l.
        (* TODO: refactor with previous case; also maybe add tactic especially for rmw; add id_inter folding into simplification *)
        arewrite (⦗eq (ThreadEvent tid (eindex st_prev))⦘
                    ⨾ immediate (sb (G st_prev)) ≡ ∅₂).
        { unfold sb. rewrite <- restr_relE, RESTR_IMM, restr_relE.
          seq_rewrite <- id_inter. simplify_updated_sets. basic_solver. }
        remove_emptiness. unfold acts_set. rewrite <- wft_rmwE; eauto.
        by_IH IHn_steps. }
      { unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite wft_rmwE at 2; eauto. fold (acts_set (G st_prev)).
        rewrite !seqA. repeat seq_rewrite <- id_inter.
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        subst ev ev'. simplify_updated_sets. repeat rewrite id_inter.
        rewrite !seqA.
        unfold acts_set. seq_rewrite <- wft_rmwE; eauto. 
        by_IH IHn_steps. }
      { subst ev ev'. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite unionA, codom_union. apply set_subset_union_r. left.
        by_IH IHn_steps. }
      { subst ev ev'. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite set_interA with (s'' := eq (ThreadEvent tid (eindex st_prev + 1))). simplify_updated_sets. 
        rewrite id_union. apply set_subset_union_l. split.
        { expand_rels.
          repeat rewrite codom_union. 
          repeat (apply set_subset_union_r; left).
          by_IH IHn_steps. }
        repeat rewrite codom_union. 
        repeat (apply set_subset_union_r; right).
        basic_solver 10. }
    }
    { apply (same_relation_exp (@seqA _ _ _ _)) in BLOCK_STEP0.
      apply (same_relation_exp (seq_id_l (step tid ⨾ step tid))) in BLOCK_STEP0.
      red in BLOCK_STEP0. destruct BLOCK_STEP0 as [st_prev' [STEP1 STEP2]]. 
      do 2 (red in STEP1; desc). do 2 (red in STEP2; desc).
      forward eapply (BLOCK_CONTENTS 0 f) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 f eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      assert (instr = f). 
      { cut (Some instr = Some f); [ins; vauto| ].
        rewrite ISTEP, INSTR. rewrite Nat.add_0_r.
        vauto. }
      rewrite <- INSTRS, UPC in *.      
      subst instr. inversion H0. subst ord. (* subst reg. subst lexpr.  *)
      forward eapply (BLOCK_CONTENTS 1 exc) as INSTR'; eauto.
      inversion ISTEP2.
      all: try (forward eapply (@H 1 exc eq_refl instr0); by vauto).
      assert (instr0 = exc). 
      { cut (Some instr0 = Some exc); [ins; vauto| ].
        rewrite ISTEP1. vauto. }
      subst instr0. inversion H1. subst new_expr xmod ordr ordw reg loc_expr loc0.
      remember (Afence Oacq) as lbl. 
      remember (Aload true Osc (RegFile.eval_lexpr (regf st_prev') loc) old_value) as lbl'.
      remember (Astore Xpln Osc (RegFile.eval_lexpr (regf st_prev') loc) new_value) as lbl''. 
      rename st into st_. remember (bst2st bst) as st.
      replace (init (flatten (binstrs bst_prev))) with (init (instrs st_prev)) in * by vauto. 
      red.
      replace (bG bst) with (G st) by vauto.
      forward eapply (@step_12_label_ext_helper st_prev st_prev' st) as LBL_EXT; eauto.
      { red. splits; eauto. do 2 (red; eexists); eauto. } 
      { red. splits; eauto. red. eexists. red. splits.
        { congruence. }
        exists exc. splits; eauto. rewrite INSTR'. f_equal; vauto. } 
      rewrite Heqlbl, Heqlbl', Heqlbl'' in LBL_EXT. simpl in LBL_EXT. desc. 
      remember (ThreadEvent tid (eindex st_prev)) as ev.
      remember (ThreadEvent tid (eindex st_prev')) as ev'. 
      remember (ThreadEvent tid (eindex st_prev' + 1)) as ev''.
      assert (wf_thread_state tid st_prev') as WFT'.
      { eapply wf_thread_state_step; eauto. red. eexists. red. splits; eauto. }
      assert (wf_thread_state tid st) as WFT''.
      { eapply wf_thread_state_step; eauto. red. eexists. red.
        splits; [congruence| ]. exists exc. splits; eauto. congruence. }
      
      destruct SB_EXT as [[NO_E SB_TRIVIAL] | SB_EXT]. 
      { assert (immediate (sb (G st)) ≡ singl_rel ev ev' ∪ singl_rel ev' ev'') as IMM_SB. 
        { rewrite immediate_sb_repr; eauto.
          rewrite UINDEX0, UINDEX. 
          assert (eindex st_prev = 0) as EINDEX0.
          { destruct (gt_0_eq (eindex st_prev)); auto.
            exfalso. destruct WFT. forward eapply (@acts_clos 0); [omega| ].
            generalize NO_E. unfold acts_set. basic_solver 100. }
          rewrite EINDEX0. 
          split.
          { red. ins. desc. subst ev ev' ev'' x y. rewrite UINDEX.
            destruct ind.
            { red. left. rewrite EINDEX0. red. split; f_equal; omega.  }
            assert (ind = 0); [by omega| subst ind].
            red. right. rewrite EINDEX0. red. split; f_equal; omega. }
          red. ins. red in H2. des.
          { subst ev ev'. red in H2. desc. subst. eexists. splits; eauto. omega. }
          { subst ev ev'. red in H2. desc. subst. eexists. splits; eauto. omega. }
        }
        rewrite NO_E in *. (* clear NO_E. *)
        (* subst ev ev' ev''. rewrite UINDEX in *.  *)
        splits. all: try rewrite IMM_SB.
        { subst ev ev' ev''. rewrite UINDEX in *. 
          rewrite E_EXT, RMW_EXT. 
          rewrite wft_rmwE; eauto. fold (acts_set (G st_prev)). rewrite NO_E.
          rewrite eqv_empty. remove_emptiness. 
          unfold_clear_updated st. expand_rels. simplify_updated_sets.          
          basic_solver 10. }
        { unfold_clear_updated st. remove_emptiness.
          rewrite set_unionA. expand_rels.
          arewrite (⦗Sc (G st_prev) ∪₁ (eq ev' ∪₁ eq ev'')⦘
                      ⨾ rmw (G st_prev) ⨾ ⦗Sc (G st_prev) ∪₁ (eq ev' ∪₁ eq ev'')⦘ ≡ rmw (G st_prev)).
          { rewrite rel_endpoints_dom.
            2: { eapply wft_rmwE; eauto. }
            fold (acts_set (G st_prev)).
            expand_sets_only. subst ev ev' ev''. simplify_updated_sets.
            rewrite set_interC at 2. rewrite !id_inter, !seqA.
            unfold acts_set. seq_rewrite <- wft_rmwE; eauto.
            symmetry. by_IH IHn_steps. }            
          apply union_more; [basic_solver| ].
          rewrite rel_endpoints_dom.
          2: { symmetry. eapply unique_restr. basic_solver. }
          expand_sets_only. subst ev ev' ev''. simplify_updated_sets.
          rewrite unique_restr; basic_solver. }
        { subst ev ev' ev''. rewrite UINDEX. 
          unfold_clear_updated st; expand_rels; simplify_updated_sets.
           basic_solver 10. }
        { subst ev ev' ev''. rewrite UINDEX.
          unfold_clear_updated st; expand_rels; simplify_updated_sets.
          basic_solver 10. }
      }
      assert (forall st_, immediate (sb (G st_)) ≡ ⦗E (G st_)⦘ ⨾ immediate (sb (G st_)) ⨾ ⦗E (G st_)⦘) as SB_IMM_E.
      { ins. unfold sb. rewrite <- restr_relE. rewrite RESTR_IMM.
        rewrite restr_relE. basic_solver 10. }
      (* assert (wf_thread_state tid st_prev') as WFT'. *)
      (* { eapply wf_thread_state_step; eauto. red. eexists. red. splits; eauto. } *)
      (* assert (wf_thread_state tid st) as WFT''. *)
      (* { eapply wf_thread_state_step; eauto. red. eexists. red. *)
      (*   splits; [congruence| ]. exists exc. splits; eauto. congruence. } *)
      splits.
      { subst ev ev' ev''. rewrite UINDEX in *.
        rewrite E_EXT, W_EXT, SC_EXT at 1. 
        remove_emptiness. expand_sets_only. simplify_updated_sets. Show. 
        repeat rewrite set_interA. simplify_updated_sets.
        rewrite RMW_EXT. expand_rels. rewrite codom_union.
        apply set_equiv_union.
        { rewrite SB_EXT. rewrite !seq_union_l.
          rewrite wft_rmwE; eauto. fold (acts_set (G st_prev)).
          rewrite singl_rel_restr. rewrite singl_rel_restr with (x := (ThreadEvent tid (eindex st_prev))). rewrite singl_rel_restr with (x := (ThreadEvent tid (eindex st_prev + 1))). 
          rewrite !seqA. repeat seq_rewrite <- id_inter. simplify_updated_sets.
          unfold acts_set. seq_rewrite <- wft_rmwE; eauto.
          rewrite SB_IMM_E. rewrite !seqA. seq_rewrite <- id_inter.
          unfold_clear_updated st. expand_sets_only. simplify_updated_sets.
          rewrite id_inter, seqA. seq_rewrite <- SB_IMM_E.
          rewrite <- set_interA. by_IH IHn_steps. }
        rewrite SB_EXT. expand_rels.
        rewrite singl_rel_restr with (x := (ThreadEvent tid (eindex st_prev - 1))). rewrite singl_rel_restr with (x := (ThreadEvent tid (eindex st_prev))). rewrite singl_rel_restr with (x := (ThreadEvent tid (eindex st_prev + 1))). 
        rewrite !seqA. repeat seq_rewrite <- id_inter. simplify_updated_sets.
        rewrite SB_IMM_E. rewrite !seqA. repeat seq_rewrite <- id_inter. simplify_updated_sets.
        rewrite <- singl_rel_restr.
        unfold_clear_updated st. expand_sets_only. simplify_updated_sets.
        basic_solver 10. }
      { unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite wft_rmwE at 2; eauto. fold (acts_set (G st_prev)).
        rewrite !seqA. repeat seq_rewrite <- id_inter.
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        subst ev ev' ev''. simplify_updated_sets. repeat rewrite id_inter.
        rewrite !seqA. unfold acts_set. seq_rewrite <- wft_rmwE; eauto.
        apply union_more; [by_IH IHn_steps| ].
        rewrite singl_rel_restr. rewrite !seqA. repeat seq_rewrite <- id_inter.
        rewrite UINDEX. expand_rels. simplify_updated_sets.
        basic_solver. }
      { subst ev ev' ev''. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite unionA.
        do 2 (rewrite codom_union; apply set_subset_union_r; left). 
        by_IH IHn_steps. }
      { subst ev ev' ev''. rewrite UINDEX in *. 
        unfold_clear_updated st; expand_rels; simplify_updated_sets.
        rewrite !set_interA. simplify_updated_sets.
        rewrite !unionA, codom_union. apply set_subset_union. 
        { rewrite id_union. expand_rels. rewrite codom_union.
          apply set_subset_union_r. left. rewrite <- set_interA. by_IH IHn_steps. }
        basic_solver 10. }
    }
    { apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP0.
      do 2 (red in BLOCK_STEP0; desc).
      forward eapply (BLOCK_CONTENTS 0 asn) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 asn eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      subst st_prev. simpl in *. congruence. }
    { apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP0.
      do 2 (red in BLOCK_STEP0; desc).
      forward eapply (BLOCK_CONTENTS 0 igt) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 igt eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      subst st_prev. simpl in *. congruence. }
  Qed. 

  Lemma GI_1thread_omm_premises tid PO PI (COMP: is_thread_compiled PO PI) Gi
        (EXEC: thread_execution tid PI Gi):
    omm_premises_hold Gi.
  Proof.
    red in EXEC. destruct EXEC as [st_fin [STEPS [TERM GRAPH]]]. 
    red in COMP. desc. red in COMP. desc.
    set (bst_fin := bst_from_st st_fin BPI (length BPI)).
    assert (st_fin = bst2st bst_fin) as BST.
    { replace PI with (instrs st_fin) in *.
      2: { apply eq_trans with (y := instrs (init PI)); auto.
           symmetry. apply steps_same_instrs. eauto. }
      unfold bst2st. simpl. rewrite firstn_all.
      red in TERM. apply is_terminal_pc_bounded in TERM. 
      rewrite <- COMP0 in *.
      rewrite <- TERM. apply state_record_equality. }
    forward eapply (@steps_imply_ommblocks bst_fin) as BLOCK_STEPS; eauto.
    { simpl. rewrite <- COMP0, <- BST. eauto. }
    replace Gi with (bG bst_fin).
    eapply GI_1thread_omm_premises_block; eauto. 
  Qed. 

End CompCorrHelpers.