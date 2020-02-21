Require Import Classical Peano_dec.
From hahn Require Import Hahn.
Require Import Omega.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import ClosuresProperties. 
Require Import OCamlToimm_s_prog_compilation.
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import Logic.Decidable. 
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.


Section BoundedProperties.
  Definition is_nonnop_f {A: Type} (labfun: A -> label) ev :=
    andb (is_f labfun ev) (is_ra labfun ev). 
  
  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  Notation "'F' G" := (fun a => is_true (is_nonnop_f G.(lab) a)) (at level 1).
  Notation "'ORlx' G" := (fun a => is_true (is_only_rlx G.(lab) a)) (at level 1).
  Notation "'Sc' G" := (fun a => is_true (is_sc G.(lab) a)) (at level 1). 
  Notation "'Acq' G" := (fun a => is_true (is_acq G.(lab) a)) (at level 1). 
  Notation "'Acqrel' G" := (fun a => is_true (is_acqrel G.(lab) a)) (at level 1). 
  Notation "'R_ex' G" := (fun a => is_true (R_ex G.(lab) a)) (at level 1).
  Notation "'same_loc' G" := (same_loc G.(lab)) (at level 1).
  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).

  Definition processes_lab (f: (actid -> label) -> actid -> bool) (lbl_matcher: label -> bool) :=
    forall labfun ev, f labfun ev = lbl_matcher (labfun ev).

  Definition w_matcher := (fun lbl => match lbl with | Astore _ _ _ _ => true | _ => false end).
  Lemma w_pl: processes_lab (@is_w actid) w_matcher. 
  Proof.
    red. 
    intros. unfold is_w. auto.
  Qed. 

  Definition r_matcher := (fun lbl => match lbl with | Aload _ _ _ _ => true | _ => false end).
  Lemma r_pl: processes_lab (@is_r actid) r_matcher. 
  Proof. red. intros. unfold is_r. auto. Qed. 

  Definition sc_matcher :=
    (fun lbl => match lbl with
             | Astore _ Osc _ _ => true
             | Aload _ Osc _ _ => true
             | Afence Osc => true
             | _ => false
             end).
  Lemma sc_pl: processes_lab (@is_sc actid) sc_matcher. 
  Proof.
    red. intros. unfold is_sc, Events.mod.
    destruct (labfun ev); auto. 
  Qed. 
  
  Definition nonnop_f_matcher :=
    (fun lbl => match lbl with
             | Afence mode => orb (mode_le Oacq mode) (mode_le Orel mode)
             | _ => false
             end).
  Lemma nonnop_f_pl: processes_lab (@is_nonnop_f actid) nonnop_f_matcher. 
  Proof.
    red. intros. unfold is_nonnop_f, nonnop_f_matcher, is_f. 
    destruct (labfun ev) eqn:eq; auto.
    unfold is_ra, is_acq, is_rel, Events.mod. rewrite eq. auto.
  Qed. 
  
  Definition acq_matcher :=
    (fun lbl => let mode := (match lbl with
                          | Astore _ mode _ _ => mode
                          | Aload _ mode _ _ => mode
                          | Afence mode => mode
                          end)
             in mode_le Oacq mode).
  Lemma acq_pl: processes_lab (@is_acq actid) acq_matcher. 
  Proof.
    red. intros. unfold is_acq, acq_matcher, Events.mod. auto. 
  Qed. 
    
  Definition acqrel_matcher :=
    (fun lbl => let mode := (match lbl with
                          | Astore _ mode _ _ => mode
                          | Aload _ mode _ _ => mode
                          | Afence mode => mode
                          end)
             in mode_le Oacqrel mode).
  Lemma acqrel_pl: processes_lab (@is_acqrel actid) acqrel_matcher. 
  Proof.
    red. intros. unfold is_acqrel, acqrel_matcher, Events.mod. auto. 
  Qed.
  
  Definition orlx_matcher :=
    (fun lbl => let mode := (match lbl with
                          | Astore _ mode _ _ => mode
                          | Aload _ mode _ _ => mode
                          | Afence mode => mode
                          end)
             in match mode with | Orlx => true | _ => false end).
  Lemma orlx_pl: processes_lab (@is_only_rlx actid) orlx_matcher. 
  Proof.
    red. intros. unfold is_only_rlx, orlx_matcher, Events.mod. auto. 
  Qed. 
    
  Definition index_bounded ev_set st :=
    ev_set (lab (G st)) ⊆₁ (fun e => index e < eindex st).

  Definition non_nop S := S (Afence Orlx) = false. 

  Lemma nonnop_bounded n: forall S matcher st tid
                            (MATCH: processes_lab S matcher)
                            (NON_NOP: non_nop matcher)
                            (STEPS: (step tid) ^^ n (init (instrs st)) st),
      index_bounded S st. 
  Proof. 
    intros. red. generalize dependent st.
    red in NON_NOP. red in MATCH.
    induction n.
    { intros. apply steps0 in STEPS. rewrite <- STEPS.
      simpl. red. intros. 
      specialize (MATCH (fun _ : actid => Afence Orlx) x).
      vauto. }
    red. intros st STEPS x Sx.
    rewrite step_prev in STEPS. destruct STEPS as [st' [STEPS' STEP]].
    replace (instrs st) with (instrs st') in STEPS'.
    2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
    specialize (IHn st' STEPS').
    do 2 (red in STEP; desc).
    red in IHn. specialize (IHn x).
    remember (ThreadEvent tid (eindex st')) as ev.
    inversion ISTEP0.
    - rewrite UG in Sx. rewrite UINDEX. apply IHn. auto.
    - rewrite UG in Sx. rewrite UINDEX. apply IHn. auto.
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx. rewrite updo in Sx; [| congruence].
        forward eapply IHn;[ | omega].
        rewrite MATCH; auto. 
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx. rewrite updo in Sx; [| congruence].
        forward eapply IHn; [auto | omega].
        rewrite MATCH; auto. 
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx. rewrite updo in Sx; [| congruence].
        forward eapply IHn; [auto | omega].
        rewrite MATCH; auto. 
    - (* show there are no CAS instructions in compiled program *)
      admit.
    - (* show there are no CAS instructions in compiled program *)
      admit.
    - (* show there are no FADD instructions in compiled program *)
      admit.
    - (* TODO *)
      admit.
  Admitted. 

  Lemma label_set_step (S: (actid -> label) -> actid -> bool) matcher st1 st2 tid new_label
        (ADD: exists foo bar baz bazz,
            G st2 = add (G st1) tid (eindex st1) new_label foo bar baz bazz)
        (MATCH: processes_lab S matcher)
        (BOUND: index_bounded S st1):
    S (lab (G st2)) ≡₁ S (lab (G st1))
      ∪₁ (if matcher new_label then eq (ThreadEvent tid (eindex st1)) else ∅). 
  Proof.
    assert (SAME_SET_ELT: forall (A : Type) (s s' : A -> Prop),
               s ≡₁ s' <-> (forall x : A, s x <-> s' x)).
    { intros. red. split; [apply set_equiv_exp| ].
      intros. red. split.
      all: red; intros.
      all: specialize (H x).
      all: apply H; auto. }
    apply SAME_SET_ELT. unfold set_union. intros.
    red in MATCH. rewrite !MATCH.
    desc. subst. simpl. 
    remember (ThreadEvent tid (eindex st1)) as ev.
    rewrite ADD. simpl. 
    destruct (classic (x = ev)).
    { rewrite H, <- Heqev. rewrite upds.
      destruct (matcher new_label); auto.
      unfold set_empty. 
      cut (matcher (lab (G st1) ev) = false). 
      { intros. rewrite H0. intuition. }
      (* require boundness of a function and restrict ev to be new event*)
      do 2 red in BOUND. specialize (BOUND ev).
      rewrite MATCH in BOUND.
      apply Bool.not_true_is_false. red. intros CONTRA. 
      apply BOUND in CONTRA. vauto. simpl in CONTRA. omega. }
    rewrite updo; auto. split; auto.
    intros. des; auto. 
    destruct (matcher new_label); vauto.
    congruence. 
  Qed. 
    
  Lemma E_bounded n tid: forall st (STEPS: (step tid) ^^ n (init (instrs st)) st),
      E (G st) ⊆₁ (fun x => index x < eindex st).
  Proof.
    induction n.
    { intros. apply steps0 in STEPS. rewrite <- STEPS. simpl. basic_solver. }
    intros.
    rewrite step_prev in STEPS. destruct STEPS as [st' [STEPS' STEP]].
    replace (instrs st) with (instrs st') in STEPS'.
    2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
    specialize (IHn st' STEPS').
    do 2 (red in STEP; desc).
    inversion ISTEP0.
    - rewrite UG, UINDEX. auto.
    - rewrite UG, UINDEX. auto.
    - rewrite UG, UINDEX. unfold add, acts_set. simpl.
      red. intros ev H. destruct H.
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
    - rewrite UG, UINDEX. unfold add, acts_set. simpl.
      red. intros ev H. destruct H.
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
    - rewrite UG, UINDEX. unfold add, acts_set. simpl.
      red. intros ev H. destruct H.
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
    - rewrite UG, UINDEX. unfold add, acts_set. simpl.
      red. intros ev H. destruct H.
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
    - rewrite UG, UINDEX. unfold add_rmw, add, acts_set. simpl.
      red. intros ev H. des.
      { subst. simpl. omega. }
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
    - rewrite UG, UINDEX. unfold add_rmw, add, acts_set. simpl.
      red. intros ev H. des.
      { subst. simpl. omega. }
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
    - rewrite UG, UINDEX. unfold add_rmw, add, acts_set. simpl.
      red. intros ev H. des.
      { subst. simpl. omega. }
      { subst. simpl. omega. }
      red in IHn. specialize (IHn ev H). omega.
  Qed. 
  
  Definition sb_bibounded n tid: forall st (STEPS: (step tid) ^^ n (init (instrs st)) st),
    sb (G st) ⊆ (fun x y => index x < eindex st /\ index y < eindex st). 
  Proof. 
    induction n.
    { intros. apply steps0 in STEPS.
      rewrite <- STEPS. simpl. unfold init_execution, sb, acts_set. simpl.
      basic_solver. }
    intros.
    pose proof STEPS as STEPS_. 
    rewrite step_prev in STEPS. destruct STEPS as [st' [STEPS' STEP]].
    replace (instrs st) with (instrs st') in STEPS'.
    2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
    specialize (IHn st' STEPS').
    do 2 (red in STEP; desc).
    unfold sb. seq_rewrite (E_bounded); eauto. 
    inversion ISTEP0; (rewrite UINDEX; basic_solver). 
  Qed. 
    
  Definition rmw_bibounded n tid: forall st (STEPS: (step tid) ^^ n (init (instrs st)) st),
    rmw (G st) ⊆ (fun x y => index x < eindex st /\ index y < eindex st). 
  Proof. 
    induction n.
    { intros. apply steps0 in STEPS.
      rewrite <- STEPS. simpl. unfold init_execution, sb, acts_set. simpl.
      basic_solver. }
    intros.
    pose proof STEPS as STEPS_. 
    rewrite step_prev in STEPS. destruct STEPS as [st' [STEPS' STEP]].
    replace (instrs st) with (instrs st') in STEPS'.
    2: { apply steps_same_instrs. exists tid. apply rt_step. auto. }
    specialize (IHn st' STEPS').
    do 2 (red in STEP; desc).
    inversion ISTEP0.
    - rewrite UG, UINDEX. auto. 
    - rewrite UG, UINDEX. auto. 
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. desc. omega. 
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. desc. omega.
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. desc. omega.
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. desc. omega.
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. red in H. des; [| omega]. 
      red in H. desc. subst. simpl. omega.
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. red in H. des; [| omega]. 
      red in H. desc. subst. simpl. omega.
    - rewrite UG, UINDEX. unfold add. simpl. sin_rewrite IHn.
      red. intros. red in H. des; [| omega]. 
      red in H. desc. subst. simpl. omega.
  Qed.

  Lemma label_set_step_helper st1 st2 n tid new_label foo bar baz bazz
        (ADD: G st2 = add (G st1) tid (eindex st1) new_label foo bar baz bazz)
        (STEPS: (step tid) ^^ n (init (instrs st1)) st1):
    forall (S : (actid -> label) -> actid -> bool) (matcher : label -> bool)
      (MATCH: processes_lab S matcher)
      (NONNOP: non_nop matcher),
    S (lab (G st2)) ≡₁ S (lab (G st1))
      ∪₁ (if matcher new_label then eq (ThreadEvent tid (eindex st1)) else ∅).
  Proof.
    intros. 
    apply label_set_step; eauto.
    eapply nonnop_bounded; eauto. 
  Qed.

  Lemma E_ADD G G' tid index (ADD: exists lbl foo bar baz bazz,
                                 G' = add G tid index lbl foo bar baz bazz):
    E G' ≡₁ E G ∪₁ eq (ThreadEvent tid index).
  Proof. 
    desc. subst G'. unfold add, acts_set. simpl.
    basic_solver. 
  Qed.

  Lemma E_ADD_RMW G G' tid index
        (ADD: exists lblr lblw foo bar baz bazz, G' = add_rmw G tid index lblr lblw foo bar baz bazz):
    E G' ≡₁ E G ∪₁ eq (ThreadEvent tid index) ∪₁ eq (ThreadEvent tid (index + 1)).
  Proof. 
    desc. subst G'. unfold add_rmw, acts_set. simpl.
    basic_solver. 
  Qed.
  

End BoundedProperties.
