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
Require Import Utils. 
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.


Section BoundedProperties.
  
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
    
  Definition orlx_w_matcher :=
    fun lbl => match lbl with
            | Astore _ Orlx _ _ => true
            | _ => false
            end.
  Definition is_orlx_w := fun {A: Type} (labfun: A -> label) ev =>
                           is_w labfun ev && is_only_rlx labfun ev. 
             
  Lemma orlx_w_pl: processes_lab (@is_orlx_w actid) orlx_w_matcher. 
  Proof.
    red. intros. unfold is_orlx_w, is_only_rlx, is_w, orlx_w_matcher, Events.mod.
    type_solver. 
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
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx. rewrite updo in Sx; [| congruence].
        forward eapply IHn; [auto | omega].
        rewrite MATCH; auto.
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx.
        remember (ThreadEvent tid (eindex st' + 1)) as ev'. 
        destruct (classic (x = ev')).
        * rewrite H0, Heqev'. simpl. omega.
        * do 2 (rewrite updo in Sx; [| congruence]).
          forward eapply IHn; [auto | omega].
          rewrite MATCH; auto.
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx.
        remember (ThreadEvent tid (eindex st' + 1)) as ev'. 
        destruct (classic (x = ev')).
        * rewrite H0, Heqev'. simpl. omega.
        * do 2 (rewrite updo in Sx; [| congruence]).
          forward eapply IHn; [auto | omega].
          rewrite MATCH; auto.
    - rewrite UG in Sx. simpl in Sx. rewrite UINDEX.
      destruct (classic (x = ev)).
      + rewrite H, Heqev. simpl. omega.
      + rewrite MATCH in Sx.
        remember (ThreadEvent tid (eindex st' + 1)) as ev'. 
        destruct (classic (x = ev')).
        * rewrite H0, Heqev'. simpl. omega.
        * do 2 (rewrite updo in Sx; [| congruence]).
          forward eapply IHn; [auto | omega].
          rewrite MATCH; auto.
  Qed.
  
  Lemma label_set_step (S: (actid -> label) -> actid -> bool) matcher st1 st2 tid new_label
        index (NEW_INDEX: index >= eindex st1)
        (ADD: exists foo bar baz bazz,
            G st2 = add (G st1) tid index new_label foo bar baz bazz)
        (MATCH: processes_lab S matcher)
        (BOUND: index_bounded S st1):
    S (lab (G st2)) ≡₁ S (lab (G st1))
      ∪₁ (if matcher new_label then eq (ThreadEvent tid index) else ∅). 
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
    remember (ThreadEvent tid index) as ev.
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
    
  Lemma label_set_rmw_step (S: (actid -> label) -> actid -> bool) matcher st1 st2 tid lblr lblw index
        (IND: index >= eindex st1)
        (ADD: exists foo bar baz bazz,
            G st2 = add_rmw (G st1) tid index lblr lblw foo bar baz bazz)
        (MATCH: processes_lab S matcher)
        (BOUND: index_bounded S st1):
    S (lab (G st2)) ≡₁ S (lab (G st1))
      ∪₁ (if matcher lblr then eq (ThreadEvent tid index) else ∅)
      ∪₁ (if matcher lblw then eq (ThreadEvent tid (index + 1)) else ∅).
  Proof.
    (* TODO: use seq_equiv_exp_iff *)
    assert (SAME_SET_ELT: forall (A : Type) (s s' : A -> Prop),
               s ≡₁ s' <-> (forall x : A, s x <-> s' x)).
    { intros. red. split; [apply set_equiv_exp| ].
      intros. red. split.
      all: red; intros.
      all: specialize (H x).
      all: apply H; auto. }    
    apply SAME_SET_ELT. unfold set_union. intros.
    red in MATCH. rewrite !MATCH.
    desc. rewrite ADD. simpl. 
    remember (ThreadEvent tid index) as evr. 
    remember (ThreadEvent tid (index + 1)) as evw.  
    destruct (classic (x = evr)).
    { rewrite H. rewrite updo.
      2: { red. ins. subst. inversion H0. omega. }
      rewrite upds. 
      destruct (matcher lblr) eqn:MATCHED; auto.
      unfold set_empty. 
      cut (matcher (lab (G st1) evr) = false). 
      { intros. rewrite H0. intuition.
        destruct (matcher lblw); vauto. omega. }
      (* require boundness of a function and restrict ev to be new event*)
      do 2 red in BOUND. specialize (BOUND evr).
      rewrite MATCH in BOUND.
      apply Bool.not_true_is_false. red. intros CONTRA. 
      apply BOUND in CONTRA. vauto. simpl in CONTRA. omega. }
    destruct (classic (x = evw)).
    { rewrite H0. rewrite upds.
      destruct (matcher lblw) eqn:MATCHED; auto.
      unfold set_empty. 
      cut (matcher (lab (G st1) evw) = false). 
      { intros. rewrite H1. intuition.
        destruct (matcher lblr); vauto. omega. }
      (* require boundness of a function and restrict ev to be new event*)
      do 2 red in BOUND. specialize (BOUND evw).
      rewrite MATCH in BOUND.
      apply Bool.not_true_is_false. red. intros CONTRA. 
      apply BOUND in CONTRA. vauto. simpl in CONTRA. omega. }
    do 2 (rewrite updo; auto). split; auto.
    intros. des; auto.  
    - destruct (matcher lblr); vauto.
    - destruct (matcher lblw); vauto.
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

  Lemma label_set_bound_inter st tid
        (STEPS: exists n, (step tid) ^^ n (init (instrs st)) st)
        index (IND: index >= eindex st)
        (S : (actid -> label) -> actid -> bool) (matcher : label -> bool)
        (MATCH: processes_lab S matcher)
        (NONNOP: non_nop matcher):
    S (lab (G st)) ∩₁ eq (ThreadEvent tid index) ≡₁ ∅. 
  Proof.
    desc.
    red. split; [| basic_solver].
    pose proof (@nonnop_bounded _ S matcher _ _ MATCH NONNOP STEPS).
    red in H. 
    rewrite H.
    red. ins. do 2 (red in H0; desc). subst. simpl in H0. omega.
  Qed.
  
  Definition splits_to {A: Type} (S S' S'': A -> Prop) := (S ≡₁ S' ∪₁ S'') /\ (S' ∩₁ S'' ≡₁ ∅). 
  
  (* Lemma E_ADD G G' tid index (ADD: exists lbl foo bar baz bazz, *)
  (*                                G' = add G tid index lbl foo bar baz bazz): *)
  (*   E G' ≡₁ E G ∪₁ eq (ThreadEvent tid index). *)
  (* Proof.  *)
  (*   desc. subst G'. unfold add, acts_set. simpl. *)
  (*   basic_solver.  *)
  (* Qed. *)
  
  Lemma E_ADD G G' tid index
        (ADD: exists lbl foo bar baz bazz, G' = add G tid index lbl foo bar baz bazz):
    E G' ≡₁ E G ∪₁ eq (ThreadEvent tid index).
  Proof.
    desc. rewrite ADD. unfold acts_set. simpl. basic_solver. 
  Qed.

  Lemma E_bound_inter st tid
        (STEPS: exists n, (step tid) ^^ n (init (instrs st)) st)
         index (IND: index >= eindex st):
    E (G st) ∩₁ eq (ThreadEvent tid index) ≡₁ ∅. 
  Proof.
    red. split; [| basic_solver].  
    desc. sin_rewrite E_bounded; eauto.
    red. ins. red in H. desc. rewrite <- H0 in H. simpl in H. omega.  
  Qed.
  
  Lemma E_ADD_RMW G G' tid index
        (ADD: exists lblr lblw foo bar baz bazz, G' = add_rmw G tid index lblr lblw foo bar baz bazz):
    E G' ≡₁ E G ∪₁ eq (ThreadEvent tid index) ∪₁ eq (ThreadEvent tid (index + 1)).
  Proof.
    desc. subst G'. unfold add_rmw, acts_set. simpl.
    basic_solver.
  Qed.

  Definition is_rw := fun (A : Type) (lab : A -> label) (a : A) =>
match lab a with
| Aload _ _ _ _ => true
| Astore _ _ _ _ => true
| _ => false
end. 

  Definition rw_matcher := fun lbl => w_matcher lbl || r_matcher lbl. 

  Lemma rw_pl: processes_lab (@is_rw actid) rw_matcher. 
  Proof.
    red. intros. unfold is_rw.
    destruct (labfun ev); auto.
  Qed.
     
  Lemma rw_alt G: (fun x => is_rw (lab G) x) ≡₁ RW G.
  Proof.
    apply set_equiv_exp_iff.
    ins. unfold set_union.
    unfold is_rw, is_r, is_w. destruct (lab G x); vauto.
    tauto. 
  Qed. 
            
  Lemma RWO_ADD st st' tid index lbl
        (ADD: exists foo bar baz bazz,
            G st' = add (G st) tid index lbl foo bar baz bazz)
        (STEPS: exists n, (step tid) ^^ n (init (instrs st)) st)
        (IND: index >= eindex st):
    RWO (G st') ≡₁ RWO (G st)
        ∪₁  (if rw_matcher lbl then eq (ThreadEvent tid index) else ∅). 
  Proof.
    desc.
    forward eapply (@label_set_step (@is_rw actid) rw_matcher st st' tid lbl _ IND _ rw_pl (@nonnop_bounded _ (@is_rw actid) rw_matcher _ _ rw_pl (eq_refl false) STEPS)) as RW_EXT; eauto.
    Unshelve. 2: { repeat eexists. eauto. }
    unfold RWO. do 2 rewrite rw_alt in RW_EXT. 
    rewrite RW_EXT. 
    replace (rmw (G st')) with (rmw (G st)).
    2: { rewrite ADD. auto. }
    rewrite set_minus_union_l.
    apply set_equiv_union; [basic_solver| ].
    destruct (rw_matcher lbl); [| basic_solver].      
    split; [basic_solver| ]. 
    apply inclusion_minus. split; [basic_solver| ].
    rewrite rmw_bibounded; eauto.
    unfold set_inter. red. ins. desc.
    subst. red in H0. desc. simpl in H0. omega.
  Qed. 
  
  Lemma RWO_bound_inter st tid
        (STEPS: exists n, (step tid) ^^ n (init (instrs st)) st)
        index (IND: index >= eindex st):
    RWO (G st) ∩₁ eq (ThreadEvent tid index) ≡₁ ∅. 
  Proof.
    desc.
    red. split; [| basic_solver].
    unfold RWO.
    arewrite (RW (G st) \₁ dom_rel (rmw (G st)) ⊆₁ RW (G st)) by basic_solver. 
    pose proof (@nonnop_bounded _ (@is_rw actid) rw_matcher _ _ rw_pl (eq_refl false) STEPS). red in H. 
    rewrite <- rw_alt. rewrite H.
    red. ins. do 2 (red in H0; desc). subst. simpl in H0. omega.
  Qed.
  
  (* Lemma LABEL_ADD st st' tid index lbl *)
  (*       (ADD: exists foo bar baz bazz, *)
  (*           G st' = add (G st) tid index lbl foo bar baz bazz) *)
  (*       (STEPS: exists n, (step tid) ^^ n (init (instrs st)) st) *)
  (*       (IND: index >= eindex st) *)
  (*       S matcher (MATCH: processes_lab S matcher): *)
  (*   S (G st') ≡₁ S (G st) *)
  (*       ∪₁  (if matcher lbl then eq (ThreadEvent tid index) else ∅).  *)
  (* Proof. *)
  (*   desc. *)
  (*   forward eapply (@label_set_step (@is_rw actid) rw_matcher st st' tid lbl _ IND _ rw_pl (@nonnop_bounded _ (@is_rw actid) rw_matcher _ _ rw_pl (eq_refl false) STEPS)) as RW_EXT; eauto. *)
  (*   Unshelve. 2: { repeat eexists. eauto. } *)
  (*   unfold RWO. do 2 rewrite rw_alt in RW_EXT.  *)
  (*   rewrite RW_EXT.  *)
  (*   replace (rmw (G st')) with (rmw (G st)). *)
  (*   2: { rewrite ADD. auto. } *)
  (*   rewrite set_minus_union_l. *)
  (*   apply set_equiv_union; [basic_solver| ]. *)
  (*   destruct (rw_matcher lbl); [| basic_solver].       *)
  (*   split; [basic_solver| ].  *)
  (*   apply inclusion_minus. split; [basic_solver| ]. *)
  (*   rewrite rmw_bibounded; eauto. *)
  (*   unfold set_inter. red. ins. desc. *)
  (*   subst. red in H0. desc. simpl in H0. omega. *)
  (* Qed.  *)
     
  Lemma diff_events_empty tid index index' (NEQ: index <> index'):
     eq (ThreadEvent tid index) ∩₁ eq (ThreadEvent tid index') ≡₁ ∅.
  Proof. basic_solver. Qed.      

  Lemma RWO_ADD_rmw st st' tid index lbl1 lbl2
        (ADD: exists foo bar baz bazz,
            G st' = add_rmw (G st) tid index lbl1 lbl2 foo bar baz bazz)
        (STEPS: exists n, (step tid) ^^ n (init (instrs st)) st)
        (IND: index >= eindex st):
    RWO (G st') ≡₁ RWO (G st)
        ∪₁ (if rw_matcher lbl2 then eq (ThreadEvent tid (index + 1)) else ∅). 
  Proof.
    desc.
    forward eapply (@label_set_rmw_step (@is_rw actid) rw_matcher st st' tid lbl1 lbl2 _ IND _ rw_pl (@nonnop_bounded _ (@is_rw actid) rw_matcher _ _ rw_pl (eq_refl false) STEPS)) as RW_EXT.
    Unshelve. 2: { repeat eexists. eauto. }
    repeat rewrite rw_alt in RW_EXT.
    unfold RWO. 
    rewrite RW_EXT.
    remember (ThreadEvent tid index) as ev. remember (ThreadEvent tid (index + 1)) as ev'. 
    arewrite (rmw (G st') ≡ rmw (G st) ∪ singl_rel ev ev').
    { rewrite ADD. unfold add_rmw. simpl. basic_solver. }
    rewrite dom_union.
    rewrite set_minus_union_r.
    arewrite (dom_rel (singl_rel ev ev') ≡₁ eq ev) by basic_solver.
    pose proof (@nonnop_bounded _ (@is_rw actid) rw_matcher _ _ rw_pl (eq_refl false) STEPS) as RW_BOUND. 
    red in RW_BOUND. 
    assert (RW (G st) ∩₁ eq ev ≡₁ ∅) as RW_Nev. 
    { split; [| basic_solver].
      rewrite <- rw_alt. rewrite RW_BOUND.
      unfold set_inter. red. ins. desc.
      subst. simpl in H. omega. }
    assert (RW (G st) ∩₁ eq ev' ≡₁ ∅) as RW_Nev'. 
    { split; [| basic_solver].
      rewrite <- rw_alt. rewrite RW_BOUND.
      unfold set_inter. red. ins. desc.
      subst. simpl in H. omega. }
    assert (forall {A: Type} (cond: bool) (X Y: A -> Prop),
               X ∩₁ Y ≡₁ ∅ -> (if cond then X else ∅) ∩₁ Y ≡₁ ∅) as IF_CONGR. 
    { ins. destruct cond; [| basic_solver]. auto. }
    arewrite ((RW (G st) ∪₁ (if rw_matcher lbl1 then eq ev else ∅)
       ∪₁ (if rw_matcher lbl2 then eq ev' else ∅)) \₁ 
                                                   eq ev ≡₁ RW (G st) ∪₁ (if rw_matcher lbl2 then eq ev' else ∅)).
    { do 2 rewrite set_minus_union_l.
      rewrite empty_inter_minus_same; auto. 
      arewrite ((if rw_matcher lbl1 then eq ev else ∅) \₁ eq ev ≡₁ ∅) by basic_solver.
      rewrite empty_inter_minus_same.
      2: { destruct (rw_matcher lbl2); [| basic_solver].
           subst. rewrite diff_events_empty; [basic_solver | omega]. }
      basic_solver. }
    do 2 rewrite set_minus_union_l.
    rewrite empty_inter_minus_same with (X := (if rw_matcher lbl1 then eq ev else ∅)).
    2: { apply IF_CONGR. split; [| basic_solver].
         rewrite rmw_bibounded; eauto.
         unfold set_inter. red. ins. desc.
         subst. red in H0. desc. simpl in H0. omega. } 
    rewrite empty_inter_minus_same with (X := (if rw_matcher lbl2 then eq ev' else ∅)).
    2: { apply IF_CONGR. split; [| basic_solver].
         rewrite rmw_bibounded; eauto.
         unfold set_inter. red. ins. desc.
         subst. red in H0. desc. simpl in H0. omega. }
    rewrite set_inter_union_r.
    do 2 rewrite set_inter_union_l.
    rewrite set_inter_minus_l, set_interK.
    do 2 (rewrite IF_CONGR; [| rewrite set_interC; auto]).
    remove_emptiness.
    apply set_equiv_union; [basic_solver| ].
    destruct (rw_matcher lbl2); [| basic_solver].
    do 2 rewrite set_inter_union_l.
    rewrite set_inter_minus_l, RW_Nev'.
    rewrite IF_CONGR.
    2: { subst. apply diff_events_empty. omega. }
    basic_solver.
  Qed.     
    
End BoundedProperties.
