(******************************************************************************)
(** * OCaml MM is weaker than IMM_S   *)
(******************************************************************************)
Require Import Classical Peano_dec.
From hahn Require Import Hahn.

Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCaml.
Require Import OCamlToimm_s. 
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
From PromisingLib Require Import Basic Loc.

Set Implicit Arguments.
Remove Hints plus_n_O.


Section OCaml_Program.
  Definition Oinstlist := list Prog.Instr.t.
    
  Definition Othread_execution (tid : thread_id) (insts : Oinstlist) (pe : execution) :=
    exists s,
      ⟪ STEPS : (step tid)＊ (init insts) s ⟫ /\
      ⟪ TERMINAL : is_terminal s ⟫ /\
      ⟪ PEQ : s.(G) = pe ⟫.

  Definition OProg := IdentMap.t Oinstlist.

  Definition Oprogram_execution (prog : OProg) (G : execution) :=
    (forall e (IN: G.(acts_set) e), is_init e \/ IdentMap.In (tid e) prog)
    /\ forall thread linstr (INTHREAD: IdentMap.find thread prog = Some linstr),
      exists pe, Othread_execution thread linstr pe
            /\ thread_restricted_execution G thread pe.
  
End OCaml_Program.
  

Section OCamlMM_TO_IMM_S_PROG.

  Variable exchange_reg: Reg.t.
  Lemma exchange_reg_dedicated: True.
  Proof.
  Admitted. 

  Inductive is_thread_compiled : Oinstlist -> list Prog.Instr.t -> Prop :=
  | compiled_empty: is_thread_compiled [] []
  | compiled_Rna lhs loc ro ri (rest: is_thread_compiled ro ri):
      let ld := (Instr.load Orlx lhs loc) in
      is_thread_compiled (ld :: ro) (ld :: ri)
  | compiled_Wna loc val ro ri (rest: is_thread_compiled ro ri):
      let st := (Instr.store Orlx loc val) in
      let f := (Instr.fence Oacqrel) in
      is_thread_compiled (st :: ro) (f :: st :: ri)
  | compiled_Rat lhs loc ro ri (rest: is_thread_compiled ro ri):
      let ld := (Instr.load Osc lhs loc) in
      let f := (Instr.fence Oacq) in
      is_thread_compiled (ld :: ro) (f :: ld :: ri)
  | compiled_Wat loc val ro ri (rest: is_thread_compiled ro ri):
      let st := (Instr.store Osc loc val) in
      let exc := (Instr.update (Instr.exchange val) Xpln Osc Osc exchange_reg loc) in
      let f := (Instr.fence Oacq) in
      is_thread_compiled (st :: ro) (f :: exc :: ri)
  | compiled_assign lhs rhs ro ri (rest: is_thread_compiled ro ri):
      let asn := (Instr.assign lhs rhs) in
      is_thread_compiled (asn :: ro) (asn :: ri)
  | compiled_ifgoto e n ro ri (rest: is_thread_compiled ro ri):
      let igt := (Instr.ifgoto e n) in
      is_thread_compiled (igt :: ro) (igt :: ri). 
  

  Definition is_compiled (po: OProg) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id po <-> IdentMap.In t_id pi ⟫ /\
    forall thread to ti (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti),
      is_thread_compiled to ti.

  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  Notation "'F' G" := (fun a => is_true (is_f G.(lab) a)) (at level 1).
  Notation "'ORlx' G" := (fun a => is_true (is_only_rlx G.(lab) a)) (at level 1).
  Notation "'Sc' G" := (fun a => is_true (is_sc G.(lab) a)) (at level 1). 
  Notation "'Acq' G" := (fun a => is_true (is_acq G.(lab) a)) (at level 1). 
  Notation "'Acqrel' G" := (fun a => is_true (is_acqrel G.(lab) a)) (at level 1). 
  Notation "'hbo'" := (OCaml.hb). 
  
  Definition prepend_events (s: actid -> Prop) (shift: nat):=
    fun (a: actid) =>
      match a with
      | ThreadEvent tid num => exists orig_num, s (ThreadEvent tid (orig_num + shift))
      | _ => False
      end.

  
  Definition same_behavior (GO GI: execution) :=
    let Facq' := prepend_events (E GO ∩₁ Sc GO) 2 in
    let Facqrel' := prepend_events (E GO ∩₁ W GO ∩₁ ORlx GO) 2 in
    let R' := prepend_events (E GO ∩₁ W GO ∩₁ Sc GO) 1 in

    let rmw_pair r w := (tid r = tid w) /\ (index r = index w - 1) in

    let wf_labels :=
        (forall e (OMM_EVENT: E GO e), GI.(lab) e = GO.(lab) e) /\
        (forall e (FACQ: Facq' e), GI.(lab) e = Afence Oacq) /\
        (forall e (FACQ: Facqrel' e), GI.(lab) e = Afence Oacqrel) /\
        (forall e (R': R' e), exists loc val w,
              GI.(lab) e = Aload true Osc loc val /\
              GO.(lab) w = Astore Xpln Osc loc val /\
              rmw_pair e w) in
    ⟪OMM_SCALED: forall e (OMM_EVENT: E GO e), exists num, index e = 3 * num ⟫ /\
    ⟪ADD_EVENTS: E GI ≡₁ E GO ∪₁ Facq' ∪₁ Facqrel' ∪₁ R' ⟫ /\
    ⟪EXT_LABELS: wf_labels ⟫ /\
    ⟪NEW_RMW: GI.(rmw) ≡ fun r w => (E GI ∩₁ R GI ∩₁ Sc GI) r /\ (E GI ∩₁ W GI ∩₁ Sc GI) w /\ rmw_pair r w ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ⊆ GI.(rf)⟫. 
      
  Variable ProgO: OProg.

  Variable ProgI: Prog.Prog.t.
  Hypothesis Compiled: is_compiled ProgI ProgO.

  Definition compile_grouped EE shift event :=
    Nat.eqb (Nat.modulo (index event) 3) 0 /\
    EE (ThreadEvent (tid event) (index event + shift)). 

  Theorem compilation_correctness:
    forall (GI: execution) (WF: Wf GI) sc (ExecI: program_execution ProgI GI) 
      (IPC: imm_s.imm_psc_consistent GI sc)
      (IMM_SCALED: forall e (IMM_EVENT: E GI e), exists num,
            ((set_compl (F GI ∪₁ dom_rel GI.(rmw))) e /\ index e = 3 * num) \/ 
            (F GI e /\ index e = 3 * num - 2) \/
            (dom_rel GI.(rmw) e /\ index e = 3 * num - 1)),
    exists (GO: execution),
      ⟪WF': Wf GO ⟫ /\
      ⟪ExecO: Oprogram_execution ProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.
    ins.
    set (GO :=
           {| acts := filterP (RW GI \₁ dom_rel (GI.(rmw))) GI.(acts);
              lab := GI.(lab); (* should restrict domain *)
              rmw := ∅₂;
              (* same deps? *)
              data := GI.(data);
              addr := GI.(addr);
              ctrl := GI.(ctrl);              
              rmw_dep := ∅₂;
              rf := GI.(rf) ⨾ ⦗set_compl (dom_rel GI.(rmw))⦘;
              co := GI.(co) |}). 
    exists GO. splits.
    { destruct WF. 
      split; subst GO; simpl; auto; admit. }
    3: { red. splits; auto.
         { admit. (* should convert to another graph *) }
         { admit. }
         { admit. }
         { admit. }
         { admit. }
         { admit. }
         subst GO. simpl. basic_solver. }
    { red. splits.
      { intros e EGOe.
        right. 
        (* destruct e; auto. right. *)
        (* same threads, should be easy *) admit. }
      intros thread subprog TP.
      set (GOt := let eq_tid := (fun e => tid e = thread) in
                  let restrict rel := ⦗eq_tid⦘ ⨾ rel ⨾ ⦗eq_tid⦘ in
                  {| acts := filterP eq_tid GO.(acts);
                     lab := GO.(lab); (* should restrict domain *)
                     rmw := restrict GO.(rmw);
                     data := restrict GO.(data);
                     addr := restrict GO.(addr);
                     ctrl := restrict GO.(ctrl);              
                     rmw_dep := restrict GO.(rmw_dep);
                     rf := restrict GO.(rf);
                     co := restrict GI.(co) |}). 
      exists GOt.
      split.
      2: { subst GOt. split; simpl; auto.
           admit. (* E GO restriction; should be easy *)
      }
      (* ? show by induction that thread execution goes to some final state *)
      red. 
      admit. }

    cut (ocaml_consistent GI).
    { assert (RF': rf GO ≡ rf GI ⨾ ⦗set_compl (dom_rel (rmw GI))⦘).
      { subst GO.  simpl. basic_solver. }
      assert (E': E GO ≡₁ E GI ∩₁ (RW GI \₁ dom_rel (rmw GI))).
      { subst GO. unfold acts_set. simpl.
        red. split.
        { red. ins. rewrite in_filterP_iff in H. red. desc. auto. }
        red. ins. rewrite  in_filterP_iff. red in H. auto. }
      assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
      { unfold Execution.sb.        
        rewrite !seqA. do 2 seq_rewrite <- id_inter.
        rewrite set_interC. 
        rewrite E'. 
        basic_solver. }
      assert (SC': Sc GO ≡₁ Sc GI) by intuition. 
      assert (HBO': hbo GO ⊆ hbo GI).
      { unfold OCaml.hb. apply clos_trans_mori.
        apply union_mori; [rewrite SB'; basic_solver | ].
        hahn_frame.
        apply union_mori; [basic_solver | rewrite RF'; basic_solver]. }
      assert (CO': co GO ≡ co GI) by intuition.
      assert (FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI).
      { unfold fr. rewrite CO'. rewrite <- seqA. apply seq_more; [| basic_solver].
        subst GO. simpl. basic_solver. }
      intros OCAML_GI. unfold ocaml_consistent. unfold ocaml_consistent in OCAML_GI.
      splits; auto.
      { red. rewrite E', RF'.
        desc. red in Comp.
        rewrite set_interC, <- set_interA.
        rewrite set_inter_minus_r.
        arewrite (R GO ∩₁ E GI ∩₁ RW GI ≡₁ R GO ∩₁ E GI) by basic_solver.
        rewrite codom_eqv1.
        rewrite set_minusE.
        apply set_subset_inter; [rewrite set_interC; apply Comp | basic_solver]. }
      { red. subst GO. simpl. rewrite inter_false_l. basic_solver. }
      { rewrite HBO'. subst GO. simpl. desc. auto. }
      { unfold fr. rewrite HBO'.
        arewrite (rf GO ⊆ rf GI) by rewrite RF'; auto. 
        subst GO. simpl. auto. desc. auto. }
      
      assert (W_RMW: W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
      { rewrite set_minusE.
        apply set_subset_inter_r. split; [basic_solver| ].
        sin_rewrite (WF.(wf_rmwD)).
        rewrite dom_eqv1. rewrite set_compl_inter.
        unionR left. type_solver. }
      arewrite (rfe GO ⊆ rfe GI).
      { unfold rfe. rewrite SB', RF'.
        apply inclusion_minus_l.
        rewrite rfi_union_rfe at 1. rewrite seq_union_l.
        apply union_mori.        
        { rewrite (WF.(wf_rfiD)). 
          arewrite (rfi GI ⊆ sb GI).
          apply seq_mori; [ | basic_solver]. 
          apply eqv_rel_mori. apply W_RMW. }
        unfold rfe. basic_solver. }
      arewrite (fre GO ⊆ fre GI).
      { unfold fre. rewrite SB', FR'.
        apply inclusion_minus_l.
        rewrite fri_union_fre at 1. rewrite seq_union_r.
        apply union_mori.        
        { rewrite (WF.(wf_friD)). 
          arewrite (fri GI ⊆ sb GI).
          rewrite <- seqA. 
          apply seq_mori; [basic_solver |].
          hahn_frame. apply eqv_rel_mori. apply W_RMW. }
        unfold fre. basic_solver. }
          
      arewrite (coe GO ⊆ coe GI).
      { unfold coe. rewrite SB', CO'. 
        apply inclusion_minus_l.
        rewrite coi_union_coe at 1. 
        apply union_mori.        
        { rewrite (WF.(wf_coiD)). 
          arewrite (coi GI ⊆ sb GI).
          apply seq_mori; hahn_frame; apply eqv_rel_mori; apply W_RMW. } 
        unfold coe. basic_solver. }
      rewrite SC'. 
      arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
      desc. auto. }
    
    (* need to specify location separation for OCaml program and prove that it's preserved in IMM program *)
    assert (LSM: forall l,
               (fun x => loc GI.(lab) x = Some l) \₁ is_init ⊆₁ ORlx GI \/
               (fun x => loc GI.(lab) x = Some l) \₁ is_init ⊆₁ Sc GI) by admit.
    assert (WSCFACQRMW : W GI ∩₁ Sc GI ≡₁ codom_rel (⦗F GI ∩₁ Acq GI⦘ ⨾ immediate (sb GI) ⨾ rmw GI)) by admit.
    assert (RMWSC: rmw GI ≡ ⦗Sc GI⦘ ⨾ rmw GI ⨾ ⦗Sc GI⦘) by admit.
    assert (WRLXF: W GI ∩₁ ORlx GI ⊆₁ codom_rel (⦗F GI ∩₁Acqrel GI⦘ ⨾ immediate (sb GI))) by admit. 
    assert (RSCF: R GI ∩₁ Sc GI ⊆₁ codom_rel (⦗F GI ∩₁ Acq GI⦘ ⨾ immediate (sb GI))) by admit. 

    apply (@imm_to_ocaml_consistent GI LSM WSCFACQRMW RMWSC WRLXF RSCF WF sc IPC).
    (* goal on the shelf ? *)
  Admitted.
  
  
End OCamlMM_TO_IMM_S_PROG.
