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
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.
Remove Hints plus_n_O.


Variable exchange_reg: Reg.t.
Lemma exchange_reg_dedicated: True.
Proof. Admitted. 


Section OCaml_Program.

  Inductive Oistep_ tid labels s1 s2 instr dindex (GT0: dindex > 0): Prop :=
  | assign reg expr
           (LABELS : labels = nil)
           (II : instr = Instr.assign reg expr)
           (UPC : s2.(pc) = s1.(pc) + 1)
           (UG : s2.(G) = s1.(G))
           (UINDEX : s2.(eindex) = s1.(eindex))
           (UREGS : s2.(regf) = RegFun.add reg (RegFile.eval_expr s1.(regf) expr) s1.(regf))
           (UDEPS : s2.(depf) = RegFun.add reg (DepsFile.expr_deps s1.(depf) expr) s1.(depf))
           (UECTRL : s2.(ectrl) = s1.(ectrl))
  | if_ expr shift
        (LABELS : labels = nil)
        (II : instr = Instr.ifgoto expr shift)
        (UPC   : if Const.eq_dec (RegFile.eval_expr s1.(regf) expr) 0
                 then s2.(pc) = s1.(pc) + 1
                 else s2.(pc) = shift)
        (UG    : s2.(G) = s1.(G))
        (UINDEX : s2.(eindex) = s1.(eindex))
        (UREGS : s2.(regf) = s1.(regf))
        (UDEPS : s2.(depf) = s1.(depf))
        (UECTRL : s2.(ectrl) = (DepsFile.expr_deps s1.(depf) expr) ∪₁ s1.(ectrl))
  | load ord reg lexpr val l
         (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
         (II : instr = Instr.load ord reg lexpr)
         (LABELS : labels = [Aload false ord (RegFile.eval_lexpr s1.(regf) lexpr) val])
         (UPC   : s2.(pc) = s1.(pc) + 1)
         (UG    : s2.(G) =
                  add s1.(G) tid s1.(eindex) (Aload false ord (RegFile.eval_lexpr s1.(regf) lexpr) val) ∅
                                             (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl) ∅)
         (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
         (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
         (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
         (UECTRL : s2.(ectrl) = s1.(ectrl))
  | store ord lexpr expr l v x
          (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
          (V: v = RegFile.eval_expr  s1.(regf)  expr)
          (X: x = Xpln)
          (LABELS : labels = [Astore x ord l v])
          (II : instr = Instr.store ord lexpr expr)
          (UPC   : s2.(pc) = s1.(pc) + 1)
          (UG    : s2.(G) =
                   add s1.(G) tid s1.(eindex) (Astore x ord l v)
                                              (DepsFile.expr_deps  s1.(depf)  expr)
                                              (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl) ∅)
          (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
          (UREGS : s2.(regf) = s1.(regf))
          (UDEPS : s2.(depf) = s1.(depf))
          (UECTRL : s2.(ectrl) = s1.(ectrl))
  | fence ord 
          (LABELS : labels = [Afence ord])
          (II : instr = Instr.fence ord)
          (UPC   : s2.(pc) = s1.(pc) + 1)
          (UG    : s2.(G) = add s1.(G) tid s1.(eindex) (Afence ord) ∅ ∅ s1.(ectrl) ∅)
          (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
          (UREGS : s2.(regf) = s1.(regf))
          (UDEPS : s2.(depf) = s1.(depf))
          (UECTRL : s2.(ectrl) = s1.(ectrl))
  | cas_un expr_old expr_new xmod ordr ordw reg lexpr val l
           (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
           (NEXPECTED : val <> RegFile.eval_expr s1.(regf) expr_old)
           (LABELS : labels = [Aload true ordr l val])
           (II : instr= Instr.update (Instr.cas expr_old expr_new) xmod ordr ordw reg lexpr)
           (UPC   : s2.(pc) = s1.(pc) + 1)
           (UG    : s2.(G) =
                    add s1.(G) tid s1.(eindex) (Aload true ordr l val) ∅
                                               (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                                                                                          (DepsFile.expr_deps s1.(depf) expr_old))
           (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
           (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
           (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
           (UECTRL : s2.(ectrl) = s1.(ectrl))
  | cas_suc expr_old expr_new xmod ordr ordw reg lexpr l expected new_value
            (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
            (EXPECTED: expected = RegFile.eval_expr s1.(regf) expr_old)
            (NEW: new_value = RegFile.eval_expr s1.(regf) expr_new)
            (LABELS : labels = [Astore xmod ordw l new_value; Aload true ordr l expected])
            (II : instr = Instr.update (Instr.cas expr_old expr_new) xmod ordr ordw reg lexpr)
            (UPC   : s2.(pc) = s1.(pc) + 1)
            (UG    : s2.(G) =
                     add_rmw s1.(G)
                                  tid s1.(eindex) (Aload true ordr l expected) (Astore xmod ordw l new_value)
                                                  (DepsFile.expr_deps s1.(depf) expr_new)
                                                  (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                                                                                             (DepsFile.expr_deps s1.(depf) expr_old))
            (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
            (UREGS : s2.(regf) = RegFun.add reg expected s1.(regf))
            (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
            (UECTRL : s2.(ectrl) = s1.(ectrl))
  | inc expr_add xmod ordr ordw reg lexpr val l nval
        (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
        (NVAL: nval = val + RegFile.eval_expr s1.(regf) expr_add)
        (LABELS : labels = [Astore xmod ordw l nval; Aload true ordr l val])
        (II : instr = Instr.update (Instr.fetch_add expr_add) xmod ordr ordw reg lexpr)
        (UPC   : s2.(pc) = s1.(pc) + 1)
        (UG    : s2.(G) =
                 add_rmw s1.(G) tid s1.(eindex)
                                         (Aload true ordr l val)
                                         (Astore xmod ordw l nval)
                                         ((eq (ThreadEvent tid s1.(eindex))) ∪₁ (DepsFile.expr_deps s1.(depf) expr_add))
                                         (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl)
                                                                                    ∅)
        (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
        (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
        (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
        (UECTRL : s2.(ectrl) = s1.(ectrl))
  | exchange new_expr xmod ordr ordw reg loc_expr old_value loc new_value
             (L: loc = RegFile.eval_lexpr s1.(regf) loc_expr)
             (NVAL: new_value = RegFile.eval_expr s1.(regf) new_expr)
             (LABELS : labels = [Astore xmod ordw loc new_value;
                                   Aload true ordr loc old_value])
             (II : instr = Instr.update (Instr.exchange new_expr)
                                        xmod ordr ordw reg loc_expr)
             (UPC   : s2.(pc) = s1.(pc) + 1)
             (UG    : s2.(G) =
                      add_rmw s1.(G) tid s1.(eindex)
                                              (Aload true ordr loc old_value)
                                              (Astore xmod ordw loc new_value)
                                              (DepsFile.expr_deps s1.(depf) new_expr)
                                              (DepsFile.lexpr_deps s1.(depf) loc_expr)
                                              s1.(ectrl)
                                                   ∅)
             (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
             (UREGS : s2.(regf) = RegFun.add reg old_value s1.(regf))
             (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid s1.(eindex))) s1.(depf))
             (UECTRL : s2.(ectrl) = s1.(ectrl)).      

  Definition Oistep (tid : thread_id) (labels : list label) s1 s2 :=
    ⟪ INSTRS : s1.(instrs) = s2.(instrs) ⟫ /\
    ⟪ ISTEP: exists instr dindex', 
        Some instr = List.nth_error s1.(instrs) s1.(pc) /\
        @Oistep_ tid labels s1 s2 instr (S dindex') (gt_Sn_O dindex')⟫.

  Definition Ostep (tid : thread_id) s1 s2 :=
    exists lbls, Oistep tid lbls s1 s2.

  Definition is_ocaml_mode mode :=
    match mode with
    | Orlx | Osc => True
    | _ => False
    end. 
  
  Definition is_ocaml_instruction instr :=
    match instr with
    | Instr.assign _ _ | Instr.ifgoto _ _ => True
    | Instr.load mode _ _ | Instr.store mode _ _ => is_ocaml_mode mode
    | _ => False
    end. 

  Definition Othread_execution (tid : thread_id) (insts : list Prog.Instr.t) (pe : execution) :=
    exists s,
      ⟪ STEPS : (Ostep tid)＊ (init insts) s ⟫ /\
      ⟪ TERMINAL : is_terminal s ⟫ /\
      ⟪ PEQ : s.(G) = pe ⟫.

  Definition OCamlProgram (prog: Prog.Prog.t) := True. 

  Definition Oprogram_execution prog (OPROG: OCamlProgram prog) (G : execution) :=
    (forall e (IN: G.(acts_set) e), is_init e \/ IdentMap.In (tid e) prog)
    /\ forall thread linstr (INTHREAD: IdentMap.find thread prog = Some linstr),
      exists pe, Othread_execution thread linstr pe
            /\ thread_restricted_execution G thread pe.
  
End OCaml_Program.


Section OCaml_IMM_Compilation.

  Inductive is_instruction_compiled : Prog.Instr.t -> list Prog.Instr.t -> Prop :=
  | compiled_Rna lhs loc:
      let ld := (Instr.load Orlx lhs loc) in
      is_instruction_compiled (ld) ([ld])
  | compiled_Wna loc val:
      let st := (Instr.store Orlx loc val) in
      let f := (Instr.fence Oacqrel) in
      is_instruction_compiled (st) ([f; st])
  | compiled_Rat lhs loc:
      let ld := (Instr.load Osc lhs loc) in
      let f := (Instr.fence Oacq) in
      is_instruction_compiled (ld) ([f; ld])
  | compiled_Wat loc val:
      let st := (Instr.store Osc loc val) in
      let exc := (Instr.update (Instr.exchange val) Xpln Osc Osc exchange_reg loc) in
      let f := (Instr.fence Oacq) in
      is_instruction_compiled (st) ([f; exc])
  | compiled_assign lhs rhs:
      let asn := (Instr.assign lhs rhs) in
      is_instruction_compiled (asn) ([asn])
  | compiled_ifgoto e n:
      let igt := (Instr.ifgoto e n) in
      is_instruction_compiled (igt) ([igt]).
  
  Inductive is_thread_compiled : list Prog.Instr.t -> list Prog.Instr.t -> Prop :=
  | compiled_empty: is_thread_compiled [] []
  | compiled_add oinstr block ro ri
                     (instr_compiled: is_instruction_compiled oinstr block)
                     (rest: is_thread_compiled ro ri):
      is_thread_compiled (ro ++ [oinstr]) (ri ++ block).

  Definition is_compiled (po: Prog.Prog.t) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id po <-> IdentMap.In t_id pi ⟫ /\
    forall thread to ti (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti), is_thread_compiled to ti.

End OCaml_IMM_Compilation.   

Section SEQ_STEPS.
  
  Inductive step_seq : thread_id -> list ((list label)*Prog.Instr.t) -> state -> state -> Prop :=
  | empty_step_seq tid st: step_seq tid [] st st
  | next_step_seq
      tid labels insn cur_st next_st fin_st
      (STEP: istep_ tid labels cur_st next_st insn)
      rest (REST: step_seq tid rest next_st fin_st):
      step_seq tid ((labels,insn)::rest) cur_st fin_st.

  Definition sublist {A: Type} (l: list A) (start len: nat) : list A.
  Admitted.
  
  Definition oseq_istep tid (labels_blocks: list (list label)) sti1 sti2 :=
    let n_steps := length labels_blocks in
    let block := sublist (instrs sti1) (pc sti1) n_steps in
    ⟪ INSTRS : sti1.(instrs) = sti2.(instrs) ⟫ /\
    ⟪ ISTEP: exists labelsblocks_insns,
        labelsblocks_insns = List.combine labels_blocks block /\
        step_seq tid labelsblocks_insns sti1 sti2 ⟫ /\
    ⟪ COMPILED_BLOCK: exists oinstr, is_instruction_compiled oinstr block ⟫.
  
  Definition oseq_step (tid : thread_id) sti1 sti2 :=
    exists labels_blocks, oseq_istep tid labels_blocks sti1 sti2.
  
End SEQ_STEPS. 
  
Section ClosuresProperties.
  Variable A: Type.
  Variable r: relation A. 
  
  Lemma steps_split n a b (SPLIT: a + b = n) x y:
    r^^n x y <-> exists z, r^^a x z /\ r^^b z y.
  Proof.
    split. 
    { ins.
      pose proof (pow_nm a b r) as STEPS_SPLIT.
      pose proof (same_relation_exp STEPS_SPLIT x y).
      rewrite SPLIT in H0. apply H0 in H. destruct H as [z STEPSz ].
      eauto. }
    ins. desf.
    pose proof (pow_nm a b r) as STEPS_SPLIT.
    pose proof (same_relation_exp STEPS_SPLIT x y).
    apply H1. red. exists z. auto.     
  Qed. 
  
  Lemma steps_sub n x y m (LEQ: m <= n): r^^n x y -> exists z, r^^m x z. 
  Proof.
    ins.
    pose proof (pow_nm m (n-m) r) as STEPS_SPLIT.
    pose proof (same_relation_exp STEPS_SPLIT x y).
    rewrite Const.add_sub_assoc in H0; [| auto]. rewrite minus_plus in H0.
    apply H0 in H. destruct H as [z STEPSz]. desc. 
    eauto. 
  Qed.

  Lemma steps0 x y: r^^0 x y <-> x = y.
  Proof. simpl. split; basic_solver. Qed.
  
  Lemma steps_indices n x y:
    r^^n x y -> forall i (INDEX: i < n), exists z1 z2, r^^i x z1 /\ r z1 z2.
  Proof.
    intros Rn i LT. 
    assert (LEQ: i + 1 <= n) by omega. 
    pose proof (steps_sub x y LEQ Rn) as [z2 Ri1].
    pose proof (@steps_split (i+1) i 1 eq_refl x z2).
    apply H in Ri1. destruct Ri1 as [z1 [Ri R1]].
    exists z1. exists z2. split; [auto| ]. 
    apply (same_relation_exp (pow_unit r)). auto.
  Qed. 
  
  Lemma step_prev x y k: r^^(S k) x y <-> exists z, r^^k x z /\ r z y.
  Proof. ins. Qed.
  
  Lemma crt_num_steps a b: r＊ a b <-> exists n, r ^^ n a b.
  Proof.
    split.
    { ins. rewrite clos_refl_transE in H. destruct H.
      { exists 0. split; auto. }
      induction H. 
      { exists 1. simpl. basic_solver. }
      destruct IHclos_trans1 as [n1 IH1]. destruct IHclos_trans2 as [n2 IH2]. 
      exists (n1+n2). (* split; [omega | ]. *)
      pose proof (@pow_nm _ n1 n2 r) as POW. destruct POW as [POW _].
      specialize (POW x z). apply POW.
      red. exists y. desc. split; auto. }
    ins. destruct H as [n STEPS].
    rewrite clos_refl_transE.
    destruct n.
    { left. desc.  simpl in STEPS. generalize STEPS. basic_solver 10. }
    right. desc.
    pose proof ctEE. specialize (H _ r). destruct H as [_ POW].
    apply POW. basic_solver. 
  Qed.


End ClosuresProperties. 

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
  Notation "'R_ex' G" := (fun a => is_true (R_ex G.(lab) a)) (at level 1).
  Notation "'hbo'" := (OCaml.hb). 
  Notation "'same_loc' G" := (same_loc G.(lab)) (at level 1).
  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
    
  (* Definition prepend_events (A: actid -> Prop) (shift: nat) := compose A (fun e => ThreadEvent (tid e) (index e + shift)). *)
  (* Notation "f '∙' g" := (compose f g) (at level 1). (* default notation is for other scope*)   *)
    
  Definition thread_local_property (P: execution -> Prop) := forall G,
      (forall tid SG (TRE: thread_restricted_execution G tid SG), P SG) -> P G.

  Definition thread_local_biproperty (P: execution -> execution -> Prop) := forall G1 G2,
      (forall tid SG1 SG2 (TRE1: thread_restricted_execution G1 tid SG1)
         (TRE2: thread_restricted_execution G2 tid SG2), P SG1 SG2) -> 
      P G1 G2.

  Definition omm_premises_hold G :=
    (* have issues with global Loc_ notation *)
    let Loc_ := fun l x => loc G.(lab) x = Some l in
    ⟪ LSM : forall l, (Loc_ l \₁ is_init ⊆₁ (ORlx G)  \/  Loc_ l \₁ is_init ⊆₁ (Sc G)) ⟫ /\
    ⟪ WSCFACQRMW : W G ∩₁ Sc G ≡₁ codom_rel (⦗F G ∩₁ Acq G⦘ ⨾ immediate (sb G) ⨾ rmw G) ⟫ /\
    ⟪ RMWSC  : rmw G ≡ ⦗Sc G⦘ ⨾ rmw G⨾ ⦗Sc G⦘ ⟫ /\
    ⟪ WRLXF : W G ∩₁ ORlx G ⊆₁ codom_rel (⦗F G ∩₁ Acqrel G⦘ ⨾ immediate (sb G)) ⟫ /\
    ⟪ RSCF  : R G ∩₁ Sc G ⊆₁ codom_rel (⦗F G ∩₁ Acq G⦘ ⨾ immediate (sb G)) ⟫.

  Definition same_behavior_local (GO GI: execution) :=
    ⟪RESTR_EVENTS: E GO ≡₁ E GI ∩₁ (RW GI \₁ dom_rel (GI.(rmw))) ⟫ /\
    ⟪SAME_LAB: lab GO = lab GI ⟫. 

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ≡ GI.(rf) ⨾ ⦗set_compl (dom_rel GI.(rmw))⦘⟫.
        
  Lemma tl_omm_premises : thread_local_property omm_premises_hold.
  Proof. Admitted.

  Lemma tl_sbl: thread_local_biproperty same_behavior_local.
  Proof. Admitted. 

  Record Wf_local (G: execution) :=
    {  wf_index' : forall a b, 
        (E G) a /\ (E G) b /\ a <> b /\ tid a = tid b /\ ~ is_init a -> index a <> index b;
       wf_dataD' : G.(data) ≡ ⦗R G⦘ ⨾ G.(data) ⨾ ⦗W G⦘ ;
       ctrl_sb' : G.(ctrl) ⨾ G.(sb) ⊆ G.(ctrl) ;
       wf_addrD' : G.(addr) ≡ ⦗R G⦘ ⨾ G.(addr) ⨾ ⦗RW G⦘ ;
       wf_ctrlD' : G.(ctrl) ≡ ⦗R G⦘ ⨾ G.(ctrl) ;
       wf_rmwD' : G.(rmw) ≡ ⦗R_ex G⦘ ⨾ G.(rmw) ⨾ ⦗W G⦘ ;
       wf_rmwl' : G.(rmw) ⊆ same_loc G ;
       wf_rmwi' : G.(rmw) ⊆ immediate G.(sb) ;
       wf_rmw_depD' : G.(rmw_dep) ≡ ⦗R G⦘ ⨾ G.(rmw_dep) ⨾ ⦗R_ex G⦘ ;
    }. 
  
  Record Wf_global (G: execution) :=
    {
      data_in_sb' : G.(data) ⊆ G.(sb) ;
      addr_in_sb' : G.(addr) ⊆ G.(sb) ;
      ctrl_in_sb' : G.(ctrl) ⊆ G.(sb) ;
      rmw_dep_in_sb' : G.(rmw_dep) ⊆ G.(sb) ;
      wf_rfE' : G.(rf) ≡ ⦗E G⦘ ⨾ G.(rf) ⨾ ⦗E G⦘ ;
      wf_rfD' : G.(rf) ≡ ⦗W G⦘ ⨾ G.(rf) ⨾ ⦗R G⦘ ;
      wf_rfl' : G.(rf) ⊆ same_loc G;
      wf_rfv' : funeq (val G.(lab)) G.(rf) ;
      wf_rff' : functional G.(rf)⁻¹ ;
      wf_coE' : G.(co) ≡ ⦗E G⦘ ⨾ G.(co) ⨾ ⦗E G⦘ ;
      wf_coD' : G.(co) ≡ ⦗W G⦘ ⨾ G.(co) ⨾ ⦗W G⦘ ;
      wf_col' : G.(co) ⊆ same_loc G;
      co_trans' : transitive G.(co) ;
      wf_co_total' : forall ol, is_total (E G ∩₁ W G ∩₁ (fun x => loc G.(lab) x = ol)) G.(co) ;
      co_irr' : irreflexive G.(co) ;
      wf_init' : forall l, (exists b, E G b /\ loc G.(lab) b = Some l) -> E G (InitEvent l) ;
      wf_init_lab' : forall l, G.(lab) (InitEvent l) = Astore Xpln Opln l 0 ;       
    }.

  (* Definition at_compilation_block sti := exists PO, is_thread_compiled PO (firstn sti.(pc) sti.(instrs)).  *)
      
  Definition mm_similar_states (sto sti: state) :=
    is_thread_compiled sto.(instrs) sti.(instrs)  /\
     is_thread_compiled (firstn sto.(pc) sto.(instrs)) (firstn sti.(pc) sti.(instrs)) /\
    (* at_compilation_block sti /\ *)
    same_behavior_local sto.(G) sti.(G) /\
    sto.(regf) = sti.(regf) /\
    sto.(eindex) = sti.(eindex). 
  
  (* Definition next_compilation_block sti (CORR: exists sto, mm_similar_states sto sti) (NOT_END: pc sti < length (instrs sti)) : list Prog.Instr.t. *)
  (* Admitted. *)
  
  Lemma pair_step sto sti (MM_SIM: mm_similar_states sto sti)
        tid sti' (SEQ_STEP: oseq_step tid sti sti'):
    exists sto', Ostep tid sto sto' /\ mm_similar_states sto' sti'.
  Proof. Admitted.
  
  Lemma first_end {A: Type} (l: list A) n x (NTH: Some x = List.nth_error l n):
    firstn (n + 1) l = firstn n l ++ [x].
  Proof.
    ins. 
    symmetry in NTH. apply nth_error_split in NTH as [l1 [l2 [CAT H]]].
    rewrite <- H. pose proof (@firstn_app_2 A 1 l1 (x :: l2)).
    rewrite CAT. simpl in H0. rewrite H0.
    pose proof (@firstn_app_2 A 0 l1). simpl in H1. rewrite app_nil_r, NPeano.Nat.add_0_r in H1.
    rewrite H1. auto. 
  Qed. 
    
  Lemma init_mm_same: forall PO PI (COMP: is_thread_compiled PO PI),
      mm_similar_states (init PO) (init PI).
  Proof.
    ins. red. simpl. splits; auto.
    { apply compiled_empty. }
    red. splits; auto. 
    arewrite (E init_execution ≡₁ ∅) by basic_solver. basic_solver. 
  Qed.

  Definition is_sorted_TODO {A: Type} (l: list A) := True.
  Inductive are_events_compilation_labels labels :=
  | labels_Rrlx loc val (R_RLX: labels  = [Aload false Orlx loc val]): are_events_compilation_labels labels
  | labels_Wrlx loc val (W_RLX: labels = [Afence Oacqrel; Astore Xpln Orlx loc val]): are_events_compilation_labels labels
  | labels_Rsc loc val (R_SC: labels = [Afence Oacq; Aload false Osc loc val]): are_events_compilation_labels labels
  | labels_Wsc loc val (W_SC: labels = [Afence Oacq; Aload true Osc loc val; Astore Xpln Osc loc val]): are_events_compilation_labels labels. 

  Inductive is_events_compilation_block (lab_fun: actid -> label) : list actid -> Prop :=
  | event_block_init loc: is_events_compilation_block lab_fun [(InitEvent loc)]
  | event_block_instr block (LABELS: are_events_compilation_labels (map lab_fun block)): is_events_compilation_block lab_fun block. 
  
    
  Definition is_compiled_graph GI :=
    let event_lt x y := Peano.lt (index x) (index y) in
    StronglySorted event_lt (acts GI) /\
    exists events_blocks,
      flatten events_blocks = acts GI /\
      Forall (is_events_compilation_block (lab GI)) events_blocks. 
      
  Lemma compiled_by_program GI PI (EX: exists tid, thread_execution tid PI GI)
        (COMP: exists PO, is_thread_compiled PO PI) : is_compiled_graph GI. 
  Proof.
    (*show that every oseq_step adds a block *)
  Admitted. 

  Lemma Wfl_subgraph SG' SG (SB: same_behavior_local SG SG') (WFL: Wf_local SG'): Wf_local SG.
  Proof.  Admitted.
      
  Lemma Wf_subgraph G' G (SB: same_behavior G G') (WF: Wf G'): Wf G.
  Proof. Admitted.

  Lemma step_seq_as_ct x y tid labelsblocks_insns (STEP_SEQ: step_seq tid labelsblocks_insns x y):
    (step tid) ^^ (length labelsblocks_insns) x y.
  Proof.
    (* use the following list predicate: *)
    (* is l_i prefix /\ exists state, let L=len state in step^^L x st *)
    (* /\ step^^(length l_i - L) st y*)
    (* then apply rev_ind *)
  Admitted.

  Definition at_compilation_block sti i := exists PO, length PO = i /\ is_thread_compiled PO (firstn sti.(pc) sti.(instrs)). 

  Lemma steps_same_instrs sti sti' (STEPS: exists tid, (step tid)＊ sti sti'):
    instrs sti = instrs sti'.
  Proof.
    destruct STEPS as [tid STEPS]. apply crt_num_steps in STEPS.
    destruct STEPS as [n STEPS].
    generalize dependent sti'.
    induction n.
    - intros sti' STEPS. simpl in STEPS. generalize STEPS. basic_solver 10.
    - intros sti' STEPS.
      rewrite step_prev in STEPS. destruct STEPS as [sti'' STEPS'']. desc.
      replace (instrs sti) with (instrs sti'').
      { red in STEPS''0. desf. red in STEPS''0. desf. }
      symmetry. eapply IHn. eauto.
  Qed. 
        
  Lemma oseq_iff_steps sti tid (AT_KTH_BLOCK: exists k, at_compilation_block sti k):
    (step tid)＊ (init (instrs sti)) sti <-> (oseq_step tid)＊ (init (instrs sti)) sti.
  Proof.
    split. 
    2: { intros OSEQ_STEPS.
         forward eapply (@hahn_inclusion_exp _ (oseq_step tid)＊ (step tid)＊); eauto.
         apply inclusion_rt_rt2.
         unfold oseq_step.
         red. intros x y [lbl_blocks OSEQ]. 
         apply crt_num_steps.
         red in OSEQ. desc. 
         exists (length labelsblocks_insns).
         apply step_seq_as_ct; auto. }
    
    intros STEPS.
    apply crt_num_steps in STEPS. destruct STEPS as [n_isteps STEPS].    
    destruct AT_KTH_BLOCK as [k AT_KTH_BLOCK].
    (* assert (OSEQ_INNER_STEPS: forall j sti_j (INDEX: j <= k) *)
    (*                             (AT_COMP: exists m,  *)
    (*                                 (step tid)^^m (init (instrs sti)) sti_j /\ *)
    (*                                 (step tid)^^(n_isteps - m) sti_j sti), *)
    (*              (oseq_step tid)^^j (init (instrs sti)) sti_j /\ *)
    (*              at_compilation_block sti_j j). *)
    (* { induction j. *)
    (*   - intros sti_j INDEX [m' INNER_STEPS']. admit. *)
    (*   - intros sti_j INDEX [m' INNER_STEPS'].  *)
    (* } *)
    
    assert (OSEQ_INNER_STEPS: forall j sti_j (INDEX: j <= k)
                                (AT_COMP: at_compilation_block sti_j j)
                                (REACH_TO: (step tid)＊ (init (instrs sti_j)) sti)
                                (REACH_FROM: (step tid)＊ sti_j sti),  
               (oseq_step tid)^^j (init (instrs sti)) sti_j). 
    { (* induction j. *)
      (* - intros sti_j INDEX AT_COMP REACH_TO REACH_FROM. *)
      (*   red in AT_COMP. destruct AT_COMP as [PO [EMPTY_PO COMP]]. *)
      (*   inversion COMP.  *)
      (*   + replace (instrs sti) with (instrs sti_j). *)
      (*     2: { eapply steps_same_instrs. exists tid. auto. } *)
          
      (*   + admit.  *)
      admit. 
    }
    apply crt_num_steps.
    forward eapply (OSEQ_INNER_STEPS).
    { eapply Nat.le_refl. }
    { eauto. }
    { apply crt_num_steps. eauto. }
    { apply rt_refl.  }
    eauto. 
  Admitted. 
  
  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI) (WFL: Wf_local SGI):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI /\
           Wf_local SGO. 
  Proof.
    forward eapply (compiled_by_program) as SGI_COMP; eauto.
    red in SGI_COMP. destruct SGI_COMP as [_ [ev_blocks [BLOCKS_OF_SGI COMP_EVENTS_BLOCKS]]].
    set (n_osteps := length ev_blocks).
    red in ExI. destruct ExI as [sti_fin ExI]. desc.
    apply (@crt_num_steps _ (step tid) (init PI) sti_fin) in STEPS as [n_isteps ISTEPS].
    assert ((oseq_step tid) ^^ n_osteps (init PI) sti_fin) as OSEQ_STEPS by admit. 
    assert (BY_STEPS: forall i sti_i (INDEX: i <= n_osteps)
                        (STEPS_TO: (oseq_step tid)^^i (init PI) sti_i)
                        (STEPS_FROM: (oseq_step tid)^^(n_osteps - i) sti_i sti_fin),
                 exists sto_i,
                 (Ostep tid)^^i (init PO) sto_i /\
                 mm_similar_states sto_i sti_i ).
    { induction i.
      - intros sti_i _ STEPS_TO STEPS_FROM.
        exists (init PO). split; [basic_solver| ].
        replace (sti_i) with (init PI); [apply init_mm_same; auto| ].
        generalize STEPS_TO. simpl. basic_solver 10.
      - intros sti_i INDEX STEPS_TO STEPS_FROM.
        rewrite step_prev in STEPS_TO.
        destruct STEPS_TO as [sti_i' [STEPS_TO' STEPS_FROM']].
        forward eapply IHi as [sto' [OSTEPS' MM_SIM']]. 
        { omega. }
        { eauto. }
        { apply (@steps_split _ _ _ 1 (n_osteps - S i)); [omega| ].
          eexists. split; eauto. simpl. basic_solver. }
        pose proof (pair_step MM_SIM' STEPS_FROM') as [sto [OSTEP MM_SIM]].
        eexists. split; eauto.
        apply step_prev. eexists; eauto.  }
    forward eapply (BY_STEPS n_osteps sti_fin (Nat.le_refl n_osteps)) as [sto_fin [OSTEPS MM_SIM]].
    { auto. }
    { rewrite Nat.sub_diag. basic_solver. }
    exists (G sto_fin).
    splits.
    { red. exists sto_fin. splits; auto. 
      { apply crt_num_steps. vauto. }
      red. 
      admit. (* prove that we've reached a terminal state *) }
    { red in MM_SIM. desc. vauto. }
    red in MM_SIM. desc. 
    apply (Wfl_subgraph MM_SIM1). vauto.     
  Admitted. 
        
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


  Lemma OPT_VAL: forall {A: Type} (opt: option A), opt <> None <-> exists o, Some o = opt.
  Proof. 
    ins. destruct opt; [vauto | ]. 
    split; [ins| ]. 
    intros [o CONTRA]. vauto.
  Qed.
  
  Lemma find_iff_in {A: Type} (M: IdentMap.t A) k: 
    IdentMap.In k M <-> exists elt, Some elt = IdentMap.find k M. 
  Proof.
    pose proof (@UsualFMapPositive.UsualPositiveMap.Facts.in_find_iff _ M k).
    pose proof OPT_VAL (IdentMap.find k M).
    eapply iff_stepl.
    - eapply H0. 
    - symmetry. eauto.
  Qed. 

  Lemma compilation_implies_omm_premises SGI PI tid
        (EXEC: thread_execution tid PI SGI) (THREAD_PROG: Some PI = IdentMap.find tid ProgI):
    omm_premises_hold SGI.
  Proof.
    red in Compiled. destruct Compiled as [SAME_THREADS COMP_THREADS].
    assert (exists PO : list Instr.t, is_thread_compiled PO PI) as [PO COMP].
    { pose proof (find_iff_in ProgO tid) as find_iff.
      destruct find_iff as [find_iff _].
      forward eapply find_iff.
      { apply SAME_THREADS. apply find_iff_in.
        eauto. }
      intros [PO THREAD_PO]. exists PO. 
      eapply COMP_THREADS; eauto. }
    forward eapply (compiled_by_program); eauto.    
    intros GRAPH_COMPILED.
    red in EXEC. destruct EXEC as [sti_fin [STEPS [TERMINAL G_FIN]]].
    assert (SAME_INSTRS: PI = instrs sti_fin).
    { forward eapply steps_same_instrs. 
      { eexists. eauto. }
      auto. } 
    rewrite SAME_INSTRS in STEPS. eapply oseq_iff_steps in STEPS; eauto.
    rewrite <- SAME_INSTRS in *. 
    2: { eexists. red. rewrite <- SAME_INSTRS. exists PO. split; auto.
         rewrite firstn_all2; auto.
         do 2 red in TERMINAL. rewrite SAME_INSTRS. omega. }
    rewrite crt_num_steps in STEPS. destruct STEPS as [n_osteps OSTEPS]. 
    assert (OMM_PREM_STEPS: forall i sti (INDEX: i <= n_osteps)
                              (REACH: (oseq_step tid) ^^ i (init PI) sti),
               omm_premises_hold (G sti)).
    { admit. }
    rewrite <- G_FIN. 
    apply (OMM_PREM_STEPS n_osteps sti_fin (Nat.le_refl n_osteps) OSTEPS). 
  Admitted.

  Definition restrict_to_thread (tid: thread_id) (G: execution) : execution.
  Admitted. 

  Definition TMP_thread_local_property (P: execution -> Prop) := forall G,
      (forall tid, P (restrict_to_thread tid G)) -> P G.
  (* Definition TMP_thread_local_property (P: execution -> Prop) := forall G, *)
  (*     (forall tid SG (TE: thread_execution G tid SG) (TRE: thread_restricted_execution G tid SG), P SG) -> P G. *)


  Lemma TMP_tl_omm_premises : TMP_thread_local_property omm_premises_hold.
  Proof. Admitted.

  Lemma GI_omm_premises : omm_premises_hold GI.
  Proof.
    (* apply TMP_tl_omm_premises. *)
    apply tl_omm_premises.
    intros tid.
    (* should carefully relate existing single thread graphs and thread_local_property *)
  Admitted. 
      
  Lemma imm_implies_omm:
    ocaml_consistent GI.
  Proof.
    pose proof GI_omm_premises as GI_OMM_PREM. red in GI_OMM_PREM. desc.
    eapply (@OCamlToimm_s.imm_to_ocaml_consistent GI); eauto. 
  Qed.
    
  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    (* pose proof thread_execs  *)
    (* assert (ALL_SGO: forall tid PO PI SGI *)
    (*                    (THREADO: IdentMap.find tid ProgO = Some PO) *)
    (*                    (THREADI: IdentMap.find tid ProgI = Some PI) *)
    (*                    (THREAD_EXEC: thread_execution tid PI SGI), *)
    (*              exists SGO, Othread_execution tid PO SGO /\ *)
    (*                     same_behavior_local SGO SGI /\ Wf_local SGO).  *)
    (* { admit. } *)
    (* should somehow get a list of threads and call merge_thread_graphs *)
    (* also should pass rf and co to resulting graph *)
    assert (exists GO, forall tid PO PI SGI
                    (THREADO: IdentMap.find tid ProgO = Some PO)
                    (THREADI: IdentMap.find tid ProgI = Some PI)
                    (THREAD_EXEC: thread_execution tid PI SGI),
                 exists SGO, Othread_execution tid PO SGO /\
                        same_behavior_local SGO SGI /\ Wf_local SGO /\
                        thread_restricted_execution GO tid SGO) as [GO SUBGRAPHS]. 
    { admit. }
    exists GO.
    split.
    { red. split.
      { admit. (* todo: every graph event is either init or from thread*)
      (* should work after precise single thread graph merge definition *)}
      red in ExecI. destruct ExecI as [EVENTS SGIS].
      intros tid PO THREAD_PO.
      assert (exists PI, Some PI = IdentMap.find tid ProgI) as [PI THREAD_PI].
      { apply find_iff_in.
        red in Compiled. destruct Compiled as [SAME_THREADS _].
        apply SAME_THREADS. apply find_iff_in.
        eauto. }      
      specialize (SGIS tid PI THREAD_PI) as [SGI [TE_I TRE_I]].
      forward eapply (SUBGRAPHS tid PO PI SGI); auto.
      intros [SGO [TE_O [SAME_BEH [WFO TRE_O]]]].
      eexists. eauto. } 
    red.
    splits.
    { apply tl_sbl. intros tid SGO SGI TRE_O TRE_I.
      red. 
      (* show that thread restriction gives an unique graph? *)
      admit. }
    { admit. }
    admit.         
  Admitted.

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI):
    ocaml_consistent GO.
  Proof.
    red in SB. desc. red in SAME_LOCAL. desc.
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { unfold Execution.sb.        
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. 
      rewrite RESTR_EVENTS. 
      basic_solver. }
    assert (SC': Sc GO ≡₁ Sc GI). 
    { rewrite SAME_LAB. auto. }
    assert (HBO': hbo GO ⊆ hbo GI).
    { unfold OCaml.hb. rewrite SC'. apply clos_trans_mori.
      apply union_mori; [rewrite SB'; basic_solver | ].
      hahn_frame. 
      apply union_mori; [rewrite SAME_CO; basic_solver | rewrite EXT_RF; basic_solver]. }
    assert (FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI).
    { unfold fr. rewrite SAME_CO. rewrite <- seqA. apply seq_more; [| basic_solver].
      rewrite EXT_RF.  basic_solver. }
    red. red in OMM_I.
    splits; auto.
    { red. rewrite RESTR_EVENTS, EXT_RF.
      desc. red in Comp.
      rewrite set_interC, <- set_interA.
      rewrite set_inter_minus_r.
      arewrite (R GO ∩₁ E GI ∩₁ RW GI ≡₁ R GO ∩₁ E GI) by rewrite SAME_LAB; basic_solver.
      rewrite codom_eqv1.
      rewrite set_minusE.
      apply set_subset_inter.
      { rewrite set_interC. rewrite SAME_LAB. apply Comp. }
      basic_solver. }
    { admit.  }
    { rewrite HBO', (same_relation_sym SAME_CO). desc.  auto. }
    { unfold fr. rewrite HBO', (same_relation_sym SAME_CO). 
      arewrite (rf GO ⊆ rf GI) by rewrite EXT_RF; auto. 
      auto. desc. auto. }    
    assert (W_RMW: W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
    { rewrite set_minusE.
      apply set_subset_inter_r. split; [basic_solver| ].
      rewrite (WFI.(wf_rmwD)).
      rewrite dom_eqv1. rewrite set_compl_inter.
      unionR left. type_solver. }
    arewrite (rfe GO ⊆ rfe GI).
    { unfold rfe. rewrite SB', EXT_RF.
      apply inclusion_minus_l.
      rewrite rfi_union_rfe at 1. rewrite seq_union_l.
      apply union_mori.        
      { rewrite (WFI.(wf_rfiD)). 
        arewrite (rfi GI ⊆ sb GI).
        apply seq_mori; [ | basic_solver]. 
        apply eqv_rel_mori. apply W_RMW. }
      unfold rfe. basic_solver. }
    arewrite (fre GO ⊆ fre GI).
    { unfold fre. rewrite SB', FR'.
      apply inclusion_minus_l.
      rewrite fri_union_fre at 1. rewrite seq_union_r.
      apply union_mori.        
      { rewrite (WFI.(wf_friD)). 
        arewrite (fri GI ⊆ sb GI).
        rewrite <- seqA. 
        apply seq_mori; [basic_solver |].
        hahn_frame. apply eqv_rel_mori. apply W_RMW. }
      unfold fre. basic_solver. }
    
    arewrite (coe GO ⊆ coe GI).
    { admit. 
      
      (* assert (CO_: forall G, coe G ≡ co G \ coi G). *)
      (* {  *)
      (*   intros. unfold coe. split.  *)

      (*   pose proof (coi_union_coe G).  *)
      (*   rewrite minus_union_l.  *)
      (*   rewrite minusK. basic_solver 10.  *)

      (* unfold coe. rewrite SB', SAME_CO. *)
      (* apply inclusion_minus_l. *)

      (* rewrite coi_union_coe at 1.  *)
      (* apply union_mori.         *)
      (* { arewrite (coi GO ⊆ sb GO). *)
      (*   seq_rewrite <- SB'. basic_solver. } *)
      (* rewrite (same_relation_sym SAME_CO).  *)
      (* rewrite (WFI.(wf_coiD)).  *)
      (* arewrite (coi GI ⊆ sb GI). *)
      (* apply seq_mori; hahn_frame; apply eqv_rel_mori; apply W_RMW. *)

      (* rewrite as equality? *) }
    rewrite SC'. 
    arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
    desc. auto.
  Admitted.

  
  Theorem compilation_correctness: exists (GO: execution),
      ⟪WFO: Wf GO ⟫ /\
      ⟪ExecO: Oprogram_execution OCamlProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.    
    pose proof GO_exists as [GO [OMM_EXEC SAME_BEH]]. (* todo*)
    exists GO.
    pose proof (Wf_subgraph SAME_BEH WFI) as WFO. (* todo *)
    splits; auto.
    apply graph_switch; auto. (* todo *)
    apply (imm_implies_omm). 
  Qed. 

End CompilationCorrectness.       