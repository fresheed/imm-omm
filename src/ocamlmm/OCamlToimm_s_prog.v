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
  | compiled_Rna_alt lhs loc:
      let ld := (Instr.load Orlx lhs loc) in
      is_instruction_compiled (ld) ([ld])
  | compiled_Wna_alt loc val:
      let st := (Instr.store Orlx loc val) in
      let f := (Instr.fence Oacqrel) in
      is_instruction_compiled (st) ([f; st])
  | compiled_Rat_alt lhs loc:
      let ld := (Instr.load Osc lhs loc) in
      let f := (Instr.fence Oacq) in
      is_instruction_compiled (ld) ([f; ld])
  | compiled_Wat_alt loc val:
      let st := (Instr.store Osc loc val) in
      let exc := (Instr.update (Instr.exchange val) Xpln Osc Osc exchange_reg loc) in
      let f := (Instr.fence Oacq) in
      is_instruction_compiled (st) ([f; exc])
  | compiled_assign_alt lhs rhs:
      let asn := (Instr.assign lhs rhs) in
      is_instruction_compiled (asn) ([asn])
  | compiled_ifgoto_alt e n:
      let igt := (Instr.ifgoto e n) in
      is_instruction_compiled (igt) ([igt]).
  
  Inductive is_thread_compiled_alt : list Prog.Instr.t -> list Prog.Instr.t -> Prop :=
  | compiled_empty_alt: is_thread_compiled_alt [] []
  | compiled_add_alt oinstr block ro ri
                     (instr_compiled: is_instruction_compiled oinstr block)
                     (rest: is_thread_compiled_alt ro ri):
      is_thread_compiled_alt (ro ++ [oinstr]) (ri ++ block).

  Definition is_compiled (po: Prog.Prog.t) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id po <-> IdentMap.In t_id pi ⟫ /\
    forall thread to ti (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti), is_thread_compiled_alt to ti.

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
    
  Definition prepend_events (A: actid -> Prop) (shift: nat) := compose A (fun e => ThreadEvent (tid e) (index e + shift)).
  Notation "f '∙' g" := (compose f g) (at level 1). (* default notation is for other scope*)  
    
  Definition same_behavior_local (GO GI: execution) :=
    let Facq' := prepend_events (E GO ∩₁ Sc GO) 2 in
    let Facqrel' := prepend_events (E GO ∩₁ W GO ∩₁ ORlx GO) 2 in
    let R' := prepend_events (E GO ∩₁ W GO ∩₁ Sc GO) 1 in
    
    let rmw_pair r w := (tid r = tid w) /\ (index r = index w - 1) in
    
    let wf_labels :=
        (GI.(lab) = GO.(lab)) /\
        (forall e (FACQ: Facq' e), GI.(lab) e = Afence Oacq) /\
        (forall e (FACQ: Facqrel' e), GI.(lab) e = Afence Oacqrel) /\
        (forall e (R': R' e), exists loc val w,
              GI.(lab) e = Aload true Osc loc val /\
              GO.(lab) w = Astore Xpln Osc loc val /\
              rmw_pair e w) in
    ⟪ADD_EVENTS: E GI ≡₁ E GO ∪₁ Facq' ∪₁ Facqrel' ∪₁ R' ⟫ /\
    ⟪EXT_LABELS: wf_labels ⟫ /\
    ⟪NEW_RMW: GI.(rmw) ≡ fun r w => (E GI ∩₁ R GI ∩₁ Sc GI) r /\ (E GI ∩₁ W GI ∩₁ Sc GI) w /\ rmw_pair r w ⟫.

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ≡ GI.(rf) ⨾ ⦗set_compl (dom_rel GI.(rmw))⦘⟫.
        
  Definition prefix {A: Type} (p l: list A) :=
    exists s, p ++ s = l.
  
  Definition prefix_option {A: Type} (p: list A) (lo: option (list A)):=
    exists l s, lo = Some l /\ p ++ s = l.
  
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
      
  Lemma compilation_same_length PO PI (COMP: is_thread_compiled_alt PO PI):
    exists BPI, length PO = length BPI /\ flatten BPI = PI. 
  Proof.
    (* induction COMP. *)
    (* { auto. } *)
    (* all: do 2 rewrite app_length; rewrite IHCOMP; auto. *)
    (* Qed. *)
  Admitted. 

  Definition mm_similar_states_alt (sto sti: state) :=
    is_thread_compiled_alt sto.(instrs) sti.(instrs)  /\
    is_thread_compiled_alt (firstn sto.(pc) sto.(instrs)) (firstn sti.(pc) sti.(instrs)) /\
    same_behavior_local sto.(G) sti.(G) /\
    sto.(regf) = sti.(regf) /\
    sto.(eindex) = sti.(eindex). 
  
  (* Definition next_compilation_block sti (CORR: exists sto, mm_similar_states_alt sto sti) (NOT_END: pc sti < length (instrs sti)) : list Prog.Instr.t. *)
  (* Admitted. *)
  
  Lemma pair_step_alt sto sti (MM_SIM: mm_similar_states_alt sto sti)
        tid sti' (SEQ_STEP: oseq_step tid sti sti'):
    exists sto', Ostep tid sto sto' /\ mm_similar_states_alt sto' sti'.
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
    
  Lemma group_steps k sti tid (REACH: (step tid) ^^ k (init (instrs sti)) sti)
        (BY_GROUPS: exists PO, is_thread_compiled_alt PO (firstn k sti.(instrs))):
    (oseq_step tid)＊ (init (instrs sti)) sti.
  Proof. Admitted. 
    
  Lemma init_mm_same: forall PO PI (COMP: is_thread_compiled_alt PO PI),
      mm_similar_states_alt (init PO) (init PI).
  Proof.
    (* should shorten it a lot *)
    ins. red. simpl. splits; auto.
    { apply compiled_empty_alt. }
    assert (NO_E: E init_execution ≡₁ ∅) by basic_solver. 
    assert (PREPEND_E0: forall S i (IN_E: S ⊆₁ E init_execution), prepend_events S i ≡₁ ∅).
    { intros. split; [| basic_solver].
      red. intros e.
      intros PREP.
      do 2 red in PREP. apply IN_E in PREP.
      unfold acts_set in PREP. simpl in PREP. auto. }
    assert (PREPEND_EAPP: forall S i x (IN_E: S ⊆₁ E init_execution), prepend_events S i x -> False).
    { intros. specialize (PREPEND_E0 S i IN_E). red in PREPEND_E0. desc.
      red in PREPEND_E0. specialize (PREPEND_E0 x H). basic_solver. }      
    red.
    splits. 
    { rewrite PREPEND_E0; [| basic_solver]. rewrite PREPEND_E0; [| basic_solver].
      rewrite PREPEND_E0; [| basic_solver]. basic_solver. }
    { auto. }
    { intros. exfalso. apply (PREPEND_EAPP ((E init_execution ∩₁ Sc init_execution)) 2 e); [basic_solver | auto]. }
    { intros. exfalso. apply (PREPEND_EAPP ((E init_execution ∩₁ W init_execution ∩₁ ORlx init_execution)) 2 e); [basic_solver | auto]. }
    { intros. exfalso. apply (PREPEND_EAPP (E init_execution ∩₁ W init_execution ∩₁ Sc init_execution) 1 e);  [basic_solver | auto]. }
    simpl. split; [basic_solver|].
    red. intros. desc. red in H. desc. red in H. desc. basic_solver. 
  Qed.

  Lemma thread_execs tid PO PI (COMP: is_thread_compiled_alt PO PI)
        SGI (ExI: thread_execution tid PI SGI):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI /\
           Wf_local SGO. 
  Proof.
    intros.
    destruct ExI as [sti EXECI]. desc.
    set (lenO := length PO). set (lenI := length PI).
    assert (STI_INSTRS: instrs sti = PI) by admit. 
    assert (OSEQ_STEPS: (oseq_step tid)＊ (init PI) sti). 
    { admit. }
    
    apply crt_num_steps in OSEQ_STEPS as [oseq_num OSEQ_REACH]. 
    assert (STO_SEQ: forall k sti_k (INDEX: k <= oseq_num)
                       (CUR_STEPS: (oseq_step tid) ^^ k (init PI) sti_k),
               exists sto_k, (Ostep tid) ^^ k (init PO) sto_k
                        /\ mm_similar_states_alt sto_k sti_k).
    { intros k.
      induction k.
      { exists (init PO). split.
        - basic_solver.
        - do 2 red in CUR_STEPS. desc. rewrite <- CUR_STEPS.
          apply init_mm_same; auto. }
      intros. 
      apply step_prev in CUR_STEPS as [sti_cur [OSEQ_REACH_CUR OSEQ_NEXT]].
      forward eapply (IHk sti_cur).
      { omega. }
      { auto. }
      intros [sto_cur [OSTEP_REACH_CUR MM_SIM_CUR]].
      pose proof (pair_step_alt MM_SIM_CUR OSEQ_NEXT) as [sto_next [OSTEP_NEXT MM_SIM_NEXT]].
      exists sto_next. split; auto.
      apply step_prev. exists sto_cur. split; auto. } 
    
    destruct (@STO_SEQ oseq_num sti (Nat.le_refl oseq_num) OSEQ_REACH) as [sto [osteps_num MM_SIM]].
    exists (G sto).
    splits.
    3: { (* Wf_local for derived sto graph *) admit. }
    2: { red in MM_SIM. desc. vauto. }
    red. exists sto. splits; auto. 
    { apply crt_num_steps. basic_solver 10. }
    red.
    (* why pc should be strictly larger than l? *) admit.
  Admitted. 

  Lemma PREP_NOT_LAST' e sto (PREPS: exists S i, prepend_events S i e /\ S ⊆₁ E (G sto)) (EXISTING_INDICES: forall e', E (G sto) e' -> index e' < eindex sto):
    index e <> eindex sto.
  Proof. 
    intros INDEQ. 
    destruct PREPS as [S [i [PREPS INE]]].
    do 2 red in PREPS. 
    specialize (INE (ThreadEvent (tid e) (index e + i)) PREPS).
    apply EXISTING_INDICES in INE.
    simpl in INE.
    omega.
  Qed.    
    
  Lemma restricted_wf GI SGI tid (WF: Wf GI) (TRI: thread_restricted_execution GI tid SGI): Wf SGI. 
  Proof.
  Admitted.
        
  Lemma wf_split G: Wf G <-> Wf_global G /\ (forall tid SG (TRE: thread_restricted_execution G tid SG), Wf_local SG). 
  Proof.
    (* destruct WFG. split; auto. *)
    (* { ins. desc. set (t := tid a). *)
    (*   specialize (WFL t). *)
    (*   admit. } *)
  Admitted.

  Lemma tre_idempotent SG tid G (TRE: thread_restricted_execution G tid SG):
    thread_restricted_execution SG tid SG.
  Proof. Admitted.


  Lemma Wf_subgraph G' G (SB: same_behavior G G') (WF: Wf G'): Wf G.
  Proof.
    (* split. *)
    (* red in SB. desc. red in SAME_LOCAL. desc.  *)
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
  Variable ProgO ProgI: Prog.Prog.t.
  Hypothesis Compiled: is_compiled ProgO ProgI.
  Hypothesis OCamlProgO: OCamlProgram ProgO.
  
  Variable GI: execution.
  Hypothesis WFI: Wf GI.
  Variable sc: relation actid. 
  Hypothesis ExecI: program_execution ProgI GI.
  Hypothesis IPC: imm_s.imm_psc_consistent GI sc.

  Definition merge_thread_graphs (graphs: list (thread_id * execution)) : execution.
  Admitted. 

  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    pose proof thread_execs.
    assert (ALL_SGO: forall tid PO PI SGI
                       (THREADO: IdentMap.find tid ProgO = Some PO)
                       (THREADI: IdentMap.find tid ProgI = Some PI)
                       (THREAD_EXEC: thread_execution tid PI SGI),
                 exists SGO, Othread_execution tid PO SGO /\
                        same_behavior_local SGO SGI /\ Wf_local SGO). 
    { admit. }
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
      { admit. }
      (* red in ExecI. destruct ExecI. specialize (H1 tid  *)
      (* intros tid PO THREADO. specialize (SUBGRAPHS tid PO).  *)
      admit. 
    } 
    red.
    splits.
    { (* should show that if every thread graph is sbl, then the whole graph is sbl*)
      admit. }
    { admit. }
    admit.     
  Admitted.

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI):
    ocaml_consistent GO.
  Proof.
    assert (E': E GO ≡₁ E GI ∩₁ (RW GI \₁ dom_rel (GI.(rmw)))).
    { admit. }
    red in SB. desc. 
    assert (RF': rf GO ≡ rf GI ⨾ ⦗set_compl (dom_rel (rmw GI))⦘).
    { rewrite EXT_RF. basic_solver. }
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { unfold Execution.sb.        
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. 
      rewrite E'. 
      basic_solver. }
    assert (LAB': GO.(lab) = GI.(lab)).
    { red in SAME_LOCAL. desc. auto. }
    assert (SC': Sc GO ≡₁ Sc GI). 
    { rewrite LAB'. auto. }
    assert (HBO': hbo GO ⊆ hbo GI).
    { unfold OCaml.hb. rewrite SC'. apply clos_trans_mori.
      apply union_mori; [rewrite SB'; basic_solver | ].
      hahn_frame. 
      apply union_mori; [rewrite SAME_CO; basic_solver | rewrite RF'; basic_solver]. }
    assert (CO': co GO ≡ co GI) by intuition.
    assert (FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI).
    { unfold fr. rewrite CO'. rewrite <- seqA. apply seq_more; [| basic_solver].
      rewrite RF'.  basic_solver. }
    red. red in OMM_I.
    splits; auto.
    { red. rewrite E', RF'.
      desc. red in Comp.
      rewrite set_interC, <- set_interA.
      rewrite set_inter_minus_r.
      arewrite (R GO ∩₁ E GI ∩₁ RW GI ≡₁ R GO ∩₁ E GI) by rewrite LAB'; basic_solver.
      rewrite codom_eqv1.
      rewrite set_minusE.
      apply set_subset_inter.
      { rewrite set_interC. rewrite LAB'. apply Comp. }
      basic_solver. }
    { assert (NO_RMW: rmw GO ≡ ∅₂) by admit. 
      red. rewrite NO_RMW. basic_solver. }
    { rewrite HBO', CO'. desc.  auto. }
    { unfold fr. rewrite HBO', CO'. 
      arewrite (rf GO ⊆ rf GI) by rewrite RF'; auto. 
      auto. desc. auto. }    
    assert (W_RMW: W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
    { rewrite set_minusE.
      apply set_subset_inter_r. split; [basic_solver| ].
      rewrite (WFI.(wf_rmwD)).
      rewrite dom_eqv1. rewrite set_compl_inter.
      unionR left. type_solver. }
    arewrite (rfe GO ⊆ rfe GI).
    { unfold rfe. rewrite SB', RF'.
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
    { unfold coe. rewrite SB', CO'. 
      apply inclusion_minus_l.
      rewrite coi_union_coe at 1. 
      apply union_mori.        
      { rewrite (WFI.(wf_coiD)). 
        arewrite (coi GI ⊆ sb GI).
        apply seq_mori; hahn_frame; apply eqv_rel_mori; apply W_RMW. } 
      unfold coe. basic_solver. }
    rewrite SC'. 
    arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
    desc. auto.
  Admitted.
  
  Lemma imm_implies_omm GO (WFO: Wf GO) (SB: same_behavior GO GI):
    ocaml_consistent GI.
  Proof.
    red in SB. desc.
    forward eapply (@OCamlToimm_s.imm_to_ocaml_consistent GI).
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { auto. }
    { eauto. }
    auto. 
  Admitted. 
  
  Theorem compilation_correctness: exists (GO: execution),
      ⟪WFO: Wf GO ⟫ /\
      ⟪ExecO: Oprogram_execution OCamlProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.
    pose proof GO_exists as [GO [OPE EVENTS]].
    exists GO.
    pose proof (Wf_subgraph EVENTS WFI) as WFO. 
    splits; auto.
    apply graph_switch; auto.
    apply (imm_implies_omm WFO); auto.
  Qed. 

End CompilationCorrectness.       