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
      is_thread_compiled (oinstr :: ro) (block ++ ri).

  Definition is_compiled (po: Prog.Prog.t) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id po <-> IdentMap.In t_id pi ⟫ /\
    forall thread to ti (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti), is_thread_compiled to ti.

End OCaml_IMM_Compilation.   

Section SEQ_STEPS.
  
  Definition sublist {A: Type} (l: list A) (start len: nat) := firstn len (skipn start l). 

  Definition on_block st block :=
    ⟪ PROG_BLOCK: block = sublist (instrs st) (pc st) (length block) ⟫ /\
    ⟪ COMP_BLOCK: (exists oinstr, is_instruction_compiled oinstr block) ⟫. 

  Definition at_compilation_block st :=
    (exists block, on_block st block) \/ is_terminal st. 

  Definition oseq_step (tid : thread_id) sti1 sti2 :=
    exists block, on_block sti1 block /\
             (step tid) ^^ (length block) sti1 sti2. 
  
  
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
  Definition is_nonnop_f {A: Type} (labfun: A -> label) ev :=
    andb (is_f labfun ev) (is_ra labfun ev). 
  Notation "'F' G" := (fun a => is_true (is_nonnop_f G.(lab) a)) (at level 1).
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

  Fixpoint seq_nats n := match n with
                         | 0 => []
                         | S n' => seq_nats n' ++ [n']
                         end.
        
  Lemma lt_ind: forall (P: nat -> Prop), P 0 -> (forall n, (forall y, y < n -> P y) -> P n) -> (forall n, P n).
  Proof. 
    intros.
    assert (forall y : nat, y < n -> P y).
    { induction n; [intros; omega| ]. 
      intros. pose proof (H0 n IHn) as Pn.
      apply H0. intros.
      assert (y0 < n) by omega.
      apply IHn. auto. }
    apply H0. auto.
  Qed.

  Lemma oseq_implies_steps st1 st2 tid (OSEQ: (oseq_step tid)＊ st1 st2): 
    (step tid)＊ st1 st2. 
  Proof.
    forward eapply (@hahn_inclusion_exp _ (oseq_step tid)＊ (step tid)＊); eauto.
    apply inclusion_rt_rt2.
    unfold oseq_step.
    red. intros x y [block [_ STEPS]].
    apply crt_num_steps.
    eauto.
  Qed. 

  Lemma block_steps_selection st1 st2 tid n (STEPS: (step tid) ^^ n st1 st2)
        block (BLOCK: on_block st1 block) (ENOUGH: n >= length block):
    exists st', (oseq_step tid) st1 st' /\ (step tid) ^^ (n - length block) st' st2.
  Proof.
    eapply steps_split in STEPS as [st' [STEPS_TO STEPS_FROM]]. 
    2: { forward eapply (le_plus_minus (length block) n) as SPLIT; [omega| ].
         eauto. }
    exists st'. split; auto.
    red. eexists. split; eauto. 
  Qed.
  
  Lemma is_terminal_new st: pc st >= length (instrs st) <-> is_terminal st.
  Proof. Admitted. 
        
  Lemma oseq_continuos st1 st2 tid (OSEQ: (oseq_step tid) st1 st2)
        (COMP: exists PO, is_thread_compiled PO (instrs st1)):
    at_compilation_block st2.
  Proof.
    (* assert (TC_HELPER: (step tid)⁺ st1 st2 -> at_compilation_block st2). *)
    (* 1: { pose proof OSEQ as OSEQ_. *)
    (*      intros TC_ACB. *)
    (*      apply rt_step, oseq_implies_steps in OSEQ.  *)
    (*      apply clos_refl_transE in OSEQ. des; [| apply TC_ACB; auto].  *)
    (*      rewrite <- OSEQ. *)
    (*      red in OSEQ_. desc.  *)
    (*      red. eauto. } *)
    (* intros TC.  *)
    pose proof OSEQ as OSEQ_.
    (* red in OSEQ.  *)
    desc. inversion COMP as [PO_EQ PI_EQ | oinstr block po' pi' PO_EQ PI_EQ]. 
    - apply rt_step in OSEQ. 
      pose proof (oseq_implies_steps OSEQ) as STEPS. 
      apply clos_refl_transE in STEPS. des. 
      { red in OSEQ_. desc. red. rewrite <- STEPS.  eauto. } 
      exfalso.
      apply ct_begin in STEPS. red in STEPS. desc.
      do 2 (red in STEPS; desc).      
      rewrite <- PI_EQ in ISTEP.
      destruct (pc st1); vauto.
    - admit.       
  Admitted.

  (* TODO: update Coq version? *)
  (* this lemma is mentioned on https://coq.inria.fr/library/Coq.Lists.List.html *)
  Lemma skipn_all2 {A: Type} (l: list A) n: length l <= n -> skipn n l = [].
  Proof. Admitted. 

  Lemma sublist_items {A: Type} (whole: list A) start size result (SL: result = sublist whole start size) (FULL: length result = size):
    forall i (INDEX: i < size), nth_error result i = nth_error whole (start + i). 
  Proof.
    (* TODO: simplify? *)
    intros.
    unfold sublist in SL.
    assert (forall {A: Type} (pref res suf: list A) i (INDEX: i < length res), nth_error res i = nth_error (pref ++ res ++ suf) (length pref + i)).
    { intros. induction pref.
      - simpl. symmetry. apply nth_error_app1. auto.
      - simpl. apply IHpref. }
    forward eapply (@H _ (firstn start whole) result (skipn size (skipn start whole))) as H'. 
    { rewrite FULL. eauto. }
    assert (STRUCT: whole = firstn start whole ++ result ++ skipn size (skipn start whole)).
    { rewrite <- (firstn_skipn start whole) at 1.
      cut (result ++ skipn size (skipn start whole) = skipn start whole).
      { intros. congruence. }
      rewrite SL. apply firstn_skipn. }
    rewrite H'. rewrite STRUCT at 4.
    cut (length (firstn start whole) = start); auto.
    apply firstn_length_le.
    destruct (le_lt_dec start (length whole)); auto.
    rewrite skipn_all2 in SL; [| omega]. rewrite firstn_nil in SL.
    rewrite SL in FULL. simpl in FULL. omega. 
  Qed. 

  (* TODO: remove it since exact instruction is known when block_start is called? *)
  Lemma block_start st block instr (BLOCK: on_block st block)
        (AT_PC: Some instr = nth_error (instrs st) (pc st)):
    (exists mode, instr = Prog.Instr.fence mode) \/
    (exists loc expr, instr = Prog.Instr.load Orlx loc expr) \/
    (exists cond loc, instr = Prog.Instr.ifgoto cond loc) \/
    (exists reg expr, instr = Prog.Instr.assign reg expr).
  Proof. 
    red in BLOCK. desc.
    inversion COMP_BLOCK.
    all: subst; simpl in *.
    (* TODO: refactor *)
    - assert (AT_PC1: Some ld = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }      
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      right. left. subst ld. eauto.
    - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [f; st0] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }      
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [f; ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }      
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [f; exc] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }      
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some asn = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [asn] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }      
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      do 3 right. subst asn. eauto. 
    - assert (AT_PC1: Some igt = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [igt] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }      
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      do 2 right. left. subst igt. eauto.
  Qed. 

  Lemma block_mid st block instr (BLOCK: on_block st block)
        (BLOCK_LEN: length block >= 2)
        (AT_PC1: Some instr = nth_error (instrs st) (pc st + 1)):
    (exists loc expr, instr = Prog.Instr.store Orlx loc expr) \/
    (exists loc expr, instr = Prog.Instr.load Osc loc expr) \/
    (exists expr loc, instr = Prog.Instr.update (Prog.Instr.exchange expr) Xpln Osc Osc exchange_reg loc).
  Proof.
    red in BLOCK. desc.
    inversion COMP_BLOCK. 
    all: (rename H into OINSTR; rename H0 into BLOCK_CONTENTS). 
    all: subst block; simpl in *. 
    (* trivial cases for single instruction blocks *)
    all: try omega. 
    (* now only 2-blocks remain*)
    (* TODO: refactor *)
    { assert (AT_PC1': Some st0 = nth_error (instrs st) (pc st + 1)).
      { apply eq_trans with (y := nth_error [f; st0] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with st0; [| congruence]. 
      subst st0. eauto. }
    { assert (AT_PC1': Some ld = nth_error (instrs st) (pc st + 1)).
      { apply eq_trans with (y := nth_error [f; ld] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with ld; [| congruence]. 
      subst ld. eauto. }
    { assert (AT_PC1': Some exc = nth_error (instrs st) (pc st + 1)).
      { apply eq_trans with (y := nth_error [f; exc] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with exc; [| congruence]. 
      subst exc. eauto. }
  Qed. 
    
  Lemma no_acb_between st1 st2 tid block n (STEPS: (step tid) ^^ n st1 st2)
        (BLOCK: on_block st1 block) (LT: n < length block) (NZ: n <> 0):
    not (at_compilation_block st2).
  Proof.    
    assert (SAME_INSTRS: instrs st2 = instrs st1).
    { symmetry. apply steps_same_instrs. eexists. eapply crt_num_steps. eauto. }
    pose proof BLOCK as BLOCK1. 
    red in BLOCK. desc.
    inversion COMP_BLOCK. 
    all: rename H into OINSTR. 
    all: rename H0 into BLOCK_CONTENTS. 
    all: subst block; simpl in *. 
    (* trivial cases for single instruction blocks *)
    all: try (replace (n) with (0) in *; [vauto | omega]).
    (* now only 2-blocks remain*)
    all: replace n with 1 in *; [| omega].
    (* TODO: refactor *)
    { assert (AT_PC1: Some st = nth_error (instrs st1) (pc st1 + 1)).
      { apply eq_trans with (y := nth_error [f; st] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error (instrs st1) (pc st1)).
      { apply eq_trans with (y := nth_error [f; st] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega. 
        eapply sublist_items; eauto. }
      assert (NEXT_PC: pc st2 = pc st1 + 1).
      { apply (same_relation_exp (pow_unit (step tid))) in STEPS.
        red in STEPS. desc. red in STEPS. desc. 
        inversion ISTEP0; auto.
        rewrite II, <- AT_PC in ISTEP. discriminate. }
      
      red. intros ACB2. red in ACB2.
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite NEXT_PC, SAME_INSTRS in TERM2.
           pose proof (nth_error_None (instrs st1) (pc st1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite NEXT_PC, SAME_INSTRS. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    { assert (AT_PC1: Some ld = nth_error (instrs st1) (pc st1 + 1)).
      { apply eq_trans with (y := nth_error [f; ld] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error (instrs st1) (pc st1)).
      { apply eq_trans with (y := nth_error [f; ld] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega. 
        eapply sublist_items; eauto. }
      assert (NEXT_PC: pc st2 = pc st1 + 1).
      { apply (same_relation_exp (pow_unit (step tid))) in STEPS.
        red in STEPS. desc. red in STEPS. desc. 
        inversion ISTEP0; auto.
        rewrite II, <- AT_PC in ISTEP. discriminate. }
      
      red. intros ACB2. red in ACB2.
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite NEXT_PC, SAME_INSTRS in TERM2.
           pose proof (nth_error_None (instrs st1) (pc st1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite NEXT_PC, SAME_INSTRS. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    { assert (AT_PC1: Some exc = nth_error (instrs st1) (pc st1 + 1)).
      { apply eq_trans with (y := nth_error [f; exc] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error (instrs st1) (pc st1)).
      { apply eq_trans with (y := nth_error [f; exc] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega. 
        eapply sublist_items; eauto. }
      assert (NEXT_PC: pc st2 = pc st1 + 1).
      { apply (same_relation_exp (pow_unit (step tid))) in STEPS.
        red in STEPS. desc. red in STEPS. desc. 
        inversion ISTEP0; auto.
        rewrite II, <- AT_PC in ISTEP. discriminate. }
      
      red. intros ACB2. red in ACB2.
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite NEXT_PC, SAME_INSTRS in TERM2.
           pose proof (nth_error_None (instrs st1) (pc st1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite NEXT_PC, SAME_INSTRS. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
  Qed.     
    
  
  (* had to define it separately since otherwise Coq doesn't understand what P is *)
  Definition StepProp n := forall st1 st2 tid (STEPS: (step tid) ^^ n st1 st2)
                             (COMP: exists PO, is_thread_compiled PO (instrs st1))
                             (ACB1: at_compilation_block st1)
                             (ACB2: at_compilation_block st2),
      (oseq_step tid)＊ st1 st2.
  
  Lemma oseq_between_acb: forall n, StepProp n. 
  Proof.
    apply lt_ind.
    { red. intros. apply steps0 in STEPS. rewrite STEPS. apply rt_refl. }
    unfold StepProp in *. intros. desc.
    unfold at_compilation_block in ACB1. desf. 
    2: { destruct n.
         { (* generalize it? *)
           apply steps0 in STEPS. rewrite STEPS. apply rt_refl. }
         forward eapply (@steps_sub _ (step tid) (S n) _ _ 1) as [st' STEP];
           [omega | eauto |].
         apply (same_relation_exp (pow_unit (step tid))) in STEP.
         do 2 (red in STEP; desc).
         cut (None = nth_error (instrs st1) (pc st1)); [congruence| ]. 
         symmetry. apply nth_error_None. red in ACB1. omega. }
    pose proof (le_lt_dec (length block) n) as LEN. destruct LEN.
    { forward eapply block_steps_selection as [st' [OSEQ NEXT_STEPS]]; eauto. 
      forward eapply (oseq_continuos OSEQ) as ACB'; eauto.
      forward eapply H as OSEQ'. 
      2: { eapply NEXT_STEPS. }
      { cut (length block > 0); try omega.
        red in ACB1. desc. destruct COMP_BLOCK; vauto. }
      { replace (instrs st') with (instrs st1); eauto.
        apply steps_same_instrs. exists tid.
        (* remove duplicated proof *)
        red in OSEQ. desc. rewrite crt_num_steps. eexists. eauto. }
      { auto. }
      { auto. }
      apply inclusion_t_rt. apply ct_begin. red.
      eexists. split; eauto. }
    destruct (NPeano.Nat.eq_0_gt_0_cases n). 
    { subst. apply steps0 in STEPS. rewrite STEPS. apply rt_refl. }
    forward eapply (no_acb_between) as NO_ACB2; vauto.
    omega. 
  Qed.

  Lemma oseq_iff_steps fin tid (TERM: is_terminal fin)
        (COMP: exists PO, is_thread_compiled PO (instrs fin)):
    (step tid)＊ (init (instrs fin)) fin <-> (oseq_step tid)＊ (init (instrs fin)) fin.
  Proof.
    split. 
    2: { (*TODO: remove this part? *)
      apply oseq_implies_steps. }
    intros STEPS. apply crt_num_steps in STEPS as [n STEPS]. 
    eapply oseq_between_acb; eauto.
    2: { red. auto. }
    desc. destruct COMP.
    { red. right.
      apply is_terminal_new. 
      simpl. omega. } 
    red. left.
    (* TODO: simplify is_thread_compiled definition *)
    exists block. red. split; eauto.
    simpl. unfold sublist. simpl.
    rewrite <- (Nat.add_0_r (length block)).
    rewrite firstn_app_2. simpl.
    rewrite <- app_nil_end. auto.     
  Qed. 
  
  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI) (WFL: Wf_local SGI):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI /\
           Wf_local SGO. 
  Proof.
    forward eapply (compiled_by_program) as SGI_COMP; eauto.
    red in SGI_COMP. destruct SGI_COMP as [_ [ev_blocks [BLOCKS_OF_SGI COMP_EVENTS_BLOCKS]]].
    red in ExI. destruct ExI as [sti_fin ExI]. desc.
    apply (@crt_num_steps _ (step tid) (init PI) sti_fin) in STEPS as [n_isteps ISTEPS].
    assert (SAME_INSTRS: PI = instrs sti_fin). 
    { replace PI with (instrs (init PI)); auto. 
      apply steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
    assert (exists n_osteps, (oseq_step tid) ^^ n_osteps (init PI) sti_fin) as [n_osteps OSEQ_STEPS]. 
    { apply crt_num_steps.
      forward eapply (oseq_iff_steps tid) as [FOO _]; eauto.
      { rewrite <- SAME_INSTRS. eauto. }
      rewrite <- SAME_INSTRS in FOO. apply FOO.
      apply crt_num_steps. eauto. }
    
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
      (* prove that we've reached a terminal state *)
      (* maybe show that pco -> pci mapping is monotone *)
      admit. }
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

  (* ISW : is_w *)
  (*         (lab *)
  (*            (add (G st') tid (eindex st') *)
  (*               (Aload false ord (RegFile.eval_lexpr (regf st') lexpr) val) ∅ *)
  (*               (DepsFile.lexpr_deps (depf st') lexpr)  *)
  (*               (ectrl st') ∅)) x *)
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
    
  Definition E_bounded n tid: forall st (STEPS: (step tid) ^^ n (init (instrs st)) st),
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
            

  Lemma OMM_PREM_STEPS n: forall st tid (REACH: (oseq_step tid) ^^ n (init (instrs st)) st),
      omm_premises_hold (G st).
  Proof.
    induction n.
    { intros. apply steps0 in REACH. rewrite <- REACH. simpl.
      red. split.
      { (*reuse the same fact for omm *)
        admit. }
      splits.
      all: try basic_solver. }
    intros.
    red. split; [admit | ]. (*reuse the same fact for omm *)
    rewrite step_prev in REACH. destruct REACH as [st' [OSEQ_STEPS' OSEQ_STEP]].
    forward eapply (IHn st' tid) as OMM_PREM'.
    { replace (instrs st') with (instrs st); auto.
      symmetry. 
      eapply (steps_same_instrs).
      exists tid. apply oseq_implies_steps. apply crt_num_steps.
      exists 1. apply (same_relation_exp (pow_unit (oseq_step tid))). eauto. }
    red in OSEQ_STEP. desc. red in OSEQ_STEP. desc.
    
    assert (exists m, (step tid) ^^ m (init (instrs st')) st') as [m STEPS']. 
    { apply crt_num_steps. apply oseq_implies_steps.
      apply crt_num_steps. eexists.
      replace (instrs st') with (instrs st); eauto.
      symmetry. apply steps_same_instrs. exists tid. apply crt_num_steps. eauto. } 
    inversion COMP_BLOCK.
    all: subst block.
    all: simpl in *.
    - apply (same_relation_exp (seq_id_l (step tid))) in OSEQ_STEP0.
      do 2 (red in OSEQ_STEP0; desc).
      assert (AT_PC: Some ld = nth_error (instrs st') (pc st')).
      { apply eq_trans with (y := nth_error [ld] 0); auto.
        rewrite <- (Nat.add_0_r (pc st')). 
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in ISTEP. inversion ISTEP. subst ld.  
      inversion ISTEP0; try (rewrite II in H1; discriminate).
      subst. inversion II. subst. 
      remember (Aload false Orlx (RegFile.eval_lexpr (regf st') lexpr) val) as new_label.
      assert (ADD_LABEL: lab (G st) (ThreadEvent tid (eindex st')) = (Aload false Orlx (RegFile.eval_lexpr (regf st') lexpr) val)).
      { rewrite UG, Heqnew_label. simpl. apply upds. }
      (* indices in IMM graph are continuos, so can subtract 1 *)
      assert (SB_UPD: immediate (sb (G st)) ≡ immediate (sb (G st'))
                                ∪ (fun x y => Events.tid x = tid /\ Events.tid y = tid /\ index x = index y - 1 /\ index y = eindex st')).
      { admit. } 

      splits.
      all: try (seq_rewrite (@label_set_step (@is_sc actid) sc_matcher st' st tid new_label); [| eauto | apply sc_pl | eapply (nonnop_bounded _ _ _ sc_pl); eauto; red; vauto]). 
      all: try (seq_rewrite (@label_set_step (@is_w actid) w_matcher st' st tid new_label); [| eauto | apply w_pl | eapply (nonnop_bounded _ _ _ w_pl); eauto; red; vauto]). 
      all: try (seq_rewrite (@label_set_step (@is_nonnop_f actid) nonnop_f_matcher st' st tid new_label); [| eauto | apply nonnop_f_pl | eapply (nonnop_bounded _ _ _ nonnop_f_pl); eauto; red; vauto]). 
      all: try (seq_rewrite (@label_set_step (@is_acq actid) acq_matcher st' st tid new_label); [| eauto | apply acq_pl | eapply (nonnop_bounded _ _ _ acq_pl); eauto; red; vauto]). 
      all: try (seq_rewrite (@label_set_step (@is_acqrel actid) acqrel_matcher st' st tid new_label); [| eauto | apply acqrel_pl | eapply (nonnop_bounded _ _ _ acqrel_pl); eauto; red; vauto]). 
      all: try (seq_rewrite (@label_set_step (@is_r actid) r_matcher st' st tid new_label); [| eauto | apply r_pl | eapply (nonnop_bounded _ _ _ r_pl); eauto; red; vauto]). 
      all: try (seq_rewrite (@label_set_step (@is_only_rlx actid) orlx_matcher st' st tid new_label); [| eauto | apply orlx_pl | admit ]). 
      all: rewrite Heqnew_label; simpl.
      all: rewrite !set_union_empty_r. 
      all: try (arewrite (rmw (G st) ≡ rmw (G st')); [rewrite UG; simpl; auto |]). 
      all: try rewrite SB_UPD.

      * do 2 case_union _ _. rewrite codom_union.
        seq_rewrite <- (set_union_empty_r (W (G st') ∩₁ Sc (G st'))). 
        apply set_equiv_union.        
        { red in OMM_PREM'. desc. auto. }
        seq_rewrite <- codom_empty. apply codom_rel_more.  
        red. split; [ basic_solver | ]. 
        sin_rewrite (rmw_bibounded _ _ _ STEPS').
        rewrite inclusion_seq_eqv_l.
        red. intros. red in H. desc. omega.  
      * red in OMM_PREM'. desc. auto.
      * case_union _ _. rewrite codom_union. seq_rewrite set_inter_union_r.
        apply set_subset_union.
        { red in OMM_PREM'. desc. auto. }
        forward eapply (@nonnop_bounded _ (@is_w actid) w_matcher) as BW; eauto. 
        { apply w_pl. }
        { red. vauto. }
        red in BW. rewrite BW. 
        red. intros. exfalso.        
        red in H. desc. rewrite <- H0 in H. simpl in H.
        omega.
      * case_union _ _. rewrite codom_union. seq_rewrite set_inter_union_l.
        apply set_subset_union.
        { red in OMM_PREM'. desc. auto. }
        (* TODO: join with previous *)
        forward eapply (@nonnop_bounded _ (@is_sc actid) sc_matcher) as BSC; eauto. 
        { apply sc_pl. }
        { red. vauto. }
        red in BSC. rewrite BSC. 
        red. intros. exfalso.        
        red in H. desc. rewrite <- H in H0. simpl in H0. 
        omega.
    - subst. red in OSEQ_STEP0. destruct OSEQ_STEP0 as [st'' [STEP_TO'' STEP_FROM'']].
      apply (same_relation_exp (seq_id_l (step tid))) in STEP_TO''.
      assert (AT_PC: Some f = nth_error (instrs st') (pc st')).
      { apply eq_trans with (y := nth_error [f; st0] 0); auto.
        rewrite <- (Nat.add_0_r (pc st')). 
        eapply sublist_items; eauto. }
      assert (AT_PC1: Some st0 = nth_error (instrs st') (pc st' + 1)).
      { apply eq_trans with (y := nth_error [f; st0] 1); auto.
        rewrite <- (Nat.add_0_r (pc st')). 
        eapply sublist_items; eauto. rewrite (Nat.add_0_r). auto. }

      red in STEP_TO''. desc. red in STEP_TO''. destruct STEP_TO'' as [SAME_INSTR' [instr' [INSTR' ISTEP']]].  
      rewrite <- AT_PC in INSTR'. inversion INSTR'. subst f.  
      inversion ISTEP'; try (rewrite II in H0; discriminate).

      red in STEP_FROM''. desc. red in STEP_FROM''. destruct STEP_FROM'' as [SAME_INSTR'' [instr'' [INSTR'' ISTEP'']]].
      rewrite UPC in INSTR''.
      replace (instrs st'') with (instrs st') in INSTR''. 
      rewrite <- AT_PC1 in INSTR''. inversion INSTR''. subst st0.
      inversion ISTEP''; try (rewrite II0 in H1; discriminate).
      subst. 
      


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
    rewrite SAME_INSTRS in STEPS.
    eapply oseq_iff_steps in STEPS; eauto.
    rewrite <- SAME_INSTRS in *.    
    2: { eexists. rewrite <- SAME_INSTRS. eauto. }
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
    pose proof GO_exists as [GO [OMM_EXEC SAME_BEH]].
    exists GO.
    pose proof (Wf_subgraph SAME_BEH WFI) as WFO.
    splits; auto.
    apply graph_switch; auto.
    apply (imm_implies_omm). 
  Qed. 

End CompilationCorrectness.       