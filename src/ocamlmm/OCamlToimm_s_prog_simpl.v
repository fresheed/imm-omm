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
  | Oassign reg expr
           (LABELS : labels = nil)
           (II : instr = Instr.assign reg expr)
           (UPC : s2.(pc) = s1.(pc) + 1)
           (UG : s2.(G) = s1.(G))
           (UINDEX : s2.(eindex) = s1.(eindex))
           (UREGS : s2.(regf) = RegFun.add reg (RegFile.eval_expr s1.(regf) expr) s1.(regf))
           (UDEPS : s2.(depf) = RegFun.add reg (DepsFile.expr_deps s1.(depf) expr) s1.(depf))
           (UECTRL : s2.(ectrl) = s1.(ectrl))
  | Oif_ expr shift
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
  | Oload ord reg lexpr val l
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
  | Ostore ord lexpr expr l v x
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
  | Ofence ord 
          (LABELS : labels = [Afence ord])
          (II : instr = Instr.fence ord)
          (UPC   : s2.(pc) = s1.(pc) + 1)
          (UG    : s2.(G) = add s1.(G) tid s1.(eindex) (Afence ord) ∅ ∅ s1.(ectrl) ∅)
          (UINDEX : s2.(eindex) = s1.(eindex) + dindex)
          (UREGS : s2.(regf) = s1.(regf))
          (UDEPS : s2.(depf) = s1.(depf))
          (UECTRL : s2.(ectrl) = s1.(ectrl))
  | Ocas_un expr_old expr_new xmod ordr ordw reg lexpr val l
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
  | Ocas_suc expr_old expr_new xmod ordr ordw reg lexpr l expected new_value
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
  | Oinc expr_add xmod ordr ordw reg lexpr val l nval
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
  | Oexchange new_expr xmod ordr ordw reg loc_expr old_value loc new_value
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
    | Orlx | Osc => true
    | _ => false
    end. 
  
  Definition is_ocaml_instruction instr :=
    match instr with
    | Instr.assign _ _ | Instr.ifgoto _ _ => true
    | Instr.load mode _ _ | Instr.store mode _ _ => is_ocaml_mode mode
    | _ => false
    end. 

  Definition Othread_execution (tid : thread_id) (insts : list Prog.Instr.t) (pe : execution) :=
    exists s,
      ⟪ STEPS : (Ostep tid)＊ (init insts) s ⟫ /\
      ⟪ TERMINAL : is_terminal s ⟫ /\
      ⟪ PEQ : s.(G) = pe ⟫.

  (* separation should be consistent across all threads *)
  
  Definition is_matching_mode instr mode :=
    match instr with
    | Instr.load md _ _ | Instr.store md _ _ => (mode = md)
    | _ => True
    end. 

  Definition locations_separated prog := forall (loc : Loc.t), exists mode,
        is_ocaml_mode mode /\
        (forall tid PO (INTHREAD: IdentMap.find tid prog = Some PO)
            instr (INPROG: In instr PO),
           is_matching_mode instr mode). 

  Definition OCamlProgram (prog: Prog.Prog.t) :=
    (forall tid PO (INTHREAD: IdentMap.find tid prog = Some PO),
        forallb is_ocaml_instruction PO) /\
    locations_separated prog. 

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

  
Section ThreadSeparatedGraph.
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
    

  Definition same_behavior_local (GO GI: execution) :=
    ⟪RESTR_EVENTS: E GO ≡₁ E GI ∩₁ (RW GI \₁ dom_rel (GI.(rmw))) ⟫ /\
    ⟪SAME_LAB: lab GO = lab GI ⟫. 

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ≡ GI.(rf) ⨾ ⦗set_compl (dom_rel GI.(rmw))⦘⟫.        

  Record thread_separated_graph :=
    {
      Gis: IdentMap.t execution;
      Einit_tsg: actid -> Prop;
      rf_tsg: relation actid;
      co_tsg: relation actid;
      rmw_tsg: relation actid;
    }.

  Definition same_keys {A B: Type} (map1: IdentMap.t A) (map2: IdentMap.t B) := True.
  Goal True. Admitted. 
  
  Definition program_execution_tsg P tsg :=
    ⟪ SAME_KEYS: same_keys P (Gis tsg) ⟫ /\
    ⟪ THREAD_GRAPH_EXEC: forall tid Pi (THREAD_PROG: Some Pi = IdentMap.find tid P)
    Gi (THREAD_GRAPH: Some Gi = IdentMap.find tid tsg.(Gis)),
      thread_execution tid Pi Gi ⟫. 

  Definition Oprogram_execution_tsg P tsg (OCAML_P: OCamlProgram P) :=
    forall tid Pi (THREAD_PROG: Some Pi = IdentMap.find tid P),
    exists Gi, Some Gi = IdentMap.find tid tsg.(Gis) /\
          Othread_execution tid Pi Gi.
  
  Definition same_behavior_tsg TSGO TSGI :=
    (forall tid (THREAD: IdentMap.In tid (Gis TSGO))
       GOi GIi
       (THREAD_GRAPHO: Some GOi = IdentMap.find tid (Gis TSGO))
       (THREAD_GRAPHI: Some GIi = IdentMap.find tid (Gis TSGI)),
        same_behavior_local GOi GIi)
    (* /\ Einit_tsg TSGO ≡₁ Einit_tsg TSGI *)
    /\ co_tsg TSGO ≡ co_tsg TSGI
    /\ rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘. 
       
  Definition g2tsg: execution -> thread_separated_graph. Admitted. 
  Definition tsg2g: thread_separated_graph -> execution. Admitted. 

  Lemma program_execution_defs_equiv P G:
    program_execution P G <-> program_execution_tsg P (g2tsg G).
  Proof. Admitted. 

  Lemma Oprogram_execution_defs_equiv P G (OCAML_P: OCamlProgram P):
    Oprogram_execution OCAML_P G <-> Oprogram_execution_tsg (g2tsg G) OCAML_P. 
  Proof. Admitted.

  Lemma same_behavior_defs_equiv GO GI:
    same_behavior GO GI <-> same_behavior_tsg (g2tsg GO) (g2tsg GI).
  Proof. Admitted. 
    
  Lemma tsg_g_bijection:
    (forall G, tsg2g (g2tsg G) = G) /\
    (forall TSG, g2tsg (tsg2g TSG) = TSG).
  Proof. Admitted. 

  (* tids should be equal *)
  (* tsg should include a fact that Gis are 1thread *)
  Lemma tsg_todo: True. Proof. Admitted.
  
End ThreadSeparatedGraph. 

Section OCamlMM_TO_IMM_S_PROG.

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
  Notation "'hbo'" := (OCaml.hb). 
  Notation "'same_loc' G" := (same_loc G.(lab)) (at level 1).
  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
    
  (* Definition thread_local_property (P: execution -> Prop) := forall G, *)
  (*     (forall tid SG (TRE: thread_restricted_execution G tid SG), P SG) -> P G. *)

  (* Definition thread_local_biproperty (P: execution -> execution -> Prop) := forall G1 G2, *)
  (*     (forall tid SG1 SG2 (TRE1: thread_restricted_execution G1 tid SG1) *)
  (*        (TRE2: thread_restricted_execution G2 tid SG2), P SG1 SG2) ->  *)
  (*     P G1 G2. *)

  Definition omm_premises_hold G :=
    (* separated *)
    (* let Loc_ := fun l x => loc G.(lab) x = Some l in *)
    (* ⟪ LSM : forall l, (Loc_ l \₁ is_init ⊆₁ (ORlx G)  \/  Loc_ l \₁ is_init ⊆₁ (Sc G)) ⟫ /\ *)
    ⟪ WSCFACQRMW : W G ∩₁ Sc G ≡₁ codom_rel (⦗F G ∩₁ Acq G⦘ ⨾ immediate (sb G) ⨾ rmw G) ⟫ /\
    ⟪ RMWSC  : rmw G ≡ ⦗Sc G⦘ ⨾ rmw G⨾ ⦗Sc G⦘ ⟫ /\
    ⟪ WRLXF : W G ∩₁ ORlx G ⊆₁ codom_rel (⦗F G ∩₁ Acqrel G⦘ ⨾ immediate (sb G)) ⟫ /\
    ⟪ RSCF  : R G ∩₁ Sc G ⊆₁ codom_rel (⦗F G ∩₁ Acq G⦘ ⨾ immediate (sb G)) ⟫.

  (* Lemma tl_sbl: thread_local_biproperty same_behavior_local. *)
  (* Proof. Admitted.  *)

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
    sto.(depf) = sti.(depf) /\
    sto.(ectrl) = sti.(ectrl) /\
    sto.(eindex) = sti.(eindex). 
  
  (* Definition next_compilation_block sti (CORR: exists sto, mm_similar_states sto sti) (NOT_END: pc sti < length (instrs sti)) : list Prog.Instr.t. *)
  (* Admitted. *)

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
  
  Lemma pair_step sto sti (MM_SIM: mm_similar_states sto sti)
        tid sti' (OSEQ_STEP: oseq_step tid sti sti'):
    exists sto', Ostep tid sto sto' /\ mm_similar_states sto' sti'.
  Proof.
    red in OSEQ_STEP. destruct OSEQ_STEP as [block [ON_BLOCK STEP]].
    red in ON_BLOCK. desc.
    inversion COMP_BLOCK.
    all: rename H into OINSTR. 
    all: rename H0 into BLOCK_CONTENTS. 
    all: subst; simpl in *. 
    - apply (same_relation_exp (seq_id_l (step tid))) in STEP.
      assert (AT_PC: Some ld = nth_error (instrs sti) (pc sti)).
      { apply eq_trans with (y := nth_error [ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc sti)).
        eapply sublist_items; eauto. }      
      red in STEP. desc. red in STEP. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ].
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.      
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto)
                         (Aload false ord (RegFile.eval_lexpr (regf sti) lexpr) val) ∅
                         (DepsFile.lexpr_deps (depf sti) lexpr) (ectrl sti) ∅;
                         eindex := eindex sto + 1;
                regf := RegFun.add reg val (regf sto);
                depf := RegFun.add reg (eq (ThreadEvent tid (eindex sti))) (depf sto);
                ectrl := ectrl sto |}).
      red in MM_SIM. desc.
      exists sto'. splits.
      { red. exists lbls. red. splits; [subst; simpl; auto| ].
        exists ld. exists 0. splits.
        { (* need to establish pc correspondence between compiled programs *)
          subst. admit. }
        pose proof (@Oload tid lbls sto sto' ld 1 (gt_Sn_O 0) Orlx reg lexpr val l) as OMM_STEP. 
        assert (ord_eq: ord = Orlx). 
        { subst ld. congruence. }
        rewrite ord_eq in *. 
        forward eapply OMM_STEP; (try auto; try congruence). 
        { subst sto'. simpl. rewrite MM_SIM2, MM_SIM3, MM_SIM4, ord_eq. auto. }
        subst sto'. simpl. rewrite MM_SIM5. auto. }
      red. splits.
      { subst sto'. simpl. replace (instrs sti') with (instrs sti); auto. }
      { (* need to prove that subprograms are compiled too *)
        admit. }
      { red. splits.
        { (* subst sto'. unfold add, acts_set. simpl.. simpl. *)
          (* destruct MM-sim further *)          
          admit. }
        { subst sto'. rewrite UG. simpl. red in MM_SIM1. desc.
          congruence. } }
      { subst sto'. rewrite UREGS. simpl. congruence. }
      { subst sto'. rewrite UDEPS. simpl. congruence. }
      { subst sto'. rewrite UECTRL. simpl. congruence. }
      { subst sto'. rewrite UINDEX. simpl. congruence. }
      (* -  *)
      (* ... *)
  Admitted.
  
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
      
  Lemma Wfl_subgraph SG' SG (SB: same_behavior_local SG SG') (WFL: Wf_local SG'): Wf_local SG.
  Proof.  Admitted.
      
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

  Lemma omm_steps_same_instrs sto sto' (STEPS: exists tid, (Ostep tid)＊ sto sto'):
    instrs sto = instrs sto'.
  Proof.
    (* TODO: join with previous*)
    destruct STEPS as [tid STEPS]. apply crt_num_steps in STEPS.
    destruct STEPS as [n STEPS].
    generalize dependent sto'.
    induction n.
    - intros sto' STEPS. simpl in STEPS. generalize STEPS. basic_solver 10.
    - intros sto' STEPS.
      rewrite step_prev in STEPS. destruct STEPS as [sto'' STEPS'']. desc.
      replace (instrs sto) with (instrs sto'').
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

  Lemma oseq_same_instrs st st' (STEPS: exists tid, (oseq_step tid)＊ st st'):
    instrs st = instrs st'.
  Proof.
    apply steps_same_instrs. desc. exists tid.
    apply oseq_implies_steps. auto.
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

  (* TODO: finish definition *)
  Definition is_corrector (corr: list nat) (PO PI: list Prog.Instr.t) :=
    length corr = length PO + 1 /\
    True. 

  Lemma compilation_correction PO PI:
    is_thread_compiled PO PI <-> exists (corrector: list nat),
      ⟪CORR: is_corrector corrector PO PI  ⟫. 
  Proof. Admitted.

  Lemma acb_iff_corr PO PI corr (CORR: is_corrector corr PO PI):
    forall st (INSTRS: instrs st = PI),
      (exists block, on_block st block) \/ pc st = length PI
      <-> (exists i, Some (pc st) = nth_error corr i). 
  Proof. Admitted.

  Lemma next_corr PO PI corr (CORR: is_corrector corr PO PI):
      forall st (INSTRS: instrs st = PI) block (BLOCK: on_block st block),
      exists i, Some (pc st + length block) = nth_error corr i.
  Proof. Admitted. 
        
  Lemma ifgoto_corr PO PI corr (CORR: is_corrector corr PO PI):
      forall cond adr (IN_PROG: In (Instr.ifgoto cond adr) PI),
      In adr corr. 
  Proof. Admitted. 
        
  Lemma oseq_continuos st1 st2 tid (OSEQ: (oseq_step tid) st1 st2)
        (COMP: exists PO, is_thread_compiled PO (instrs st1)):
    at_compilation_block st2.
  Proof.
    red in OSEQ. desc.
    remember (instrs st1) as PI.
    pose proof COMP as COMP_. 
    apply (compilation_correction PO PI) in COMP_. desc.
    pose proof (acb_iff_corr CORR) as IN_CORR'.
    assert (exists i : nat, Some (pc st1) = nth_error corrector i).
    { apply IN_CORR'; eauto. }
    destruct H as [i1 PC1]. 
    forward eapply (next_corr CORR) as [i1' PC1']; eauto.
    assert (PC2: pc st2 = pc st1 + length block
            \/ exists cond adr, block = [Instr.ifgoto cond adr]).
    { admit. }
    assert (SAME_INSTRS: instrs st1 = instrs st2). 
    { apply steps_same_instrs. exists tid. apply crt_num_steps. eauto. }
    assert (BLOCK_STEP: pc st2 = pc st1 + length block -> at_compilation_block st2).
    { intros PC2_BLOCK. rewrite <- PC2_BLOCK in PC1'.
      forward eapply (IN_CORR' st2) as [_ IN_CORR2]; [congruence | ]. 
      forward eapply (IN_CORR2) as IN_CORR2'; eauto.
      destruct IN_CORR2'. 
      { red. left. eauto. }
      red. right. red. apply is_terminal_new. rewrite PC2_BLOCK, <- SAME_INSTRS, <- HeqPI. omega. }
    des.
    { apply BLOCK_STEP. auto. }
    subst. simpl in *.
    apply (same_relation_exp (seq_id_l (step tid))) in OSEQ0.
    do 2 (red in OSEQ0; desc).
    red in OSEQ. desc. 
    assert (AT_PC1: Some (Instr.ifgoto cond adr) = nth_error (instrs st1) (pc st1)).
    { apply eq_trans with (y := nth_error [Instr.ifgoto cond adr] 0); auto.
      rewrite <- (NPeano.Nat.add_0_r (pc st1)).
      eapply sublist_items; eauto. }
    rewrite <- AT_PC1 in ISTEP. injection ISTEP as INSTR_IFGOTO. 
    inversion ISTEP0; try (rewrite II in INSTR_IFGOTO; discriminate).
    subst. injection II. intros. subst. 
    destruct (Const.eq_dec (RegFile.eval_expr (regf st1) expr) 0).
    { apply BLOCK_STEP. auto. }
    forward eapply (ifgoto_corr CORR expr shift) as TO_CORR. 
    { eapply nth_error_In. eauto. }
    specialize (IN_CORR' st2 (eq_sym SAME_INSTRS)) as [_ IN_CORR''].
    forward eapply IN_CORR'' as IN_CORR'''. 
    { pose proof (In_nth_error corrector shift TO_CORR). desc. 
      exists n0. congruence. }
    des.
    { red. eauto. }
    red. right. red. apply is_terminal_new. rewrite IN_CORR''',  <- SAME_INSTRS.
    omega.     
  Admitted.

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

  Lemma compilation_bijective: forall PI PO PO' (COMP: is_thread_compiled PO PI)
                                 (COMP': is_thread_compiled PO' PI),
      PO' = PO. 
  Proof.
  Admitted.

  Lemma firstn_injective {A: Type} (l: list A) x y
        (SAME: firstn x l = firstn y l):
    x = y \/ (x >= length l /\ y >= length l). 
  Proof.
  Admitted. 

  
  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI) (WFL: Wf_local SGI):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI /\
           Wf_local SGO. 
  Proof.
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
    assert (SAME_OINSTRS: PO = instrs sto_fin).
    { replace PO with (instrs (init PO)); auto.
      apply omm_steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
    
    exists (G sto_fin).
    splits.
    { red. exists sto_fin. splits; auto. 
      { apply crt_num_steps. vauto. }
      apply is_terminal_new.
      red in MM_SIM. desc. 
      rewrite (@firstn_all2 _ (pc sti_fin) (instrs sti_fin)) in MM_SIM0; [| auto].
      2: { red in TERMINAL. omega. }
      pose proof (compilation_bijective MM_SIM MM_SIM0) as COMP_BIJ. 
      rewrite <- firstn_all in COMP_BIJ.
      pose proof (firstn_injective (instrs sto_fin) _ _ COMP_BIJ) as PC_CORR.
      desf. omega. }
    { red in MM_SIM. desc. vauto. }
    red in MM_SIM. desc. 
    apply (Wfl_subgraph MM_SIM1). vauto.     
  Qed.

  Lemma same_beh_implies_similar_rels GO GI (SB: same_behavior GO GI):
    ⟪ SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘⟫ /\
    ⟪ SC': Sc GO ≡₁ Sc GI ⟫ /\
    ⟪ FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI ⟫.
  Proof.
    red in SB. desc. red in SAME_LOCAL. desc. 
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { unfold Execution.sb.        
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. 
      rewrite RESTR_EVENTS. 
      basic_solver. }
    splits; auto. 
    { rewrite SAME_LAB. auto. }
    { unfold fr. rewrite SAME_CO. rewrite <- seqA. apply seq_more; [| basic_solver].
      rewrite EXT_RF.  basic_solver. }
  Qed. 

  Lemma empty_inter_minus_same {A: Type} (X Y: A -> Prop):
    X ∩₁ Y ≡₁ ∅ -> X \₁ Y ≡₁ X.
  Proof. 
    ins. red. split; [basic_solver| ].
    red. ins.
    red in H. desc.
    red. split; auto.
    red in H. specialize (H x).
    red. ins. apply H. basic_solver. 
  Qed.

  Lemma same_relation_exp_iff {A: Type} (r r': relation A):
    r ≡ r' <-> (forall x y, r x y <-> r' x y).
  Proof.
    red. split.
    { apply same_relation_exp. }
    ins. red. split.
    all: red; ins; apply H; auto.
  Qed.

  Lemma set_equiv_exp_iff {A : Type} (s s' : A -> Prop):
    s ≡₁ s' <-> forall x : A, s x <-> s' x.
  Proof.
    red. split; [apply set_equiv_exp| ].
    ins. red. split.
    all: red; ins; apply H; auto.
  Qed. 

    
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

  Lemma SAME_INIT GO GI (SB: same_behavior GO GI): forall l, E GO (InitEvent l) <-> E GI (InitEvent l). 
  Proof. Admitted. 

  Lemma ocaml_no_rmw_tmp GO GI (SB: same_behavior GO GI):
    GO.(rmw) ≡ ∅₂.
  Proof. Admitted.

  Definition RWO GI := (RW GI \₁ dom_rel (rmw GI)). 
  
  Lemma same_beh_implies_similar_intrarels GO GI (SB: same_behavior GO GI):
    ⟪DATA_SIM: data GO ≡ restr_rel (RWO GI) (data GI) ⟫ /\
    ⟪CTRL_SIM: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI) ⟫ /\ 
    ⟪ADDR_SIM: addr GO ≡ restr_rel (RWO GI) (addr GI) ⟫ /\
    ⟪SB_SIM: sb GO ≡ restr_rel (RWO GI) (sb GI) ⟫ /\
    ⟪NO_RMWDEP: rmw_dep GO ≡ ∅₂ ⟫.
  Proof. Admitted.     

  Lemma Wf_subgraph GO GI (SB: same_behavior GO GI) (WF: Wf GI): Wf GO.
  Proof.
    pose proof SB as SB'. 
    pose proof (same_beh_implies_similar_rels SB). 
    red in SB. desc. red in SAME_LOCAL. desc.
    symmetry in SAME_CO.
    assert (forall (r1 r2 r3: relation actid), r1 ⊆ r2 -> r1 \ r3 ⊆ r2 \r3) as MINUS_INCL. 
    { ins. basic_solver. }
    assert (forall (r1 r3: relation actid) S1 S2, r1 ≡ ⦗S1⦘ ⨾ r1 ⨾ ⦗S2⦘ -> r1 \ r3 ≡ ⦗S1⦘ ⨾ (r1 \ r3) ⨾ ⦗S2⦘) as MINUS_EQUIV. 
    { ins. seq_rewrite H. basic_solver. }
    (* TODO: should we include addr, ctrl equality in same_behavior? *)
    pose proof (same_beh_implies_similar_intrarels SB'). desc. 
    inversion WF. 
    pose proof (ocaml_no_rmw_tmp SB') as NO_RMW. 
    assert (rf GO ≡ restr_rel (RWO GI) (rf GI)) as RF_SIM. 
    { rewrite EXT_RF. rewrite wf_rfD. rewrite restr_relE.
      rewrite !seqA.
      arewrite (⦗(RWO GI)⦘ ⨾ ⦗W GI⦘ ≡ ⦗W GI⦘).
      { rewrite <- id_inter. apply eqv_rel_more. split; [basic_solver| ].
        apply set_subset_inter_r. split; auto.
        unfold RWO. 
        rewrite wf_rmwD.
        red. ins. red. split; [basic_solver| ]. 
        red. ins. red in H0. desc. apply seq_eqv_lr in H0. desc.
        type_solver. }
      arewrite (⦗R GI⦘ ⨾ ⦗(RWO GI)⦘ ≡ ⦗R GI⦘ ⨾ ⦗set_compl (dom_rel (rmw GI))⦘); [| basic_solver].
      rewrite <- !id_inter. apply eqv_rel_more.
      unfold RWO. 
      seq_rewrite set_inter_minus_r.
      arewrite (R GI ∩₁ RW GI ≡₁ R GI) by basic_solver. }
    split. 
    all: (try seq_rewrite DATA_SIM; try seq_rewrite CTRL_SIM;
          try seq_rewrite ADDR_SIM; try seq_rewrite SB_SIM;
          try seq_rewrite SAME_CO;  try seq_rewrite RF_SIM;
          try seq_rewrite Rex_SAME;
          try seq_rewrite NO_RMW; try seq_rewrite NO_RMWDEP;
          try rewrite SAME_LAB).
    12: { rewrite RESTR_EVENTS.
          rewrite set_interC at 2. 
          rewrite !id_inter.
          rewrite seqA.
          seq_rewrite <- restr_relE.
          arewrite (restr_rel (RWO GI) (restr_rel (RWO GI) (rf GI)) ≡ restr_rel (RWO GI) (rf GI)) by basic_solver.          
          rewrite <- restr_relE.
          rewrite restrC.
          rewrite restr_relE with (d := E GI). rewrite <- wf_rfE.
          basic_solver. }
    all: try vauto.
    9, 17: basic_solver. 
    all: try (apply restr_rel_mori; auto). 
    1: { ins. des.
         specialize (wf_index a b). forward eapply wf_index; auto.
         destruct RESTR_EVENTS as [EGO_EGI _]. red in EGO_EGI.
         splits; auto.
         { specialize (EGO_EGI a H). red in EGO_EGI. desc. auto. } 
         specialize (EGO_EGI b H0). red in EGO_EGI. desc. auto. }
    { rewrite wf_dataD at 1. rewrite restr_seq_eqv_l, restr_seq_eqv_r. auto. }    
    { rewrite wf_addrD at 1. rewrite restr_seq_eqv_l, restr_seq_eqv_r. auto. }    
    { rewrite wf_ctrlD at 1. rewrite restr_seq_eqv_l. auto. }    
    { assert (forall (r1 r2: relation actid) (D: actid -> Prop),
                 restr_rel D r1 ⨾ restr_rel D r2 ⊆ restr_rel D (r1 ⨾ r2)).
      { ins. basic_solver. }
      rewrite H. apply restr_rel_mori; auto. }
    { rewrite wf_rfD at 1. rewrite restr_seq_eqv_l, restr_seq_eqv_r. auto. }
    { apply inclusion_restr_rel_l. auto. }
    { apply funeq_restr. auto. }
    { rewrite restr_relE. rewrite !transp_seq.
      rewrite !transp_eqv_rel. rewrite seqA, <- restr_relE.
      apply functional_restr. auto. }
    1: { rewrite RESTR_EVENTS.
         rewrite set_interC at 1. rewrite !id_inter.
         rewrite seqA. seq_rewrite <- wf_coE.
         rewrite wf_coD at 2.
         assert (forall (r: relation actid) D1 D2, restr_rel D1 (restr_rel D2 r) ≡ restr_rel (D1 ∩₁ D2) r).
         { ins. basic_solver. }
         rewrite wf_coD at 1. 
         rewrite <- !restr_relE. rewrite H.
         apply restr_rel_more; [| basic_solver].
         split; [| basic_solver].
         rewrite set_inter_minus_l.
         rewrite wf_rmwD.
         arewrite (RW GI ∩₁ W GI ≡₁ W GI) by basic_solver.
         apply empty_inter_minus_same.
         type_solver. }
    { ins. specialize (wf_co_total ol).
         forward eapply (@is_total_more _ (E GI ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol)) (E GO ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol))).
         { apply set_equiv_inter; [| basic_solver].
           rewrite RESTR_EVENTS.
           rewrite set_interA. rewrite set_inter_minus_l.
           arewrite (RW GI ∩₁ W GI ≡₁ W GI) by basic_solver.
           rewrite empty_inter_minus_same; [auto| ]. 
           rewrite wf_rmwD. type_solver. }
         { symmetry. eapply SAME_CO. }
         intros [impl _]. apply impl. auto. }
    ins.
    eapply SAME_INIT; eauto. 
    apply wf_init. desc.
    exists b. split; auto.
    apply (proj1 RESTR_EVENTS). auto. 
  Qed. 


  
End OCamlMM_TO_IMM_S_PROG.

Section CompCorrHelpers.
  Lemma GI_1thread_omm_premises tid PO PI (COMP: is_thread_compiled PO PI) Gi
        (EXEC: thread_execution tid PI Gi):
    omm_premises_hold Gi.
  Proof. Admitted.

End CompCorrHelpers. 

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
    
  Lemma events_generation n tid: forall st ev (REACH: (oseq_step tid) ^^ n (init (instrs st)) st),
      E (G st) ev -> exists st1 st2, (oseq_step tid) st1 st2 /\
                               index ev >= eindex st1 /\
                               index ev < eindex st2.
  Proof.
    induction n.
    { intros st x REACH Ex. apply steps0 in REACH.
      rewrite <- REACH in Ex. unfold init, init_execution, acts_set in Ex.
      simpl in Ex. vauto. }
    intros st x REACH Ex.
    forward eapply (oseq_implies_steps) as STEPS.
    { eapply crt_num_steps. eauto. }
    apply crt_num_steps in STEPS as [m STEPS].
    rewrite step_prev in REACH. destruct REACH as [st' [OSEQ_STEPS' OSEQ_STEP]].
    pose proof (E_bounded m tid st STEPS x Ex) as BOUND. red in BOUND.
    apply le_S_gt in BOUND. 
    assert (eindex st' <= eindex st).
    { apply rt_step, oseq_implies_steps in OSEQ_STEP.
      apply eindex_steps_mon in OSEQ_STEP. auto. }
    destruct (le_lt_dec (eindex st') (index x)).
    { exists st'. exists st. splits; auto. }
    replace (instrs st) with (instrs st') in OSEQ_STEPS'.
    2: { apply oseq_same_instrs. exists tid. apply rt_step. auto. }
    forward eapply (IHn); eauto.
    forward eapply (@oseq_implies_steps (init (instrs st')) st' tid) as STEPS'.
    { apply crt_num_steps. eauto. }
    apply crt_num_steps in STEPS'. destruct STEPS' as [m' STEPS']. 
    pose proof (events_continuos m' tid st' STEPS' l).
    apply (step_events_struct m tid st STEPS) in Ex.
    cut (x = ThreadEvent tid (index x)). 
    { intros. congruence. }
    destruct x.
    { exfalso. red in Ex. desc. apply Ex0. vauto. }
    red in Ex. desc. simpl in Ex. vauto. 
  Qed.

  Lemma rmw_sc n: forall st tid (REACH: (oseq_step tid) ^^ n (init (instrs st)) st),
      rmw (G st) ≡ ⦗Sc (G st)⦘ ⨾ rmw (G st) ⨾ ⦗Sc (G st)⦘.
  Proof. 
    induction n.
    { intros. apply steps0 in REACH. rewrite <- REACH. simpl. basic_solver. }
    intros.
    rewrite step_prev in REACH. destruct REACH as [st' [REACH' OSEQ]].
    replace (instrs st) with (instrs st') in REACH'.
    2: { apply oseq_same_instrs. exists tid. apply rt_step. auto. }
    specialize (IHn st' tid REACH').
    red in OSEQ. desc. red in OSEQ. desc.
    (* inversion COMP_BLOCK. *)
    (* all: subst; simpl in *. *)
    (* - apply (same_relation_exp (seq_id_l (step tid))) in OSEQ0. *)
    (*   do 2 (red in OSEQ0; desc).  *)
  Admitted. 
    
  Lemma OMM_PREM_STEPS' n: forall st tid (REACH: (oseq_step tid) ^^ n (init (instrs st)) st),
      omm_premises_hold (G st).
  Proof.
    intros. 
    red. split.
    { admit. }
    forward eapply (oseq_implies_steps) as STEPS.
    { eapply crt_num_steps. eauto. }
    apply crt_num_steps in STEPS as [m STEPS]. 
    splits.
    2: { admit. }
    { cut (W (G st) ∩₁ Sc (G st)
             ⊆₁ codom_rel (⦗F (G st) ∩₁ Acq (G st)⦘ ⨾ immediate (sb (G st)) ⨾ rmw (G st))); [admit| ].
      red. intros. red in H. destruct H as [Wx SCx]. 
      assert (index x < eindex st) as BOUND. 
      { cut (index_bounded (@is_w actid) st); auto. 
        eapply nonnop_bounded; eauto. 
        { instantiate (1:=w_matcher). apply w_pl. }
        red. vauto. } 
      pose proof (events_continuos m tid st STEPS BOUND) as Ex. 
      assert (EQ: x = (ThreadEvent tid (index x))) by admit.
      rewrite <- EQ in *. 
      pose proof (events_generation n tid st x REACH Ex) as [st1 [st2 [OSEQ [IND1 IND2]]]]. 
      do 2 (red in OSEQ; desc).
      inversion COMP_BLOCK.
      all: rename H into OINSTR. 
      all: rename H0 into BLOCK_CONTENTS.
      all: subst; simpl in *.      
      (* - exfalso. apply (same_relation_exp (seq_id_l (step tid))) in OSEQ0. *)
      (*   do 2 (red in OSEQ0; desc). *)
      (*   inversion ISTEP0. (* ; try (rewrite II in *; discriminate).*) *)
      all: admit. }
  Admitted.                


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
    forward eapply (OMM_PREM_STEPS' n_osteps sti_fin tid); [| intros; congruence].
    replace (instrs sti_fin) with PI; auto. 
  Qed.

  Lemma omm_premises_thread_local TSG (OMM_PREM_THREADS: forall tid Gi (THREAD_Gi: Some Gi = IdentMap.find tid (Gis TSG)), omm_premises_hold Gi):
    omm_premises_hold (tsg2g TSG). 
  Proof. Admitted.  

  Lemma GI_omm_premises : omm_premises_hold GI.
  Proof.
    rewrite <- (proj1 tsg_g_bijection). 
    apply omm_premises_thread_local.
    ins.
    apply program_execution_defs_equiv in ExecI.
    red in ExecI.
    (* bug? desf hangs here *)
    destruct ExecI as [SAME_KEYS THREAD_EXEC]. clear ExecI. 
    assert (exists PIi, Some PIi = IdentMap.find tid ProgI) as [PIi PIi_THREAD] by admit.
    red in THREAD_EXEC. specialize (THREAD_EXEC tid PIi PIi_THREAD Gi THREAD_Gi).
    assert (True) by admit. clear H.
    destruct Compiled as [SAME_TIDS TID_COMPILED].
    assert (exists POi, IdentMap.find tid ProgO = Some POi) as [POi POi_THREAD] by admit.
    specialize (TID_COMPILED tid POi PIi POi_THREAD (eq_sym PIi_THREAD)).
    eapply GI_1thread_omm_premises; eauto. 
  Admitted.

  (* currently rlx fences are used as default value for label function *)
  (* it forces us to (temporarily?) assert that there are no actual rlx fence nodes in a graph *)
  Lemma only_nontrivial_fences_workaround:
    F GI ≡₁ (fun a => is_true (is_f GI.(lab) a)). 
  Proof. Admitted.

  Lemma GI_locations_separated: 
    let Loc_ := fun l e => loc (lab GI) e = Some l in
    forall l : location,
      Loc_ l \₁ (fun a : actid => is_init a) ⊆₁ ORlx GI \/
      Loc_ l \₁ (fun a : actid => is_init a) ⊆₁ Sc GI.
  Proof. Admitted. 

  Lemma imm_implies_omm:
    ocaml_consistent GI.
  Proof.
    pose proof GI_omm_premises as GI_OMM_PREM. red in GI_OMM_PREM. desc.
    pose proof GI_locations_separated. 
    rewrite only_nontrivial_fences_workaround in *. 
    eapply (@OCamlToimm_s.imm_to_ocaml_consistent GI); eauto.
  Qed. 

  Lemma TSGO_exists TSGI (TSG_EXECI : program_execution_tsg ProgI TSGI):
    exists TSGO,
    Oprogram_execution_tsg TSGO OCamlProgO /\
    co_tsg TSGO ≡ co_tsg TSGI /\
    rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘ /\
    (forall tid : IdentMap.key,
        IdentMap.In tid (Gis TSGO) ->
        forall GOi GIi : execution,
          Some GOi = IdentMap.find tid (Gis TSGO) ->
          Some GIi = IdentMap.find tid (Gis TSGI) -> same_behavior_local GOi GIi). 
  Proof.
    
  Admitted. 
    
  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    pose proof (proj1 (program_execution_defs_equiv ProgI GI) ExecI) as TSG_EXECI. 
    remember (g2tsg GI) as TSGI.
    cut (exists TSGO, Oprogram_execution_tsg TSGO OCamlProgO /\
                 co_tsg TSGO ≡ co_tsg TSGI /\
                 rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘ /\
                 forall tid (PROG_THREAD: IdentMap.In tid (Gis TSGO))
                   GOi GIi (THREAD_GO: Some GOi = IdentMap.find tid (Gis TSGO))
                   (THREAD_GI: Some GIi = IdentMap.find tid (Gis TSGI)),
                   same_behavior_local GOi GIi
                   ). 
    { intros [TSGO [TSGO_ExecO [CO_SAME [RF_SIM GOis_sbl]]]]. desc.      
      exists (tsg2g TSGO). 
      split. 
      { apply (proj2 (Oprogram_execution_defs_equiv (tsg2g TSGO) OCamlProgO)).
        rewrite ((proj2 tsg_g_bijection) TSGO). auto. }
      apply ((same_behavior_defs_equiv (tsg2g TSGO) GI)).
      rewrite ((proj2 tsg_g_bijection) TSGO). rewrite <- HeqTSGI.
      red. splits; auto. }    
    apply TSGO_exists; auto. 
  Qed. 

  Lemma restr_rel_empty_minus {T: Type} (r r': relation T) (A B: T -> Prop)
        (NO_INTER: A ∩₁ B ≡₁ ∅):
    restr_rel A r \ restr_rel B r' ≡ r. 
  Proof. Admitted. 
    
  Lemma ocaml_no_rmw GO (ExecO: Oprogram_execution OCamlProgO GO):
    GO.(rmw) ≡ ∅₂.
  Proof. Admitted.

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI)
        (ExecO: Oprogram_execution OCamlProgO GO):
    ocaml_consistent GO.
  Proof.
    pose proof (same_beh_implies_similar_rels SB). 
    red in SB. desc. red in SAME_LOCAL. desc.
    assert (HBO': hbo GO ⊆ hbo GI).
    { unfold OCaml.hb. rewrite SC'. apply clos_trans_mori.
      apply union_mori; [rewrite SB'; basic_solver | ].
      hahn_frame. 
      apply union_mori; [rewrite SAME_CO; basic_solver | rewrite EXT_RF; basic_solver]. }
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
    { red. seq_rewrite ocaml_no_rmw; auto. basic_solver. }
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
    
    arewrite (coe GO ≡ coe GI).
    { unfold coe.      
      rewrite SB', <- SAME_CO.
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

    rewrite SC'. 
    arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
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