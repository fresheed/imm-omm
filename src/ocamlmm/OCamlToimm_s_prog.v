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

  Inductive Oistep_ tid labels s1 s2 instr dindex : Prop :=
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
    ⟪ ISTEP: exists instr dindex, 
               Some instr = List.nth_error s1.(instrs) s1.(pc) /\
               Oistep_ tid labels s1 s2 instr dindex⟫.    

  Definition Ostep (tid : thread_id) s1 s2 :=
    exists lbls, Oistep tid lbls s1 s2.

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
  

Section OCamlMM_TO_IMM_S_PROG.

  Variable exchange_reg: Reg.t.
  Lemma exchange_reg_dedicated: True.
  Proof.
  Admitted. 

  Inductive is_thread_compiled : list Prog.Instr.t -> list Prog.Instr.t -> Prop :=
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
  

  Definition is_compiled (po: Prog.Prog.t) (pi: Prog.Prog.t) :=
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
  Notation "'R_ex' G" := (fun a => is_true (R_ex G.(lab) a)) (at level 1).
  Notation "'hbo'" := (OCaml.hb). 
  Notation "'same_loc' G" := (same_loc G.(lab)) (at level 1).
  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
  
  Definition prepend_events (s: actid -> Prop) (shift: nat):=
    fun (a: actid) =>
      match a with
      | ThreadEvent tid num => exists orig_num, s (ThreadEvent tid (orig_num + shift))
      | _ => False
      end.

  
  Definition same_behavior_local (GO GI: execution) :=
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
    ⟪ADD_EVENTS: E GI ≡₁ E GO ∪₁ Facq' ∪₁ Facqrel' ∪₁ R' ⟫ /\
    ⟪EXT_LABELS: wf_labels ⟫ /\
    ⟪NEW_RMW: GI.(rmw) ≡ fun r w => (E GI ∩₁ R GI ∩₁ Sc GI) r /\ (E GI ∩₁ W GI ∩₁ Sc GI) w /\ rmw_pair r w ⟫.

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ⊆ GI.(rf)⟫.
    
  
  Variable ProgO ProgI: Prog.Prog.t.
  Hypothesis Compiled: is_compiled ProgO ProgI.
  Hypothesis OCamlProgO: OCamlProgram ProgO.

  Variable GI: execution.
  Hypothesis WFI: Wf GI.
  Variable sc: relation actid. 
  Hypothesis ExecI: program_execution ProgI GI.
  Hypothesis IPC: imm_s.imm_psc_consistent GI sc.

  Definition prefix {A: Type} (p l: list A) :=
    exists s, p ++ s = l.

  Definition prefix_option {A: Type} (p: list A) (lo: option (list A)):=
    exists l s, lo = Some l /\ p ++ s = l.

  Definition kept_events G := ⦗set_compl (dom_rel G.(rmw) ∪₁ F G)⦘.
  
  Theorem correspondence_partial:
    forall (BPI: list (list Prog.Instr.t)) PI (BLOCK_PI: flatten BPI = PI)
      tid SGI (ExI: thread_execution tid PI SGI)
      (INCL_I: prefix_option PI (IdentMap.find tid ProgI))
      PO (INCL_O: prefix_option PO (IdentMap.find tid ProgO))
      (COMP: is_thread_compiled PO PI),
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI. 
  Proof. Admitted.

  Lemma ProgI_blocks: forall tid PI (THREAD: IdentMap.find tid ProgI = Some PI),
      exists BPI, flatten BPI = PI.
  Proof. Admitted. 

  Lemma thread_execs: forall tid PO (THREAD_O: IdentMap.find tid ProgO = Some PO)
                        PI (THREAD_I: IdentMap.find tid ProgI = Some PI)
                        SGI (TRI: thread_restricted_execution GI tid SGI)
                        (ExI: thread_execution tid PI SGI), 
      exists SGO, Othread_execution tid PO SGO /\
             same_behavior_local SGO SGI. 
  Proof.
    ins.    
    assert (BLOCKS: exists BPI, flatten BPI = PI).
    { apply (ProgI_blocks tid THREAD_I). }
    destruct BLOCKS as [BPI BLOCKS].
    apply (correspondence_partial BPI BLOCKS ExI).
    { red. eexists. exists []. rewrite app_nil_r. eauto. }
    { red. eexists. exists []. rewrite app_nil_r. eauto. }
    red in Compiled. destruct Compiled as [_ Comp].
    apply (Comp tid); auto.
  Qed.

  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof. Admitted.

  Record Wf_local (G: execution) :=
    {  wf_index : forall a b, 
        (E G) a /\ (E G) b /\ a <> b /\ tid a = tid b /\ ~ is_init a -> index a <> index b;
       wf_dataD : G.(data) ≡ ⦗R G⦘ ⨾ G.(data) ⨾ ⦗W G⦘ ;
       ctrl_sb : G.(ctrl) ⨾ G.(sb) ⊆ G.(ctrl) ;
       wf_addrD : G.(addr) ≡ ⦗R G⦘ ⨾ G.(addr) ⨾ ⦗RW G⦘ ;
       wf_ctrlD : G.(ctrl) ≡ ⦗R G⦘ ⨾ G.(ctrl) ;
       wf_rmwD : G.(rmw) ≡ ⦗R_ex G⦘ ⨾ G.(rmw) ⨾ ⦗W G⦘ ;
       wf_rmwl : G.(rmw) ⊆ same_loc G ;
       wf_rmwi : G.(rmw) ⊆ immediate G.(sb) ;
       wf_rmw_depD : G.(rmw_dep) ≡ ⦗R G⦘ ⨾ G.(rmw_dep) ⨾ ⦗R_ex G⦘ ;
    }. 

  Record Wf_global (G: execution) :=
    {
       data_in_sb : G.(data) ⊆ G.(sb) ;
       addr_in_sb : G.(addr) ⊆ G.(sb) ;
       ctrl_in_sb : G.(ctrl) ⊆ G.(sb) ;
       rmw_dep_in_sb : G.(rmw_dep) ⊆ G.(sb) ;
       wf_rfE : G.(rf) ≡ ⦗E G⦘ ⨾ G.(rf) ⨾ ⦗E G⦘ ;
       wf_rfD : G.(rf) ≡ ⦗W G⦘ ⨾ G.(rf) ⨾ ⦗R G⦘ ;
       wf_rfl : G.(rf) ⊆ same_loc G;
       wf_rfv : funeq (val G.(lab)) G.(rf) ;
       wf_rff : functional G.(rf)⁻¹ ;
       wf_coE : G.(co) ≡ ⦗E G⦘ ⨾ G.(co) ⨾ ⦗E G⦘ ;
       wf_coD : G.(co) ≡ ⦗W G⦘ ⨾ G.(co) ⨾ ⦗W G⦘ ;
       wf_col : G.(co) ⊆ same_loc G;
       co_trans : transitive G.(co) ;
       wf_co_total : forall ol, is_total (E G ∩₁ W G ∩₁ (fun x => loc G.(lab) x = ol)) G.(co) ;
       co_irr : irreflexive G.(co) ;
       wf_init : forall l, (exists b, E G b /\ loc G.(lab) b = Some l) -> E G (InitEvent l) ;
       wf_init_lab : forall l, G.(lab) (InitEvent l) = Astore Xpln Opln l 0 ;       
    }.

  Lemma wf_split G (WFG: Wf_global G)
        (WFL: forall tid SG (TRE: thread_restricted_execution G tid SG), Wf_local SG):
    Wf G.
  Proof.
    destruct WFG. split; auto.
    { ins. desc. set (t := tid a).
      specialize (WFL t).
      admit. }
  Admitted. 
    
    
  Theorem compilation_correctness: exists (GO: execution),
      ⟪WFO: Wf GO ⟫ /\
      ⟪ExecO: Oprogram_execution OCamlProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.
    pose proof GO_exists as [GO [OPE EVENTS]].
    exists GO. splits; auto.
    { (* TODO: split WF condition to local and global  *)      
      admit. }
    admit. 
    
  Admitted.
  
  
End OCamlMM_TO_IMM_S_PROG.
