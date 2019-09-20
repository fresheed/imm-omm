(******************************************************************************)
(** * OCaml MM is weaker than IMM_S   *)
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

  Inductive is_thread_block_compiled : list Prog.Instr.t -> list (list Prog.Instr.t) -> Prop :=
  | compiled_empty: is_thread_block_compiled [] []
  | compiled_Rna lhs loc ro ri (rest: is_thread_block_compiled ro ri):
      let ld := (Instr.load Orlx lhs loc) in
      is_thread_block_compiled (ro ++ [ld]) (ri ++ [[ld]])
  | compiled_Wna loc val ro ri (rest: is_thread_block_compiled ro ri):
      let st := (Instr.store Orlx loc val) in
      let f := (Instr.fence Oacqrel) in
      is_thread_block_compiled (ro ++ [st]) (ri ++ [[f; st]])
  | compiled_Rat lhs loc ro ri (rest: is_thread_block_compiled ro ri):
      let ld := (Instr.load Osc lhs loc) in
      let f := (Instr.fence Oacq) in
      is_thread_block_compiled (ro ++ [ld]) (ri ++ [[f; ld]])
  | compiled_Wat loc val ro ri (rest: is_thread_block_compiled ro ri):
      let st := (Instr.store Osc loc val) in
      let exc := (Instr.update (Instr.exchange val) Xpln Osc Osc exchange_reg loc) in
      let f := (Instr.fence Oacq) in
      is_thread_block_compiled (ro ++ [st]) (ri ++ [[f; exc]])
  | compiled_assign lhs rhs ro ri (rest: is_thread_block_compiled ro ri):
      let asn := (Instr.assign lhs rhs) in
      is_thread_block_compiled (ro ++ [asn]) (ri ++ [[asn]])
  | compiled_ifgoto e n ro ri (rest: is_thread_block_compiled ro ri):
      let igt := (Instr.ifgoto e n) in
      is_thread_block_compiled (ro ++ [igt]) (ri ++ [[igt]]). 
  

  Definition is_compiled (po: Prog.Prog.t) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id po <-> IdentMap.In t_id pi ⟫ /\
    forall thread to ti (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti), exists block_ti, flatten block_ti = ti /\ is_thread_block_compiled to block_ti.

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

  Definition tmp BPI' :=
    forall PI' (BLOCKS: flatten BPI' = PI')
      tid GI' (EXECI: thread_execution tid PI' GI') (WFLI: Wf_local GI')
      PO' (COMP': is_thread_block_compiled PO' BPI'),
    exists GO', Othread_execution tid PO' GO' /\
           same_behavior_local GO' GI' /\
           Wf_local GO'.

  Lemma compilation_same_length PO BPI (COMP: is_thread_block_compiled PO BPI):
    length PO = length BPI.
  Proof.
    induction COMP.
    { auto. }
    all: do 2 rewrite app_length; rewrite IHCOMP; auto.
  Qed.

  Record block_state := 
    {
      binstrs : list (list Instr.t);
      bpc : nat;
      G' : execution;
      eindex' : nat;
      regf' : RegFile.t;
      depf' : DepsFile.t;
      ectrl' : actid -> Prop
    }.

  Definition block_init (binstrs: list (list Instr.t)) :=
    {|
      binstrs := binstrs;
      bpc := 0;
      G' := init_execution;
      eindex' := 0;
      regf' := RegFile.init;
      depf' := DepsFile.init;
      ectrl' := ∅ |}. 

  Inductive step_seq : thread_id -> list ((list label)*Prog.Instr.t) -> state -> state -> Prop :=
  | empty_step_seq tid st: step_seq tid [] st st
  | next_step_seq
      tid labels insn cur_st next_st fin_st
      (STEP: istep_ tid labels cur_st next_st insn)
      rest (REST: step_seq tid rest next_st fin_st):
      step_seq tid ((labels,insn)::rest) cur_st fin_st.

  Definition bst2st bsti := 
    {|
      instrs := flatten bsti.(binstrs);
      pc := length (flatten (firstn bsti.(bpc) bsti.(binstrs)));
      G := bsti.(G');
      eindex := bsti.(eindex');
      regf := bsti.(regf');
      depf := bsti.(depf');
      ectrl := bsti.(ectrl');
    |}. 
    
  (* Definition st2bst st  -> block_state. *)
  (* Admitted.  *)

  Definition block_istep tid (labels_blocks: list (list label)) bst1 bst2 :=
    ⟪ INSTRS : bst1.(binstrs) = bst2.(binstrs) ⟫ /\
    ⟪ ISTEP: exists block labelsblocks_insns st1 st2,
        Some block = List.nth_error bst1.(binstrs) bst1.(bpc) /\
        labelsblocks_insns = List.combine labels_blocks block /\
        st1 = bst2st bst1 /\ st2 = bst2st bst2 /\
        step_seq tid labelsblocks_insns st1 st2 ⟫ /\
    ⟪BPC: bst2.(bpc) = bst1.(bpc) + 1 ⟫. 

  Definition block_step (tid : thread_id) bst1 bst2 :=
    exists labels_blocks, block_istep tid labels_blocks bst1 bst2.

  Definition block_similar_states (bst: block_state) (st: state) :=
    flatten bst.(binstrs) = st.(instrs) /\
    flatten (firstn bst.(bpc) bst.(binstrs)) = firstn st.(pc) st.(instrs) /\
    bst.(G') = st.(G) /\
    bst.(regf') = st.(regf). 

  Definition mm_similar_states (sto: state) (bst: block_state) :=
    is_thread_block_compiled sto.(instrs) bst.(binstrs)  /\
    sto.(pc) = bst.(bpc) /\
    is_thread_block_compiled (firstn sto.(pc) sto.(instrs)) (firstn bst.(bpc) bst.(binstrs)) /\
    same_behavior_local sto.(G) bst.(G') /\
    sto.(regf) = bst.(regf').

  (* Lemma block_step_correspondence tid bsti bsti' (BSTEP: block_step tid bsti bsti') *)
  (*       block (BLOCK: Some block = List.nth_error bsti.(binstrs) bsti.(bpc)): *)
  (* exists instr, is_thread_block_compiled [instr] [block].  *)
  (* Proof. *)
  Lemma block_step_correspondence i sto bsti (MM_SIM: mm_similar_states sto bsti) (INDEX: i < length bsti.(binstrs)) block (BLOCK: Some block = List.nth_error bsti.(binstrs) i):
    exists instr, is_thread_block_compiled [instr] [block] /\
             Some instr = List.nth_error sto.(instrs) i. 
  Proof.
    (* red in MM_SIM. desc. *)
    (* induction MM_SIM. *)
    (* - simpl in INDEX. omega. *)
    (* - apply IHMM_SIM.  *)
  Admitted. 

  Lemma pair_step sto bsti (MM_SIM: mm_similar_states sto bsti)
        tid bsti' (BSTEP: block_step tid bsti bsti'):
    exists sto', Ostep tid sto sto' /\ mm_similar_states sto' bsti'.
  Proof.
    assert (LT: bsti.(bpc) < length bsti.(binstrs)) by admit. 
    pose proof (block_step_correspondence MM_SIM LT).  (* as [instr CORR].  *)
    (* [lbl_bs [sti [sti' [BLOCK [YYY [CONV [CONV' ZZZ]]]]]]] *)
    destruct BSTEP as [labels_blocks [XXXX [[block [lbl_bs [sti [sti' [BLOCK [YYY [CONV [CONV' ZZZ]]]]]]]] BPC']]]. 
    destruct (H block BLOCK) as [oinstr [BLOCK_COMP OINDEX]].
    inversion BLOCK_COMP.
    - assert (ONLYO: ro = []).
      { destruct ro; auto.
        simpl in H1. inversion H1.
        apply app_eq_nil in H4. desc. discriminate. }
      assert (ri = []) by admit.
      rewrite ONLYO in H1. rewrite H0 in H2. simpl in *.
      injection H1. injection H2. intros.
      assert (LEN_MATCH: length labels_blocks = length block) by admit. 
      rewrite <- H3 in YYY.
      assert (exists lbls, lbl_bs = [ (lbls, ld) ]).
      { unfold combine in YYY. destruct labels_blocks.
        - rewrite <- H3 in LEN_MATCH. simpl in LEN_MATCH. discriminate.
        - simpl in YYY. simpl in YYY.
          rewrite <- H3 in LEN_MATCH. simpl in LEN_MATCH.
          injection LEN_MATCH. intros. apply length_zero_iff_nil in H5.
          rewrite H5 in YYY.
          exists l. auto. }
      destruct H5 as [lbls H5]. rewrite H5 in ZZZ. 
      inversion ZZZ.
      inversion REST.
      rewrite H15 in STEP.
      inversion STEP; try discriminate.
      
      (* eexists. *)
      set (sto' := {|
          instrs := sto.(instrs);
          pc := sto.(pc)+1;
          G := add (G sto) tid (eindex sto)
                   (Aload false ord (RegFile.eval_lexpr (regf sto) lexpr) val) ∅
                   (DepsFile.lexpr_deps (depf sto) lexpr) (ectrl sto) ∅;
          eindex := sto.(eindex) + 1; 
          regf := RegFun.add reg val (regf sto);
          depf := RegFun.add reg (eq (ThreadEvent tid (eindex sto))) (depf sto);
          ectrl := ectrl sto
                  |}).
      exists sto'. 
      split.
      { red. exists lbls. red. split; [admit| ].
        red. exists ld. exists 1.
        split; [admit | ].
        assert (EQlocs: forall loc, RegFile.eval_lexpr (regf sto) loc = RegFile.eval_lexpr (regf sti) loc).
        { intros. unfold bst2st in CONV.
          assert (regf' bsti = regf sti).
          { rewrite CONV. simpl. auto. }
          rewrite <- H13.
          red in MM_SIM. desc. rewrite MM_SIM3. auto. } 
        assert (EQl: l = RegFile.eval_lexpr (regf sto) lexpr).
        { rewrite (EQlocs lexpr). auto.  }
        assert (EQlabels: lbls = [Aload false ord (RegFile.eval_lexpr (regf sto) lexpr) val]).
        { rewrite (EQlocs lexpr). auto. }
        assert (PC': pc sto' = pc sto + 1) by intuition.
        assert (G': G sto' =
                    add (G sto) tid (eindex sto)
                        (Aload false ord (RegFile.eval_lexpr (regf sto) lexpr) val) ∅
                        (DepsFile.lexpr_deps (depf sto) lexpr) (ectrl sto) ∅).
        { subst sto'. auto. }
        assert (EI': eindex sto' = eindex sto + 1) by intuition.
        assert (REG': regf sto' = RegFun.add reg val (regf sto)) by intuition.
        assert (DEPF': depf sto' = RegFun.add reg (eq (ThreadEvent tid (eindex sto))) (depf sto)) by intuition.
        assert (CTRL': ectrl sto' = ectrl sto) by intuition.
        pose proof (@load tid lbls sto sto' ld 1 ord reg lexpr val l EQl II EQlabels PC' G' EI' REG' DEPF' CTRL').
        auto. }
      red.
      splits.
      { assert (instrs sto' = instrs sto) by intuition.
        assert (binstrs bsti' = binstrs bsti) by intuition.
        rewrite H13, H16.
        red in MM_SIM. desc. auto. }
      { replace (pc sto') with (pc sto + 1); [| intuition]. 
        replace (bpc bsti') with (bpc bsti + 1).
        { red in MM_SIM. desc. rewrite MM_SIM0. auto. } } 
      { assert (first_end: forall {A: Type} (l: list A) n x (NTH: Some x = List.nth_error l n), firstn (n + 1) l = firstn n l ++ [x]). 
        { admit. }
        rewrite <- H4 in OINDEX.
        replace (bpc bsti) with (pc sto) in OINDEX.
        2: { red in MM_SIM. intuition. }
        replace (pc sto') with (pc sto + 1); [| intuition]. 
        replace (bpc bsti') with (bpc bsti + 1).
        rewrite (first_end _ (instrs sto') (pc sto) ld OINDEX).
        rewrite <- H3 in BLOCK.
        replace (binstrs bsti') with (binstrs bsti). 
        rewrite (first_end _ (binstrs bsti) (bpc bsti) [ld] BLOCK).
        replace (instrs sto') with (instrs sto) by intuition. 
        apply compiled_Rna.
        red in MM_SIM. desc. auto. }
      { red. 
        
        
      
  Admitted.

  Lemma steps_into_blocks tid sti sti' bsti bsti' (BLOCK_SIM: block_similar_states bsti sti) (BLOCK_SIM': block_similar_states bsti' sti'):
    step tid sti sti' <-> block_step tid bsti bsti'.
  Proof. Admitted. 
      
  Lemma restricted_wf SGI tid (TRI: thread_restricted_execution GI tid SGI): Wf SGI. 
  Proof.
  Admitted.

  Lemma init_blocks_same: forall PI BPI (BLOCK: flatten BPI = PI),
      block_similar_states (block_init BPI) (init PI).
  Proof. ins. Qed. 
    
  Lemma init_mm_same: forall PO BPI (COMP: is_thread_block_compiled PO BPI),
      mm_similar_states (init PO) (block_init BPI).
  Proof.
    ins. red. simpl. splits; auto.
    { apply compiled_empty. }
    red.
    assert (NO_E: E init_execution ≡₁ ∅) by basic_solver. 
    assert (PREPEND_E0: forall S i (IN_E: S ⊆₁ E init_execution), prepend_events S i ≡₁ ∅).
    { intros. split; [| basic_solver].
      red. intros. 
      unfold prepend_events in H.
      destruct x; [auto| ].
      destruct H as [n H]. rewrite NO_E in IN_E. apply IN_E in H. 
      basic_solver. }
    assert (PREPEND_EAPP: forall S i x (IN_E: S ⊆₁ E init_execution), prepend_events S i x -> False).
    { intros. specialize (PREPEND_E0 S i IN_E). red in PREPEND_E0. desc.
      red in PREPEND_E0. specialize (PREPEND_E0 x H). basic_solver. }      
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
    
  Lemma wf_alt G: Wf G <-> Wf_global G /\ (forall tid SG (TRE: thread_restricted_execution G tid SG), Wf_local SG). 
  Proof.
    (* destruct WFG. split; auto. *)
    (* { ins. desc. set (t := tid a). *)
    (*   specialize (WFL t). *)
    (*   admit. } *)
  Admitted.

  Lemma tre_idempotent SG tid G (TRE: thread_restricted_execution G tid SG):
    thread_restricted_execution SG tid SG.
  Proof. Admitted.

  Lemma crt_num_steps {A: Type} (r: relation A) a b: r＊ a b <-> exists n, n >= 0 /\ r ^^ n a b.
  Proof.
    split.
    { ins. rewrite clos_refl_transE in H. destruct H.
      { exists 0. split; auto. simpl. basic_solver. }
      induction H. 
      { exists 1. split; [auto | simpl; basic_solver]. }
      destruct IHclos_trans1 as [n1 IH1]. destruct IHclos_trans2 as [n2 IH2]. 
      exists (n1+n2). split; [omega | ].
      pose proof (@pow_nm _ n1 n2 r) as POW. destruct POW as [POW _].
      specialize (POW x z). apply POW.
      red. exists y. desc. split; auto. }
    ins. destruct H as [n STEPS].
    rewrite clos_refl_transE.
    destruct n.
    { left. desc. simpl in STEPS0. generalize STEPS0. basic_solver 10. }
    right. desc.
    pose proof ctEE. specialize (H _ r). destruct H as [_ POW].
    apply POW. basic_solver. 
  Qed.

  Lemma steps_split {A: Type} (r: relation A) n a b (SPLIT: a + b = n) x y: r^^n x y <-> exists z, r^^a x z /\ r^^b z y.
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
    
  Lemma steps_sub {A: Type} (r: relation A) n x y m (LEQ: m <= n): r^^n x y -> exists z, r^^m x z. 
  Proof.
    ins.
    pose proof (pow_nm m (n-m) r) as STEPS_SPLIT.
    pose proof (same_relation_exp STEPS_SPLIT x y).
    rewrite Const.add_sub_assoc in H0; [| auto]. rewrite minus_plus in H0.
    apply H0 in H. destruct H as [z STEPSz]. desc. 
    eauto. 
  Qed.

  Lemma steps0 {A: Type} (r: relation A) x y: r^^0 x y <-> x = y.
  Proof. simpl. split; basic_solver. Qed.

  Lemma steps_indices {A: Type} (r: relation A) n x y: r^^n x y -> forall i (INDEX: i < n), exists z1 z2, r^^i x z1 /\ r z1 z2.
  Proof.
    intros Rn i LT. 
    assert (LEQ: i + 1 <= n) by omega. 
    pose proof (@steps_sub _ r n x y (i+1) LEQ Rn) as [z2 Ri1].
    pose proof (@steps_split _ r (i+1) i 1 eq_refl x z2).
    apply H in Ri1. destruct Ri1 as [z1 [Ri R1]].
    exists z1. exists z2. split; [auto| ]. 
    apply (same_relation_exp (pow_unit r)). auto.
  Qed. 
    
  Lemma step_prev: forall {A: Type} (r: relation A) x y k, r^^(S k) x y -> exists z, r^^k x z /\ r z y.
  Proof. ins. Qed. 

  Lemma thread_execs: forall tid PO (THREAD_O: IdentMap.find tid ProgO = Some PO)
                        PI (THREAD_I: IdentMap.find tid ProgI = Some PI)
                        SGI (TRI: thread_restricted_execution GI tid SGI)
                        (ExI: thread_execution tid PI SGI), 
      exists SGO, Othread_execution tid PO SGO /\
             same_behavior_local SGO SGI /\
             Wf_local SGO. 
  Proof.
    ins.
    destruct ExI as [sti EXECI]. desc.
    destruct Compiled as [_ COMP_BLOCKS].
    specialize (COMP_BLOCKS tid PO PI THREAD_O THREAD_I).
    destruct COMP_BLOCKS as [BPI [BLOCKS COMP]].
    set (bsti := {| binstrs := BPI;
                   bpc := length BPI;
                   G' := SGI;
                   eindex' := sti.(eindex);
                   regf' := sti.(regf);
                   depf' := sti.(depf);
                   ectrl' := sti.(ectrl); |}).
    assert (BLOCK_STEPS: (block_step tid)＊ (block_init BPI) bsti). 
    { pose proof (steps_into_blocks tid).
      apply crt_num_steps in STEPS. destruct STEPS as [nsteps STEPS].
      induction nsteps eqn:NSTEPS.
      { cut (bsti = block_init BPI).
        { rewrite clos_refl_transE. auto. }
        desc. simpl in STEPS0.
        red in STEPS0. desc.
        pose proof (@init_blocks_same _ _ BLOCKS). red in H0. 
        unfold block_init. subst bsti.
        admit. }
      admit. }
    rewrite crt_num_steps in BLOCK_STEPS. destruct BLOCK_STEPS as [nsteps [GEQ0 BLOCK_STEPS]].

    assert (BSTI_SEQ: forall m (INDEX: m <= nsteps) bsti (MSTEPS: (block_step tid)^^m (block_init BPI) bsti), exists sto, (Ostep tid)^^m (init PO) sto /\ mm_similar_states sto bsti). 
    { intros m. induction m.
      { intros LEQ bsti0 BSTEPS. exists (init PO). split; [apply steps0; auto| ].
        do 2 red in BSTEPS. desc. 
        rewrite <- BSTEPS. apply (init_mm_same COMP). }
      intros LEQ bsti1 SMSTEPS. 
      apply step_prev in SMSTEPS. destruct SMSTEPS as [bsti0 [MSTEPS STEP1]].
      assert (LEQ': m <= nsteps) by omega. 
      destruct (IHm LEQ' bsti0 MSTEPS) as [sto0 [MOSTEPS MM_SIM0]].
      pose proof (@pair_step sto0 bsti0 MM_SIM0 tid bsti1 STEP1) as [sto1 [OSTEP1 MM_SIM1]].
      exists sto1. split; auto.
      rewrite <- Nat.add_1_r. apply <- (@steps_split _ (Ostep tid) (m + 1) _ _ (eq_refl (m+1))).
      exists sto0. split; auto. simpl. basic_solver. }

    destruct (BSTI_SEQ nsteps (Nat.le_refl nsteps) bsti BLOCK_STEPS) as [sto [OSTEPS MM_SIM]].
    exists sto.(G). splits.
    { red. exists sto. splits; auto. 
      { apply crt_num_steps. exists nsteps. desc. split; auto. }
      admit. (* adjust terminal state definition *) }
    { red in MM_SIM. intuition.  }
    admit. (* add Wf_local to lemmas ?*)
  Admitted. 

  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof. Admitted.

  Lemma Wf_subgraph G' G (SB: same_behavior G G') (WF: Wf G'): Wf G.
  Proof.
    (* split. *)
    (* red in SB. desc. red in SAME_LOCAL. desc.  *)
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

  Lemma imm_implies_omm: ocaml_consistent GI.
  Proof. Admitted. 
    
  Theorem compilation_correctness: exists (GO: execution),
      ⟪WFO: Wf GO ⟫ /\
      ⟪ExecO: Oprogram_execution OCamlProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.
    pose proof GO_exists as [GO [OPE EVENTS]].
    exists GO. splits; auto.
    { apply (Wf_subgraph EVENTS WFI). }
    apply graph_switch; auto. 
    apply imm_implies_omm.
  Qed. 
  
  
End OCamlMM_TO_IMM_S_PROG.
