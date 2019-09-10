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
    ⟪ SAME_THREADS: True ⟫ /\ (* how to compare key sets? *)
    forall thread to ti
      (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti),
      is_thread_compiled to ti.

  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'ORlx' G" := (fun a => is_true (is_only_rlx G.(lab) a)) (at level 1).
  Notation "'Sc' G" := (fun a => is_true (is_sc G.(lab) a)) (at level 1). 
  
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

  Variable GI : execution.
  Variable ProgI: Prog.Prog.t.
  Hypothesis Compiled: is_compiled ProgI ProgO.

  Theorem compilation_correctness:
    forall (GI: execution) sc (ExecI: program_execution ProgI GI) 
      (IPC: imm_s.imm_psc_consistent GI sc),
    exists (GO: execution),
      ⟪ExecO: Oprogram_execution ProgO GO⟫ /\
      ⟪OC: ocaml_consistent GO ⟫ /\
      ⟪SameBeh: same_behavior GO GI⟫.
  Proof.
    ins. 
  Admitted.

  
  
End OCamlMM_TO_IMM_S_PROG.
