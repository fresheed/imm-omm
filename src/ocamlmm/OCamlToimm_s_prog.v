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

  Inductive is_thread_compiled : Oinstlist -> list Prog.Instr.t -> Prop :=
  | compiled_empty: is_thread_compiled [] []
  | compiled_Rna ord lhs loc ro ri (rest: is_thread_compiled ro ri):
      let ld := (Instr.load ord lhs loc) in
      is_thread_compiled (ld::ro) (ld::ri)
  (* compilation scheme ... *)
  (* id mapping for silent statements*)
  .
  

  Definition is_compiled (po: OProg) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: True ⟫ /\ (* how to compare key sets? *)
    forall thread to ti
      (TO: IdentMap.find thread po = Some to)
      (TI: IdentMap.find thread pi = Some ti),
      is_thread_compiled to ti.

  Definition same_behavior (GO GI: execution) :=
    (* graph correspondence definition *)
    True. 
      
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
  Admitted.

  
  
End OCamlMM_TO_IMM_S_PROG.
