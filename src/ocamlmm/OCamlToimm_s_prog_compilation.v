From hahn Require Import Hahn.
Require Import Omega.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import imm_common.
Require Import imm_s_hb.
Require Import imm_s.
Require Import OCamlToimm_s_prog. 
Require Import ClosuresProperties. 
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.


Section OCaml_IMM_Compilation.   

  Definition exchange_reg: Reg.t.
    vauto.
  Admitted.      

  Inductive is_instruction_compiled: Prog.Instr.t -> list Prog.Instr.t -> Prop :=
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

  Definition is_thread_block_compiled PO BPI := Forall2 is_instruction_compiled PO BPI. 

  Definition is_thread_compiled PO PI :=
    exists BPI, is_thread_block_compiled PO BPI /\ PI = flatten BPI. 
      
  Definition is_compiled (po: Prog.Prog.t) (pi: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id po <-> IdentMap.In t_id pi ⟫ /\
    ⟪ THREADS_COMPILED: forall thread to ti (TO: Some to = IdentMap.find thread po)
      (TI: Some ti = IdentMap.find thread pi), is_thread_compiled to ti ⟫. 

  Lemma every_instruction_compiled PO BPI (COMP: is_thread_block_compiled PO BPI)
        i instr block (INSTR: Some instr = nth_error PO i)
        (BLOCK: Some block = nth_error BPI i):
    is_instruction_compiled instr block.
  Proof.
    generalize dependent BPI. generalize dependent i.
    generalize dependent instr. generalize dependent block. 
    induction PO.
    - ins.
      assert (forall {A: Type}, nth_error ([]: list A) i = None). 
      { ins. apply nth_error_None. simpl. omega. }
      rewrite H in INSTR. vauto.
    - ins. inversion COMP. subst.
      destruct (NPeano.Nat.zero_or_succ i).
      + subst. simpl in *. congruence.
      + desc. subst. simpl in *. 
        apply (@IHPO block instr m INSTR l' H3 BLOCK). 
  Qed. 

  Lemma compilation_same_length PO BPI (COMP: is_thread_block_compiled PO BPI):
    length PO = length BPI.
  Proof.
    generalize dependent BPI.
    induction PO.
    { ins. inversion COMP. auto. }
    ins. inversion COMP. simpl.
    intuition.
  Qed. 

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

End OCaml_IMM_Compilation.   
