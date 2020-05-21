(******************************************************************************)
(** * ocaml MM is weaker than IMM_S   *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Omega.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
(* Require Import imm_common. *)
Require Import imm_s_hb.
Require Import imm_s.
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.


Section OCaml_Program.

  Inductive Oistep_ tid labels s1 s2 instr dindex: Prop :=
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
                  add s1.(G) tid (s1.(eindex) + dindex) (Aload false ord (RegFile.eval_lexpr s1.(regf) lexpr) val) ∅
                                             (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl) ∅)
         (UINDEX : s2.(eindex) = s1.(eindex) + dindex + 1)
         (UREGS : s2.(regf) = RegFun.add reg val s1.(regf))
         (UDEPS : s2.(depf) = RegFun.add reg (eq (ThreadEvent tid (s1.(eindex) + dindex))) s1.(depf))
         (UECTRL : s2.(ectrl) = s1.(ectrl))
  | Ostore ord lexpr expr l v x
          (L: l = RegFile.eval_lexpr s1.(regf) lexpr)
          (V: v = RegFile.eval_expr  s1.(regf)  expr)
          (X: x = Xpln)
          (LABELS : labels = [Astore x ord l v])
          (II : instr = Instr.store ord lexpr expr)
          (UPC   : s2.(pc) = s1.(pc) + 1)
          (UG    : s2.(G) =
                   add s1.(G) tid (s1.(eindex) + dindex) (Astore x ord l v)
                                              (DepsFile.expr_deps  s1.(depf)  expr)
                                              (DepsFile.lexpr_deps s1.(depf) lexpr) s1.(ectrl) ∅)
          (UINDEX : s2.(eindex) = s1.(eindex) + dindex + 1)
          (UREGS : s2.(regf) = s1.(regf))
          (UDEPS : s2.(depf) = s1.(depf))
          (UECTRL : s2.(ectrl) = s1.(ectrl))
          . 

  Definition Oistep (tid : thread_id) (labels : list label) s1 s2 :=
    ⟪ INSTRS : s1.(instrs) = s2.(instrs) ⟫ /\
    ⟪ ISTEP: exists instr dindex, 
        Some instr = List.nth_error s1.(instrs) s1.(pc) /\
        @Oistep_ tid labels s1 s2 instr dindex⟫.
  
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
 
  (* Definition is_matching_mode instr mode := *)
  (*   match instr with *)
  (*   | Instr.load md _ _ | Instr.store md _ _ => (mode = md) *)
  (*   | _ => True *)
  (*   end. *)

  Definition instr_mode instr :=
    match instr with
    | Instr.load mode _ _ | Instr.store mode _ _ | Instr.fence mode => Some mode
    | Instr.update _ _ _ mode_r mode_w _ _ => Some mode_r (* assume that mode_r = mode_w *)
    | _ => None
    end. 

  Definition instr_locs instr :=
    match instr with
    | Instr.load _ _ lxpr | Instr.store _ lxpr _
    | Instr.update _ _ _ _ _ _ lxpr => match lxpr with
                                  | Instr.lexpr_loc l => [l]
                                  | Instr.lexpr_choice _ l1 l2 => [l1;  l2]
                                  end
    | _ => []
    end. 

  Definition locations_separated prog := forall (loc : Loc.t), exists mode,
        is_ocaml_mode mode /\
        (forall tid PO (INTHREAD: IdentMap.find tid prog = Some PO)
           instr (INPROG: In instr PO)
           (AT_LOC: In loc (instr_locs instr)),
            Some mode = instr_mode instr). 

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
