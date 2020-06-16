(******************************************************************************)
(** OMM to IMM compilation scheme                                             *)
(******************************************************************************)
From hahn Require Import Hahn.
Require Import Omega.
Require Import Events.
Require Import Execution.
Require Import Execution_eco.
Require Import ClosuresProperties. 
Require Import Prog.
Require Import Utils. 
Require Import ProgToExecution.
Require Import ListHelpers.
Require Import ProgToExecutionProperties.
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.


Section OCaml_IMM_Compilation.   

  (* Reserve the first register to hold read values during exchange instructions *)
  Definition exchange_reg: Reg.t := xH. 

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
      let exc := (Instr.update (Instr.exchange val) false Xpln Osc Osc exchange_reg loc) in
      let f := (Instr.fence Oacq) in
      is_instruction_compiled (st) ([f; exc])
  | compiled_assign lhs rhs:
      let asn := (Instr.assign lhs rhs) in
      is_instruction_compiled (asn) ([asn])
  (* Note that is_instruction_compiled doesn't mean that in the compiled program a given instruction will be replaced with specified block.  *)
  (* ifgoto instruction is an example since eventually the address will be corrected *)
  | compiled_ifgoto e n:
      let igt := (Instr.ifgoto e n) in
      is_instruction_compiled (igt) ([igt]).  

  Inductive address_corrected: list (list Prog.Instr.t) -> Prog.Instr.t -> Prog.Instr.t -> Prop :=
  | corrected_ifgoto BPI0 cond addr0:
      let addr := length (flatten (firstn addr0 BPI0))
      in address_corrected BPI0 (Instr.ifgoto cond addr0) (Instr.ifgoto cond addr)
  | corrected_exact BPI0 instr
                    (NOT_IFGOTO: ~ (match instr with | Instr.ifgoto _ _ => True | _ => False end)):
      address_corrected BPI0 instr instr.

  Definition block_corrected BPI0 block0 block := Forall2 (address_corrected BPI0) block0 block. 
      
  Definition is_thread_block_compiled PO BPI :=
    exists BPI0, Forall2 is_instruction_compiled PO BPI0 /\
            Forall2 (block_corrected BPI0) BPI0 BPI. 

  Definition itbc_weak PO BPI :=
    exists BPI0 BPI0',
      Forall2 is_instruction_compiled PO BPI0 /\
      Forall2 (block_corrected BPI0') BPI0 BPI.

   Lemma correction_same_struct BPI0 BPI ref
         (CORR: Forall2 (block_corrected ref) BPI0 BPI):
     same_struct BPI0 BPI.
   Proof.
     generalize dependent BPI0.
     induction BPI.
     { ins. inversion CORR. red. auto. }
     ins. inversion CORR. subst.
     red. apply Forall2_cons.
     { red in H2. eapply Forall2_length; eauto. }
     apply IHBPI; auto.
   Qed. 

  Definition is_thread_compiled_with PO PI BPI :=
    is_thread_block_compiled PO BPI /\ PI = flatten BPI.

  Definition is_thread_compiled PO PI :=
    exists BPI, is_thread_compiled_with PO PI BPI. 

  Lemma itbc_implies_itbcw PO BPI (COMP: is_thread_block_compiled PO BPI):
    itbc_weak PO BPI.
  Proof.
    red in COMP. red. desc. eauto.
  Qed. 

  Definition is_compiled (ProgO: Prog.Prog.t) (ProgI: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id ProgO <-> IdentMap.In t_id ProgI ⟫ /\
    ⟪ THREADS_COMPILED: forall thread PO PI (TO: Some PO = IdentMap.find thread ProgO)
                          (TI: Some PI = IdentMap.find thread ProgI),
        is_thread_compiled PO PI ⟫.

  Lemma every_instruction_compiled PO BPI (COMP: is_thread_block_compiled PO BPI)
        i instr block (INSTR: Some instr = nth_error PO i)
        (BLOCK: Some block = nth_error BPI i):
    (is_instruction_compiled instr block /\ (~ (match instr with | Instr.ifgoto _ _ => True | _ => False end))) \/
    (exists cond addr0 addr, instr = Instr.ifgoto cond addr0 /\ block = [Instr.ifgoto cond addr]). 
  Proof.
    red in COMP. desc.
    assert (exists block0, Some block0 = nth_error BPI0 i) as [block0 BLOCK0].
    { apply OPT_VAL, nth_error_Some.
      replace (length BPI0) with (length BPI).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length. eauto. }
    cut (is_instruction_compiled instr block0 /\ (block_corrected BPI0) block0 block).
    2: split; eapply Forall2_index; eauto. 
    intros [COMP' BC]. inversion COMP'.
    6: { subst. right. inversion BC. subst.
         inversion H3. subst.
         inversion H1.
         { subst. repeat eexists. }
         subst. exfalso. apply NOT_IFGOTO. subst igt. vauto. }
    all: subst; left; inversion BC; subst; inversion H3; subst; inversion H1; auto.
    all: subst; inversion H5; subst; inversion H2; subst; auto.
  Qed.     

  Lemma compilation_same_length_weak PO BPI (COMP: itbc_weak PO BPI):
    length PO = length BPI.
  Proof.
    red in COMP. desc.
    eapply eq_trans; eapply Forall2_length; eauto. 
  Qed. 

  Lemma compilation_same_length PO BPI (COMP: is_thread_block_compiled PO BPI):
    length PO = length BPI.
  Proof.
    apply compilation_same_length_weak. apply itbc_implies_itbcw. auto.
  Qed. 

  Lemma resulting_block_compiled_weak PO BPI b block
        (COMP : itbc_weak PO BPI)
        (BPI_NE: Forall (fun l : list Instr.t => l <> []) BPI)
        (BLOCK: Some block = nth_error BPI b):
    exists oinstr : Instr.t, is_instruction_compiled oinstr block.
  Proof. 
    red in COMP. desc.
    assert (exists block0, Some block0 = nth_error BPI0 b) as [block0 BLOCK0].
    { apply OPT_VAL, nth_error_Some.
      replace (length BPI0) with (length BPI).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length. eauto. }
    assert (exists oinstr, Some oinstr = nth_error PO b) as [oinstr OINSTR]. 
    { apply OPT_VAL. apply nth_error_Some.
      replace (length PO) with (length BPI).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. apply compilation_same_length_weak. red. eauto. }
    assert (is_instruction_compiled oinstr block0) as COMP_.
    { eapply Forall2_index; eauto. }
    assert (block_corrected BPI0' block0 block) as CORR.
    { eapply Forall2_index; eauto. }
    assert (exists oinstr0 : Instr.t, is_instruction_compiled oinstr0 block) as COMP'.
    { inversion COMP_. 
      6: { subst. inversion CORR. subst. inversion H3. subst.
           inversion H1; vauto. }
      all: (exists oinstr; subst).
      all: (inversion CORR; subst; inversion H3; subst;
            inversion H1; vauto).
      all: (inversion H5; subst; inversion H2; subst; vauto). }
    splits; auto.
  Qed. 

  Lemma resulting_block_compiled PO BPI b block
        (COMP : is_thread_block_compiled PO BPI)
        (BPI_NE: Forall (fun l : list Instr.t => l <> []) BPI)
        (BLOCK: Some block = nth_error BPI b):
    exists oinstr : Instr.t, is_instruction_compiled oinstr block.
  Proof.
    eapply resulting_block_compiled_weak; eauto. eapply itbc_implies_itbcw. eauto. 
  Qed. 

  Lemma COMPILED_NONEMPTY_weak PO BPI (COMP: itbc_weak PO BPI):
    Forall (fun l : list Instr.t => l <> []) BPI.
  Proof.
    apply ForallE. intros block BLOCK.
    apply In_nth_error in BLOCK. desc. symmetry in BLOCK. 
    red in COMP. desc.
    assert (exists block0, Some block0 = nth_error BPI0 n) as [block0 BLOCK0].
    { apply OPT_VAL, nth_error_Some.
      replace (length BPI0) with (length BPI).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length. eauto. }
    cut (block0 <> []).
    2: { assert (exists instr, Some instr = nth_error PO n) as [instr INSTR].
         { apply OPT_VAL, nth_error_Some.
           replace (length PO) with (length BPI0).
           { apply nth_error_Some, OPT_VAL. eauto. }
           symmetry. eapply Forall2_length. eauto. }
         pose proof (Forall2_index COMP _ INSTR BLOCK0).
         inversion H; simpl; vauto. }
    ins. red. ins. red in H. apply H.
    apply length_zero_iff_nil. apply length_zero_iff_nil in H0.
    rewrite <- H0.
    pose proof (Forall2_index COMP0 _ BLOCK0 BLOCK). red in H1.
    eapply Forall2_length; eauto.  
  Qed. 
  
  Lemma COMPILED_NONEMPTY  PO BPI (COMP: is_thread_block_compiled PO BPI):
    Forall (fun l : list Instr.t => l <> []) BPI.
  Proof.
    eapply COMPILED_NONEMPTY_weak. eapply itbc_implies_itbcw. eauto.  
  Qed.

  Lemma progs_positions PO BPI0 BPI b
    (COMPILED: Forall2 is_instruction_compiled PO BPI0)
    (CORRECTED: Forall2 (block_corrected BPI0) BPI0 BPI)
    (IN_PROG: b < length BPI):
    exists oinstr block block0, 
      ⟪OINSTR: Some oinstr = nth_error PO b ⟫/\
      ⟪BLOCK: Some block = nth_error BPI b ⟫/\
      ⟪BLOCK0: Some block0 = nth_error BPI0 b ⟫/\
      ⟪COMP: is_instruction_compiled oinstr block0 ⟫/\
      ⟪CORR: block_corrected BPI0 block0 block ⟫.
  Proof.
    apply nth_error_Some, OPT_VAL in IN_PROG. destruct IN_PROG as [block BLOCK].
    assert (exists block0, Some block0 = nth_error BPI0 b) as [block0 BLOCK0].
    { apply OPT_VAL. apply nth_error_Some.
      replace (length BPI0) with (length BPI).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length; eauto. } 
    assert (exists oinstr, Some oinstr = nth_error PO b) as [oinstr OINSTR]. 
    { apply OPT_VAL. apply nth_error_Some.        
      replace (length PO) with (length BPI0).
      { apply nth_error_Some, OPT_VAL. eauto. }
      symmetry. eapply Forall2_length; eauto. }
    repeat eexists; splits; eauto; eapply Forall2_index; eauto. 
  Qed.

End OCaml_IMM_Compilation.

Section ExprEvaluation.   
  
  Definition value_regs value :=
    match value with
    | Value.const _ => []
    | Value.reg r => [r]
    end. 

  Definition expr_regs expr :=
    match expr with
    | Instr.expr_val val 
    | Instr.expr_op1 _ val => value_regs val
    | Instr.expr_op2 _ val1 val2 => value_regs val1 ++ value_regs val2
    end. 

  Definition lexpr_regs lexpr :=
    match lexpr with
    | Instr.lexpr_loc _ => []
    | Instr.lexpr_choice val _ _ => value_regs val
    end.

  Definition rmw_regs rmw :=
    match rmw with
    | Instr.fetch_add expr => expr_regs expr
    | Instr.cas expr1 expr2 => expr_regs expr1 ++ expr_regs expr2
    | Instr.exchange expr => expr_regs expr
    end. 

  Definition instr_regs instr :=
    match instr with
    | Instr.assign reg expr => reg :: expr_regs expr
    | Instr.load _ reg lexpr => reg :: lexpr_regs lexpr
    | Instr.store _ lexpr expr => lexpr_regs lexpr ++ expr_regs expr
    | Instr.update rmw _ _ _ _ reg lexpr => reg :: rmw_regs rmw ++ lexpr_regs lexpr
    | Instr.fence _ => []
    | Instr.ifgoto expr _ => expr_regs expr
    end.

  Definition exchange_reg_reserved_instr instr :=
    match instr with
    | Instr.assign reg expr => reg <> exchange_reg /\ ~ In exchange_reg (expr_regs expr)
    | Instr.load _ reg lexpr => reg <> exchange_reg /\ ~ In exchange_reg (lexpr_regs lexpr)
    | Instr.store _ lexpr expr => ~ In exchange_reg (expr_regs expr) /\ ~ In exchange_reg (lexpr_regs lexpr)
    | Instr.update rmw _ _ _ _ _ lexpr => ~ In exchange_reg (rmw_regs rmw) /\ ~ In exchange_reg (lexpr_regs lexpr)
    | Instr.ifgoto expr _ => ~ In exchange_reg (expr_regs expr)
    | _ => True
    end.

  Definition exchange_reg_reserved PO := Forall exchange_reg_reserved_instr PO. 

  Lemma exchange_reg_compilation_reserved PO PI
        (REG_RESERVED: exchange_reg_reserved PO)
        (COMP: is_thread_compiled PO PI)
        instr (INSTR: In instr PI):
    exchange_reg_reserved_instr instr. 
  Proof.
    destruct COMP as [BPI COMP]. red in COMP. desc.
    subst. apply in_flatten_iff in INSTR. destruct INSTR as [block [BLOCK INSTR]].
    red in COMP. desc.
    apply In_nth_error in BLOCK. desc.
    forward eapply progs_positions; eauto.
    { eapply nth_error_Some, OPT_VAL. eauto. }
    ins. desc.
    assert (block0 = block) by congruence. subst.
    cut (exchange_reg_reserved block).
    { ins. eapply Forall_forall; eauto. }
    cut (exchange_reg_reserved block1). 
    { ins. red in CORR.
      apply ForallE. intros iinstr IINSTR. apply In_nth_error in IINSTR. desc.
      assert (exists iinstr0, Some iinstr0 = nth_error block1 n0).
      { apply OPT_VAL, nth_error_Some. erewrite Forall2_length; eauto.
        apply nth_error_Some, OPT_VAL. eauto. }
      desc.
      assert (exchange_reg_reserved_instr iinstr0).
      { eapply Forall_forall; eauto. eapply nth_error_In; eauto. }
      forward eapply Forall2_index as ADDR_CORR; eauto.
      inversion ADDR_CORR; vauto. }
    forward eapply (proj1 (Forall_forall exchange_reg_reserved_instr PO) REG_RESERVED) as OINSTR_REG. 
    { eapply nth_error_In; eauto. }
    inversion COMP1; vauto. 
  Qed. 

  Definition lexpr_of lexpr instr :=
    match instr with
    | Instr.load _ _ lexpr' 
    | Instr.store _ lexpr' _ 
    | Instr.update _ _ _ _ _ _ lexpr' => lexpr = lexpr'
    | _ => False
    end.
    
  Definition expr_of expr instr :=
    match instr with 
    | Instr.assign _ expr'
    | Instr.store _ _ expr'
    | Instr.ifgoto expr' _ => expr = expr'
    | _ => False
    end.
  
  Definition rmw_expr_of expr rmw :=
    match rmw with 
    | Instr.exchange expr' 
    | Instr.fetch_add expr' => expr = expr'
    | Instr.cas expr1 expr2 => expr = expr1 \/ expr = expr2
    end.

  Definition safe_reg_of reg instr :=
    match instr with 
    | Instr.assign reg' _
    | Instr.load _ reg' _ => reg = reg'
    | _ => False
    end. 

  
  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  
  Definition RWO GI := (RW GI \₁ dom_rel (rmw GI)). 

  Lemma eval_expr_same st st'
        (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        expr (NOT_EXC: ~ In exchange_reg (expr_regs expr)):
    RegFile.eval_expr (regf st) expr = RegFile.eval_expr (regf st') expr.
  Proof.
    unfold RegFile.eval_expr, RegFile.eval_value, RegFun.find, expr_regs, value_regs in *. 
    destruct expr. 
    - destruct val; vauto. apply REGF_SIM. simpl in NOT_EXC. intuition.
    - destruct op0; vauto. f_equal.
      apply REGF_SIM. simpl in NOT_EXC. intuition.
    - destruct op1, op2; vauto; simpl in NOT_EXC; intuition.
  Qed. 

  Lemma eval_instr_expr PI (REG_RESERVED: exchange_reg_reserved PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        instr (INSTR: In instr PI) expr (EXPR_OF: expr_of expr instr):
    RegFile.eval_expr (regf st) expr = RegFile.eval_expr (regf st') expr.
  Proof.
    apply eval_expr_same; auto.
    eapply Forall_forall in REG_RESERVED; eauto.
    destruct instr; simpl in *; desc; vauto.     
  Qed. 
    
  Lemma eval_lexpr_same st st'
        (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        lexpr (NOT_EXC: ~ In exchange_reg (lexpr_regs lexpr)):
    RegFile.eval_lexpr (regf st) lexpr = RegFile.eval_lexpr (regf st') lexpr.
  Proof.
    destruct lexpr; vauto.
    unfold RegFile.eval_lexpr.
    replace (RegFile.eval_expr (regf st') r) with (RegFile.eval_expr (regf st) r); auto.
    apply eval_expr_same; auto.  
  Qed. 

  Lemma eval_instr_lexpr PI (REG_RESERVED: exchange_reg_reserved PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        instr (INSTR: In instr PI) lexpr (EXPR_OF: lexpr_of lexpr instr):
    RegFile.eval_lexpr (regf st) lexpr = RegFile.eval_lexpr (regf st') lexpr.
  Proof.
    apply eval_lexpr_same; auto.
    eapply Forall_forall in REG_RESERVED; eauto.
    destruct instr; simpl in *; desc; vauto.     
  Qed. 
    
  Lemma eval_rmw_expr PI (REG_RESERVED: exchange_reg_reserved PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        rmw (INSTR: exists rex x orr orw lhs loc, In (Instr.update rmw rex x orr orw lhs loc) PI)
        expr (EXPR_OF: rmw_expr_of expr rmw):
    RegFile.eval_expr (regf st) expr = RegFile.eval_expr (regf st') expr.
  Proof.
    desc. apply eval_expr_same; auto.
    eapply Forall_forall in REG_RESERVED; eauto.
    destruct rmw; simpl in *; desc; vauto.
    des; subst; intuition. 
  Qed. 
    
  Lemma eval_safe_reg PI (REG_RESERVED: exchange_reg_reserved PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        instr (INSTR: In instr PI) reg (SAFE_REG_OF: safe_reg_of reg instr):
    regf st reg = regf st' reg.
  Proof.
    apply REGF_SIM; auto.
    eapply Forall_forall in REG_RESERVED; eauto.
    destruct instr; simpl in *; desc; vauto.     
  Qed.

  Lemma eval_expr_deps_same st st'
        (DEPF_SIM: forall reg (NEXC: reg <> exchange_reg), depf st reg ≡₁ depf st' reg ∩₁ RWO (G st'))
        expr (NOT_EXC: ~ In exchange_reg (expr_regs expr)):
    DepsFile.expr_deps (depf st) expr ≡₁ DepsFile.expr_deps (depf st') expr ∩₁ RWO (G st').
  Proof.
    unfold DepsFile.expr_deps, DepsFile.val_deps. destruct expr; vauto.
    - destruct val; [basic_solver| ]. simpl in NOT_EXC. unfold RegFun.find.
      intuition.
    - destruct op; vauto. destruct op0; [basic_solver| ]. simpl in NOT_EXC. 
      unfold RegFun.find. intuition.
    - destruct op1, op2; vauto; unfold RegFun.find; simpl in NOT_EXC.
      + basic_solver. 
      + remove_emptiness. intuition. 
      + remove_emptiness. intuition.
      + rewrite set_inter_union_l. apply set_equiv_union; intuition. 
  Qed. 
  
  Lemma eval_instr_expr_deps PI (REG_RESERVED: exchange_reg_reserved PI)
        st st' (DEPF_SIM: forall reg (NEXC: reg <> exchange_reg), depf st reg ≡₁ depf st' reg ∩₁ RWO (G st'))
        instr (INSTR: In instr PI) expr (EXPR_OF: expr_of expr instr):
    DepsFile.expr_deps (depf st) expr ≡₁ DepsFile.expr_deps (depf st') expr ∩₁ RWO (G st').
  Proof.
    apply eval_expr_deps_same; auto.
    eapply Forall_forall in REG_RESERVED; eauto.
    destruct instr; simpl in *; desc; vauto.     
  Qed.
  
  Lemma eval_lexpr_deps_same st st'
        (DEPF_SIM: forall reg (NEXC: reg <> exchange_reg), depf st reg ≡₁ depf st' reg ∩₁ RWO (G st'))
        lexpr (NOT_EXC: ~ In exchange_reg (lexpr_regs lexpr)):
    DepsFile.lexpr_deps (depf st) lexpr ≡₁ DepsFile.lexpr_deps (depf st') lexpr ∩₁ RWO (G st').
  Proof.
    unfold DepsFile.lexpr_deps. destruct lexpr; [basic_solver |]. 
    unfold DepsFile.val_deps. destruct r; [basic_solver| ]. 
    unfold RegFun.find. apply DEPF_SIM.  
    red. ins. apply NOT_EXC. vauto.
  Qed. 
    
  Lemma eval_instr_lexpr_deps PI (REG_RESERVED: exchange_reg_reserved PI)
        st st' (DEPF_SIM: forall reg (NEXC: reg <> exchange_reg), depf st reg ≡₁ depf st' reg ∩₁ RWO (G st'))
        instr (INSTR: In instr PI) lexpr (EXPR_OF: lexpr_of lexpr instr):
    DepsFile.lexpr_deps (depf st) lexpr ≡₁ DepsFile.lexpr_deps (depf st') lexpr ∩₁ RWO (G st').
  Proof.
    apply eval_lexpr_deps_same; auto.
    eapply Forall_forall in REG_RESERVED; eauto.
    destruct instr; simpl in *; desc; vauto.     
  Qed.
    
End ExprEvaluation.   


Section OCaml_IMM_Correspondence.
  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).
  
  Record block_state :=
    { binstrs : list (list Instr.t);
      bpc : nat;
      bG : execution;
      beindex : nat;
      bregf : RegFile.t;
      bdepf : DepsFile.t;
      bectrl : actid -> Prop }.

  Definition bst2st bst :=
    {| instrs := flatten (binstrs bst);
       pc := length (flatten (firstn (bpc bst) (binstrs bst)));
       G := bG bst;
       eindex := beindex bst;
       regf := bregf bst;
       depf := bdepf bst;
       ectrl := bectrl bst;      
    |}.

  Definition block_step_helper block (tid : thread_id) bst1 bst2 :=
    ⟪ AT_BLOCK: Some block = nth_error (binstrs bst1) (bpc bst1) ⟫ /\
    ⟪ BLOCK_STEP: (step tid) ^^ (length block) (bst2st bst1) (bst2st bst2) ⟫. 

  Definition block_step (tid : thread_id) bst1 bst2 : Prop :=
    exists block, block_step_helper block tid bst1 bst2.
  
  Definition binit blocks :=
    {|
      binstrs := blocks;
      bpc := 0;
      bG := init_execution;
      beindex := 0;
      bregf := RegFile.init;
      bdepf := DepsFile.init;
      bectrl := ∅ |}.

  Definition same_behavior_local GO GI :=
    ⟪ RESTR_EVENTS: E GO ≡₁ E GI ∩₁ RWO GI ⟫ /\
    ⟪ SAME_LAB: forall x (EGOx: E GO x), lab GO x = lab GI x ⟫ /\
    ⟪ RESTR_RMW: rmw GO ≡ ∅₂⟫ /\
    ⟪ RESTR_DATA: data GO ≡ restr_rel (RWO GI) (data GI)⟫ /\
    ⟪ RESTR_CTRL: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI)⟫ /\ 
    ⟪ RESTR_ADDR: addr GO ≡ restr_rel (RWO GI) (addr GI)⟫ /\ 
    ⟪ RESTR_RMWDEP: rmw_dep GO ≡ ∅₂⟫. 

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GO.(co) ≡ GI.(co) ⟫ /\
    ⟪RESTR_RF: GO.(rf) ≡ restr_rel (RWO GI) GI.(rf) ⟫ /\
    ⟪SAME_INIT: E GO ∩₁ is_init ≡₁ E GI ∩₁ is_init ⟫ /\
    ⟪SAME_INIT_LAB: forall l, lab GO (InitEvent l) = lab GI (InitEvent l) ⟫. 

  Definition mm_similar_states sto bsti :=
    is_thread_block_compiled (instrs sto) (binstrs bsti) /\
    pc sto = bpc bsti /\
    same_behavior_local (G sto) (bG bsti) /\
    (forall reg (NEXC: reg <> exchange_reg), regf sto reg = bregf bsti reg) /\
    (forall reg (NEXC: reg <> exchange_reg), depf sto reg ≡₁ bdepf bsti reg ∩₁ RWO (bG bsti)) /\
    ectrl sto ≡₁ bectrl bsti ∩₁ RWO (bG bsti) /\
    eindex sto = beindex bsti.
  

  Definition omm_block_step (tid : thread_id) (bst1 bst2: block_state) :=
    ⟪ BLOCK_STEP: exists block, block_step_helper block tid bst1 bst2 ⟫ /\
    ⟪ BINSTRS_SAME: binstrs bst1 = binstrs bst2 ⟫ /\
    ⟪ COMPILED: exists PO, is_thread_block_compiled PO (binstrs bst1) ⟫. 
  
  Lemma near_pc b block d (BLOCK_POS: Some b = nth_error block d)
        bst st (BST2ST: st = bst2st bst)
        (AT_BLOCK: Some block = nth_error (binstrs bst) (bpc bst))
        (BST_NONTERM: bpc bst < length (binstrs bst)):
    Some b = nth_error (instrs st) (pc st + d).
  Proof.
    replace (instrs st) with (flatten (binstrs bst)).
    2: { unfold bst2st in BST2ST. subst. auto. }
    replace (pc st) with (length (flatten (firstn (bpc bst) (binstrs bst)))).
    2: { unfold bst2st in BST2ST. subst. auto. }
    rewrite <- (firstn_skipn (bpc bst) (binstrs bst)) in AT_BLOCK. 
    rewrite nth_error_app2 in AT_BLOCK.
    2: { apply firstn_le_length. }
    rewrite firstn_length_le in AT_BLOCK; [| omega]. 
    rewrite Nat.sub_diag in AT_BLOCK.
    rewrite (@flatten_split _ (binstrs bst) (bpc bst)); [| auto]. 
    rewrite nth_error_app2; [| omega].
    rewrite minus_plus.
    remember (skipn (bpc bst) (binstrs bst)) as ll. 
    assert (forall {A: Type} l (x: A), Some x = nth_error l 0 -> exists l', l = x :: l'). 
    { ins. destruct l; vauto. }
    apply H in AT_BLOCK. desc.
    rewrite AT_BLOCK. simpl.
    rewrite nth_error_app1.
    { cut (exists b, Some b = nth_error block d); auto. 
      apply OPT_VAL. congruence. }
    apply nth_error_Some. congruence. 
  Qed. 

  Lemma block_step_nonterminal bst bst' tid
        (OSEQ_STEP: block_step tid bst bst'):
    bpc bst < length (binstrs bst).
  Proof.
    destruct (dec_lt (bpc bst) (length (binstrs bst))); auto.
    exfalso. apply not_lt in H.
    do 2 (red in OSEQ_STEP; desc).
    pose proof (proj2 (nth_error_None (binstrs bst) (bpc bst))). 
    intuition. congruence.
  Qed.

  Definition omm_block_step_PO PO (tid : thread_id) (bst1 bst2: block_state) :=
    ⟪ BLOCK_STEP: exists block, block_step_helper block tid bst1 bst2 ⟫ /\
    ⟪ BINSTRS_SAME: binstrs bst1 = binstrs bst2 ⟫ /\
    ⟪ COMPILED: is_thread_block_compiled PO (binstrs bst1) ⟫. 
  
  Lemma bs_extract bst bst' tid PO (OMM_BLOCK_STEP: omm_block_step_PO PO tid bst bst'):
    block_step tid bst bst'.
  Proof. red in OMM_BLOCK_STEP; desc. red in BLOCK_STEP. desc. vauto. Qed.

  Definition goto_addresses_restricted PO :=
    forall cond addr0 i (IN: Some (Instr.ifgoto cond addr0) = nth_error PO i),
      addr0 <= length PO.
    
  Definition omm_clarified PO :=
    exchange_reg_reserved PO /\
    goto_addresses_restricted PO. 
    
End OCaml_IMM_Correspondence. 

Section CorrectedDefinitions.

  Notation "'E' G" := G.(acts_set) (at level 1).

  Definition graphs_sim_weak (G1 G2: execution) :=
    E G1 ≡₁ E G2 /\
    (forall x, E G1 x -> lab G1 x = lab G2 x) /\
    rmw G1 ≡ rmw G2 /\
    data G1 ≡ data G2 /\
    addr G1 ≡ addr G2 /\
    ctrl G1 ≡ ctrl G2 /\
    rmw_dep G1 ≡ rmw_dep G2.    
  
End CorrectedDefinitions.   
