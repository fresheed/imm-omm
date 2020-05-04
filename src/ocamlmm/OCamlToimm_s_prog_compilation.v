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
Require Import Utils. 
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

  Lemma compilation_addresses_restricted PO BPI (COMP: is_thread_block_compiled PO BPI)
        cond addr0 i (IN: Some (Instr.ifgoto cond addr0) = nth_error PO i):
    addr0 <= length PO.
  Proof. Admitted.     
  
  Lemma Forall2_index {A B: Type} (l1: list A) (l2: list B) P
        (FORALL2: Forall2 P l1 l2)
        x y i (XI: Some x = nth_error l1 i) (YI: Some y = nth_error l2 i):
    P x y.
  Proof.
    generalize dependent l2. generalize dependent l1.
    set (T := fun i => forall l1 : list A,
                  Some x = nth_error l1 i ->
                  forall l2 : list B, Forall2 P l1 l2 -> Some y = nth_error l2 i -> P x y).
    eapply (strong_induction T).
    ins. red. ins. unfold T in IH.
    destruct l1; [destruct n; vauto |]. destruct l2; [destruct n; vauto |]. 
    destruct n eqn:N.
    { subst. simpl in *. inversion H. inversion H1. subst.
      inversion H0. auto. }
    subst. simpl in *. eapply IH; eauto.
    inversion H0. auto.
  Qed.


  Lemma Forall2_length {A B: Type} (l1: list A) (l2: list B) P
        (FORALL2: Forall2 P l1 l2):
    length l1 = length l2.
  Proof.
    generalize dependent l2. induction l1.
    { ins. inversion FORALL2. auto. }
    ins. inversion FORALL2. subst. simpl. f_equal.
    apply IHl1. auto.
  Qed. 
      
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

  (* Lemma ifgoto_corr PO PI corr (CORR: is_corrector corr PO PI): *)
  (*     forall cond adr (IN_PROG: In (Instr.ifgoto cond adr) PI), *)
  (*     In adr corr. *)
  (* Proof. Admitted. *)

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
    | Instr.update rmw _ _ _ reg lexpr => reg :: rmw_regs rmw ++ lexpr_regs lexpr
    | Instr.fence _ => []
    | Instr.ifgoto expr _ => expr_regs expr
    end.

  Lemma exchange_reg_dedicated PI (COMP: exists PO, is_thread_compiled PO PI)
        instr (INSTR: In instr PI):
    ~ In exchange_reg (instr_regs instr) <->
    ~ match instr with
      | Instr.update (Instr.exchange expr) _ _ _ reg lexpr => reg = exchange_reg /\ ~ In exchange_reg (lexpr_regs lexpr) /\ ~ In exchange_reg (expr_regs expr)
      | _ => False
      end. 
  Proof. Admitted.

  Lemma exchange_reg_dedicated' PI (COMP: exists PO, is_thread_compiled PO PI)
        instr (INSTR: In instr PI):
    match instr with
    | Instr.assign reg expr => reg <> exchange_reg /\ ~ In exchange_reg (expr_regs expr)
    | Instr.load _ reg lexpr => reg <> exchange_reg /\ ~ In exchange_reg (lexpr_regs lexpr)
    | Instr.store _ lexpr expr => ~ In exchange_reg (expr_regs expr) /\ ~ In exchange_reg (lexpr_regs lexpr)
    | Instr.update rmw _ _ _ reg lexpr => ~ In exchange_reg (rmw_regs rmw) /\ ~ In exchange_reg (lexpr_regs lexpr)
    | Instr.ifgoto expr _ => ~ In exchange_reg (expr_regs expr)
    | _ => True
    end.
  Proof. Admitted.

  Definition lexpr_of lexpr instr :=
    match instr with
    | Instr.load _ _ lexpr' 
    | Instr.store _ lexpr' _ 
    | Instr.update _ _ _ _ _ lexpr' => lexpr = lexpr'
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

  Lemma eval_instr_expr PI (COMP: exists PO, is_thread_compiled PO PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        instr (INSTR: In instr PI) expr (EXPR_OF: expr_of expr instr):
    RegFile.eval_expr (regf st) expr = RegFile.eval_expr (regf st') expr.
  Proof.
    apply eval_expr_same; auto.
    forward eapply exchange_reg_dedicated' as DED; eauto.
    red in EXPR_OF. 
    destruct instr; desc; vauto.
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

  Lemma eval_instr_lexpr PI (COMP: exists PO, is_thread_compiled PO PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        instr (INSTR: In instr PI) lexpr (EXPR_OF: lexpr_of lexpr instr):
    RegFile.eval_lexpr (regf st) lexpr = RegFile.eval_lexpr (regf st') lexpr.
  Proof.
    apply eval_lexpr_same; auto.
    forward eapply exchange_reg_dedicated' as DED; eauto.
    red in EXPR_OF. 
    destruct instr; desc; vauto.
  Qed. 
    
  Lemma eval_rmw_expr PI (COMP: exists PO, is_thread_compiled PO PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        rmw (INSTR: exists x orr orw lhs loc, In (Instr.update rmw x orr orw lhs loc) PI)
        expr (EXPR_OF: rmw_expr_of expr rmw):
    RegFile.eval_expr (regf st) expr = RegFile.eval_expr (regf st') expr.
  Proof.
    desc. apply eval_expr_same; auto.
    forward eapply exchange_reg_dedicated' as DED; eauto.
    red in EXPR_OF. 
    destruct rmw; desc; vauto.
    simpl in DED.
    red. ins. apply DED.
    apply in_or_app. 
    des; vauto. 
  Qed. 
    
  Lemma eval_safe_reg PI (COMP: exists PO, is_thread_compiled PO PI)
        st st' (REGF_SIM: forall reg (NOT_EXC: reg <> exchange_reg), regf st reg = regf st' reg)
        instr (INSTR: In instr PI) reg (SAFE_REG_OF: safe_reg_of reg instr):
    regf st reg = regf st' reg.
  Proof.
    apply REGF_SIM; auto.
    forward eapply exchange_reg_dedicated' as DED; eauto.
    red in SAFE_REG_OF. 
    destruct instr; desc; vauto.
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
  
  Lemma eval_instr_expr_deps PI (COMP: exists PO, is_thread_compiled PO PI)
        st st' (DEPF_SIM: forall reg (NEXC: reg <> exchange_reg), depf st reg ≡₁ depf st' reg ∩₁ RWO (G st'))
        instr (INSTR: In instr PI) expr (EXPR_OF: expr_of expr instr):
    DepsFile.expr_deps (depf st) expr ≡₁ DepsFile.expr_deps (depf st') expr ∩₁ RWO (G st').
  Proof.
    apply eval_expr_deps_same; auto.
    forward eapply exchange_reg_dedicated' as DED; eauto.
    red in EXPR_OF. 
    destruct instr; desc; vauto.    
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
    
  Lemma eval_instr_lexpr_deps PI (COMP: exists PO, is_thread_compiled PO PI)
        st st' (DEPF_SIM: forall reg (NEXC: reg <> exchange_reg), depf st reg ≡₁ depf st' reg ∩₁ RWO (G st'))
        instr (INSTR: In instr PI) lexpr (EXPR_OF: lexpr_of lexpr instr):
    DepsFile.lexpr_deps (depf st) lexpr ≡₁ DepsFile.lexpr_deps (depf st') lexpr ∩₁ RWO (G st').
  Proof.
    apply eval_lexpr_deps_same; auto.
    forward eapply exchange_reg_dedicated' as DED; eauto.
    red in EXPR_OF. 
    destruct instr; desc; vauto.    
  Qed.     
    
End OCaml_IMM_Compilation.


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

  Lemma state_record_equality st:
    st = {|
      instrs := instrs st;
      pc := pc st;
      G := G st;
      eindex := eindex st;
      regf := regf st;
      depf := depf st;
      ectrl := ectrl st
    |}.
  Proof. 
  Admitted. 
    
  Lemma blockstate_record_equality bst:
    bst = {|
      binstrs := binstrs bst;
      bpc := bpc bst;
      bG := bG bst;
      beindex := beindex bst;
      bregf := bregf bst;
      bdepf := bdepf bst;
      bectrl := bectrl bst
    |}.
  Proof. 
  Admitted.    

  (* TODO: understand https://stackoverflow.com/questions/27322979/why-coq-doesnt-allow-inversion-destruct-etc-when-the-goal-is-a-type*)
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

    (* Definition same_binstrs *)
  Lemma SAME_BINSTRS bst bst' tid (BLOCK_STEP: block_step tid bst bst'):
    binstrs bst = binstrs bst'.
  Proof.
    (* not true in general because of non-injective flatten *)
  Admitted.  


  Definition same_behavior_local (GO GI: execution) :=
    ⟪ RESTR_EVENTS: E GO ≡₁ E GI ∩₁ RWO GI ⟫ /\
    ⟪ SAME_LAB: forall x (EGOx: E GO x), lab GO x = lab GI x ⟫. 

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GO.(co) ≡ GI.(co) ⟫ /\
    ⟪RESTR_RF: GO.(rf) ≡ restr_rel (RWO GI) GI.(rf) ⟫ /\
    ⟪SAME_INIT: E GO ∩₁ is_init ≡₁ E GI ∩₁ is_init ⟫ /\
    ⟪SAME_INIT_LAB: forall l, lab GO (InitEvent l) = lab GI (InitEvent l) ⟫. 

  (* Definition mm_similar_states (sto: state) (bsti: block_state) := *)
  (*   is_thread_block_compiled sto.(instrs) bsti.(binstrs)  /\ *)
  (*   sto.(pc) = bsti.(bpc) /\ *)
  (*   same_behavior_local sto.(G) bsti.(bG) /\ *)
  (*   sto.(regf) = bsti.(bregf) /\ *)
  (*   sto.(depf) = bsti.(bdepf) /\ *)
  (*   sto.(ectrl) = bsti.(bectrl) /\ *)
  (*   sto.(eindex) = bsti.(beindex). *)

  Definition mm_similar_states (sto: state) (bsti: block_state) :=
    is_thread_block_compiled sto.(instrs) bsti.(binstrs)  /\
    sto.(pc) = bsti.(bpc) /\
    same_behavior_local sto.(G) bsti.(bG) /\
    (forall reg (NOT_EXC: reg <> exchange_reg), sto.(regf) reg = bsti.(bregf) reg) /\
    (forall reg (NOT_EXC: reg <> exchange_reg), sto.(depf) reg = bsti.(bdepf) reg) /\
    sto.(ectrl) = bsti.(bectrl) /\
    sto.(eindex) = bsti.(beindex).

  Definition omm_block_step (tid : thread_id) (bst1 bst2: block_state) :=
    ⟪ BLOCK_STEP: exists block, block_step_helper block tid bst1 bst2 ⟫ /\
    ⟪ BINSTRS_SAME: binstrs bst1 = binstrs bst2 ⟫ /\
    ⟪ COMPILED: exists PO, is_thread_block_compiled PO (binstrs bst1) ⟫. 
  
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

  Lemma bs_extract bst bst' tid (OMM_BLOCK_STEP: omm_block_step tid bst bst'):
    block_step tid bst bst'.
  Proof. red in OMM_BLOCK_STEP; desc. red in BLOCK_STEP. desc. vauto. Qed.

  Definition sublist {A: Type} (l: list A) (start len: nat) := firstn len (skipn start l).  
    
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

End OCaml_IMM_Correspondence. 

Section CorrectedDefinitions.

  Notation "'E' G" := G.(acts_set) (at level 1).

  Definition program_execution_corrected (prog : Prog.t) G :=
    (forall e : actid, E G e -> is_init e \/ IdentMap.In (tid e) prog) /\
    (forall (thread : IdentMap.key) (PIi : list Instr.t)
       (THREAD: Some PIi = IdentMap.find thread prog)
       Gi (THREAD_EXEC: thread_restricted_execution G thread Gi),
        thread_execution thread PIi Gi).


  Definition graphs_sim_weak (G1 G2: execution) :=
    E G1 ≡₁ E G2 /\
    (forall x, E G1 x -> lab G1 x = lab G2 x) /\
    rmw G1 ≡ rmw G2 /\
    data G1 ≡ data G2 /\
    addr G1 ≡ addr G2 /\
    ctrl G1 ≡ ctrl G2 /\
    rmw_dep G1 ≡ rmw_dep G2.    

  Definition Othread_execution_sim tid instrs G_ :=
    exists s,
      ⟪ STEPS : (Ostep tid)＊ (init instrs) s ⟫ /\
      ⟪ TERMINAL : is_terminal s ⟫ /\
      ⟪ PEQ : graphs_sim_weak s.(G) G_ ⟫.

  Definition Oprogram_execution_corrected prog (OPROG: OCamlProgram prog) G :=
    (forall e (IN: G.(acts_set) e), is_init e \/ IdentMap.In (tid e) prog) /\
    (forall (thread : IdentMap.key) (POi : list Instr.t)
       (THREAD: Some POi = IdentMap.find thread prog)
       Gi (THREAD_EXEC: thread_restricted_execution G thread Gi),
        (* Othread_execution thread POi Gi). *)
        Othread_execution_sim thread POi Gi).
  
  Lemma program_execution_equiv (prog : Prog.t) G:
    program_execution_corrected prog G <-> program_execution prog G.
  Proof. Admitted.

  Lemma Oprogram_execution_equiv prog G (OPROG: OCamlProgram prog):
    Oprogram_execution_corrected OPROG G <-> Oprogram_execution OPROG G.
  Proof. Admitted.

    
  Definition same_behavior_local_ext GO GI :=
    ⟪ RESTR_EVENTS: E GO ≡₁ E GI ∩₁ RWO GI ⟫ /\
    ⟪ SAME_LAB: forall x (EGOx: E GO x), lab GO x = lab GI x ⟫ /\
    ⟪ RESTR_RMW: rmw GO ≡ ∅₂⟫ /\
    ⟪ RESTR_DATA: data GO ≡ restr_rel (RWO GI) (data GI)⟫ /\
    ⟪ RESTR_CTRL: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI)⟫ /\ 
    ⟪ RESTR_ADDR: addr GO ≡ restr_rel (RWO GI) (addr GI)⟫ /\ 
    ⟪ RESTR_RMWDEP: rmw_dep GO ≡ ∅₂⟫. 
  
  Lemma sbl_ext_TMP GOi GIi (SBL: same_behavior_local GOi GIi):
    same_behavior_local_ext GOi GIi.
  Proof. Admitted.

  
End CorrectedDefinitions.   
