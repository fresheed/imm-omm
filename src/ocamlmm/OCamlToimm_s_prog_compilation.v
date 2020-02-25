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

  Definition is_thread_compiled PO PI :=
    exists BPI, is_thread_block_compiled PO BPI /\ PI = flatten BPI. 

  Definition is_compiled (ProgO: Prog.Prog.t) (ProgI: Prog.Prog.t) :=
    ⟪ SAME_THREADS: forall t_id, IdentMap.In t_id ProgO <-> IdentMap.In t_id ProgI ⟫ /\
    ⟪ THREADS_COMPILED: forall thread PO PI (TO: Some PO = IdentMap.find thread ProgO)
                          (TI: Some PI = IdentMap.find thread ProgI),
        is_thread_compiled PO PI ⟫.

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

  Lemma compilation_same_length PO BPI (COMP: is_thread_block_compiled PO BPI):
    length PO = length BPI.
  Proof.
    red in COMP. desc.
    eapply eq_trans; eapply Forall2_length; eauto. 
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
      | Instr.update (Instr.exchange _) _ _ _ reg lexpr => reg = exchange_reg /\ ~ In exchange_reg (lexpr_regs lexpr)
      | _ => False
      end. 
  Proof. Admitted.
  
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

End OCaml_IMM_Compilation.


Section OCaml_IMM_Correspondence.
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
  
  Notation "'E' G" := G.(acts_set) (at level 1).
  Notation "'R' G" := (fun a => is_true (is_r G.(lab) a)) (at level 1).
  Notation "'W' G" := (fun a => is_true (is_w G.(lab) a)) (at level 1).
  Notation "'RW' G" := (R G ∪₁ W G) (at level 1).

  Definition same_behavior_local (GO GI: execution) :=
    ⟪ RESTR_EVENTS: E GO ≡₁ E GI ∩₁ (RW GI \₁ dom_rel (GI.(rmw))) ⟫ /\
    ⟪ SAME_LAB: forall x (EGOx: E GO x), lab GO x = lab GI x ⟫. 

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ≡ GI.(rf) ⨾ ⦗set_compl (dom_rel GI.(rmw))⦘⟫.        

  Definition mm_similar_states (sto: state) (bsti: block_state) :=
    is_thread_block_compiled sto.(instrs) bsti.(binstrs)  /\
    sto.(pc) = bsti.(bpc) /\
    same_behavior_local sto.(G) bsti.(bG) /\
    sto.(regf) = bsti.(bregf) /\
    sto.(depf) = bsti.(bdepf) /\
    sto.(ectrl) = bsti.(bectrl) /\
    sto.(eindex) = bsti.(beindex).


  Definition omm_block_step (tid : thread_id) (bst1 bst2: block_state) :=
    exists block, block_step_helper block tid bst1 bst2 /\
             exists instr, is_instruction_compiled instr block. 
  
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

  Lemma bs_extract bst bst' tid (OSEQ_STEP: omm_block_step tid bst bst'):
    block_step tid bst bst'.
  Proof. do 2 (red in OSEQ_STEP; desc). vauto. Qed.

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

  Lemma BPC_CHANGE_foobar bst bst' tid
        (OMM_BLOCK_STEP: omm_block_step tid bst bst')
        (COMP: exists PO, is_thread_block_compiled PO (binstrs bst)):
    bpc bst' = bpc bst + 1 \/ exists cond adr, Some [Instr.ifgoto cond adr] = nth_error (binstrs bst) (bpc bst).
  Proof.
    red in OMM_BLOCK_STEP. desc. red in OMM_BLOCK_STEP. desc.
    assert ((exists (cond : Instr.expr) (adr : nat),
                block = [Instr.ifgoto cond adr])
            \/ (forall (cond : Instr.expr) (adr : nat), ~ In (Instr.ifgoto cond adr) block)) as BLOCK_CONTENT.
    { admit. }
    (* remember (bst2st bst) as st. remember (bst2st bst') as st'.  *)
    assert (block = sublist (instrs (bst2st bst)) (pc (bst2st bst)) (length block)).
    { admit. }
    destruct BLOCK_CONTENT.
    { right. desc. exists cond. exists adr. congruence. }
    left.
    assert (pc (bst2st bst') = pc (bst2st bst) + length block) by admit.
    unfold bst2st in H1. simpl in H1.
    replace (binstrs bst') with (binstrs bst) in * by admit.
    assert (length block > 0) as LENB. 
    { inversion OMM_BLOCK_STEP0; vauto. }
    assert (bpc bst' <= bpc bst \/ exists d, bpc bst' = bpc bst + S d) by admit.
    desf. 
    { assert (length (flatten (firstn (bpc bst') (binstrs bst)))
              <= length (flatten (firstn (bpc bst) (binstrs bst)))).
      { admit. }
      omega. }
    { destruct d; auto.
      exfalso. 
      rewrite H2 in *.
      replace (bpc bst + S (S d)) with ((bpc bst + 1) + (d + 1)) in H1 by omega. 
      replace (binstrs bst) with (firstn (bpc bst + 1) (binstrs bst) ++ skipn (bpc bst + 1) (binstrs bst)) in H1 at 1.
      2: { apply firstn_skipn. }
      replace (bpc bst + 1) with (length (firstn (bpc bst + 1) (binstrs bst))) in H1 at 1.
      2: { apply firstn_length_le.
           rewrite Nat.add_1_r. apply lt_le_S.
           apply nth_error_Some. congruence. }
      rewrite firstn_app_2 in H1.
      rewrite (first_end _ _ AT_BLOCK) in H1.
      rewrite !flatten_app, !app_length in H1. simpl in H1.
      rewrite <- app_nil_end in H1.
      assert (length (flatten (firstn (d + 1) (skipn (bpc bst + 1) (binstrs bst)))) = 0).
      { omega. }
      apply length_zero_iff_nil in H3.
      assert (firstn (d + 1) (skipn (bpc bst + 1) (binstrs bst)) = []).
      { destruct (firstn (d + 1) (skipn (bpc bst + 1) (binstrs bst))); auto.
        admit. }
  Admitted. 
      
      (* do 2 rewrite <- Nat.add_1_r, Const.add_assoc in H1. *)
      (* assert (exists block', Some block' = nth_error (binstrs bst) (bpc bst) *)
  (*   dest *)

      (* foobar.  *)
    (* inversion OMM_BLOCK_STEP0. *)
      
  (* Qed. *)

  (* Lemma BPC_CHANGE_foobar2 bst bst' tid (OMM_BLOCK_STEP: omm_block_step tid bst bst') (COMP: exists PO, is_thread_block_compiled PO (binstrs bst)): *)
  (*   bpc bst' = bpc bst + 1 \/ exists cond adr, Some [Instr.ifgoto cond adr] = nth_error (binstrs bst) (bpc bst). *)
  (* Proof. *)
  (*   red in OMM_BLOCK_STEP. desc. *)
  (*   assert (binstrs bst = binstrs bst') as BINSTRS_SAME. *)
  (*   { eapply (@SAME_BINSTRS _ _ tid). red. eauto. } *)
  (*   red in OMM_BLOCK_STEP. desc. *)
  (*   inversion OMM_BLOCK_STEP0. *)
  (*   - left. subst. simpl in *. apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP. *)
  (*     assert (Some ld = nth_error PO (bpc bst)). *)
  (*     { assert (exists instr, Some instr = nth_error PO (bpc bst)). *)
  (*       { apply OPT_VAL. apply nth_error_Some. *)
  (*         rewrite (compilation_same_length COMP). *)
  (*         apply nth_error_Some. eapply OPT_VAL. eauto. } *)
  (*       desc. pose proof (every_instruction_compiled COMP _ H AT_BLOCK). *)
  (*       inversion H0. vauto. } *)
  (*     do 2 (red in BLOCK_STEP; desc). *)
  (*     replace instr with ld in *. *)
  (*     2: { foobar.  *)
  (*     assert (AT_PC: Some ld = nth_error (instrs (bst2st bst)) (pc (bst2st bst))). *)
  (*     {  *)
  (*       apply eq_trans with (y := nth_error [ld] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc (bst2st bst))). *)
  (*       eapply sublist_items; eauto. } *)
  (*     inversion ISTEP0; rewrite <- AT_PC in ISTEP; inversion ISTEP; rewrite II in H2; subst ld. *)
  (*     all: try discriminate H2. *)
  (*     subst. unfold bst2st in UPC. simpl in UPC. *)
  (* Admitted. *)

  Lemma BPC_CHANGE bst bst' tid (OMM_BLOCK_STEP: omm_block_step tid bst bst'):
    bpc bst' = bpc bst + 1 \/ exists cond adr, Some [Instr.ifgoto cond adr] = nth_error (binstrs bst) (bpc bst).
  Proof.
    red in OMM_BLOCK_STEP. desc. red in OMM_BLOCK_STEP. desc.
    assert ((exists (cond : Instr.expr) (adr : nat),
                block = [Instr.ifgoto cond adr])
            \/ (forall (cond : Instr.expr) (adr : nat), ~ In (Instr.ifgoto cond adr) block)) as BLOCK_CONTENT.
    { admit. }
    destruct BLOCK_CONTENT.
    { right. desc. exists cond. exists adr. congruence. }
    left.
    remember (bst2st bst) as st. remember (bst2st bst') as st'.
    assert (pc st = length (flatten (firstn (bpc bst) (binstrs bst)))) by vauto. 
    assert (pc st' = length (flatten (firstn (bpc bst') (binstrs bst)))) by admit.
    assert (pc st' = pc st + length block) by admit.
    rewrite H2 in H1. rewrite Heqst in H1. unfold bst2st in H1. simpl in H1.
    rewrite <- app_length in H1.
    replace (flatten (firstn (bpc bst) (binstrs bst)) ++ block) with (flatten (firstn (bpc bst) (binstrs bst) ++ [block])) in H1. 
    2: { rewrite flatten_app. simpl. rewrite app_nil_r. auto. }
    rewrite <- first_end in H1; auto.
    assert (bpc bst' < bpc bst + 1 \/ bpc bst' = bpc bst + 1 \/ bpc bst' > bpc bst + 1) by omega. 
    destruct H3 as [BPC | [BPC | BPC]]; auto; exfalso. 
    {
      (* set (strict_prefix_alt := fun {A: Type} (l1 l2: list A) => exists x l', l2 = l1 ++ x :: l'). *)
      (* assert (strict_prefix_alt _ (firstn (bpc bst') (binstrs bst)) (firstn (bpc bst + 1) (binstrs bst))) by admit. *)
      (* red in H4. desc. rewrite H4, flatten_app, app_length in H1. *)
      (* simpl in H1. rewrite app_length in H1. *)
      (* assert (length x > 0). *)
      (* {  *)
      (* assert (length (flatten l') = 0) by omega. *)
      (* apply length_zero_iff_nil in H5. *)
      admit. }

    (* foobar. *)
    
    (* destruct H0. *)
    (* { admit. } *)
    (* desc. cut (d = 1); [ins; vauto|].   *)
    (* unfold bst2st in BLOCK_STEP. rewrite H0 in *. simpl in *.  *)
    (* assert (block = sublist (instrs (bst2st bst)) (pc (bst2st bst)) (length block)). *)
    (* { admit. } *)
    
  Admitted. 

End OCaml_IMM_Correspondence. 
