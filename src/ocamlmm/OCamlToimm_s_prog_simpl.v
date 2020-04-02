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
Require Import OCamlToimm_s_prog. 
Require Import OCamlToimm_s_prog_compilation. 
Require Import OCamlToimm_s_prog_pair_step. 
Require Import OCamlToimm_s_prog_bounded_properties. 
Require Import Utils.
Require Import ClosuresProperties. 
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import Logic.Decidable. 
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.


Definition same_keys {A B: Type} (map1: IdentMap.t A) (map2: IdentMap.t B)
  := forall key, IdentMap.In key map1 <-> IdentMap.In key map2.

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

  (* Definition restrict (G: execution) (tid: thread_id): execution. *)
  (*   set (thread_local := fun x y => Events.tid x = tid /\ Events.tid y = tid).  *)
  (*   exact {| *)
  (*       acts := filterP (fun e => is_tid tid e) (acts G); *)
  (*       lab := lab G; (* TODO: restrict? *) *)
  (*       rmw := rmw G ∩ thread_local; *)
  (*       data := data G ∩ thread_local; *)
  (*       addr := addr G ∩ thread_local; *)
  (*       ctrl := ctrl G ∩ thread_local; *)
  (*       rmw_dep := rmw_dep G ∩ thread_local; *)
  (*       rf := ∅₂; *)
  (*       co := ∅₂; |}. *)
  (* Defined. *)
  (* Definition g2tsg' (G: execution): *)
  (*   exists (TSG: thread_separated_graph), True.  *)
  (*   set (events_tids := map (fun e => Events.tid e) (acts G)).  *)
  (*   assert (ListDec.decidable_eq thread_id) as DECIDE_TID.  *)
  (*   { unfold thread_id, Ident.t. red. ins. red.  *)
  (*     pose proof (DecidableTypeEx.Positive_as_DT.eq_dec x y).  *)
  (*     destruct H; auto. } *)
  (*   pose proof (ListDec.uniquify DECIDE_TID events_tids) as [tids TIDS_UNIQUE].  *)
  (*   set (Gis_list := map (fun tid => (tid, restrict G tid)) tids).  *)
  (*   (* TODO: remove rmw from tsg? *)     *)
  (*   exists {| *)
  (*       Gis := UsualFMapPositive.UsualPositiveMap.Properties.of_list Gis_list; *)
  (*       Einit_tsg := fun e => In e (filterP (fun e' => is_tid tid_init e') (acts G)); *)
  (*       rf_tsg := rf G; *)
  (*       co_tsg := co G; *)
  (*       rmw_tsg := rmw G |}.  *)
  (*   auto.  *)
  (* Defined. *)
 
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
    
  Definition omm_premises_hold G :=
    (* separated *)
    (* let Loc_ := fun l x => loc G.(lab) x = Some l in *)
    (* ⟪ LSM : forall l, (Loc_ l \₁ is_init ⊆₁ (ORlx G)  \/  Loc_ l \₁ is_init ⊆₁ (Sc G)) ⟫ /\ *)
    ⟪ WSCFACQRMW : E G ∩₁ W G ∩₁ Sc G ≡₁ codom_rel (⦗F G ∩₁ Acq G⦘ ⨾ immediate (sb G) ⨾ rmw G) ⟫ /\
    ⟪ RMWSC  : rmw G ≡ ⦗Sc G⦘ ⨾ rmw G⨾ ⦗Sc G⦘ ⟫ /\
    ⟪ WRLXF : E G ∩₁ W G ∩₁ ORlx G ⊆₁ codom_rel (⦗F G ∩₁ Acqrel G⦘ ⨾ immediate (sb G)) ⟫ /\
    ⟪ RSCF  : E G ∩₁ R G ∩₁ Sc G ⊆₁ codom_rel (⦗F G ∩₁ Acq G⦘ ⨾ immediate (sb G)) ⟫.

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
      data_in_sb' : G.(data) ⊆ G.(sb) ;
      addr_in_sb' : G.(addr) ⊆ G.(sb) ;
      ctrl_in_sb' : G.(ctrl) ⊆ G.(sb) ;
      rmw_dep_in_sb' : G.(rmw_dep) ⊆ G.(sb) ;
    }. 
  
  Record Wf_global (G: execution) :=
    {
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

  Lemma init_mm_same: forall PO BPI (COMP: is_thread_block_compiled PO BPI),
      mm_similar_states (init PO) (binit BPI).
  Proof.
    ins. red. simpl. splits; auto.
    unfold init_execution. red. simpl. basic_solver. 
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

  Definition on_block st block :=
    ⟪ PROG_BLOCK: block = sublist (instrs st) (pc st) (length block) ⟫ /\
    ⟪ COMP_BLOCK: (exists oinstr, is_instruction_compiled oinstr block) ⟫.
  
  Definition at_compilation_block st :=
    (exists block, on_block st block) \/ is_terminal st.

  Definition oseq_step (tid : thread_id) sti1 sti2 :=
    exists block, on_block sti1 block /\
             (step tid) ^^ (length block) sti1 sti2. 

  Lemma is_terminal_new st: pc st >= length (instrs st) <-> is_terminal st.
  Proof. Admitted.

  Lemma is_terminal_pc_bounded st: is_terminal st <-> pc st = length (instrs st).
  Proof. Admitted. 

  Definition bst_from_st st BPI b :=
    {|
      binstrs := BPI;
      bpc := b;
      bG := G st; 
      beindex := eindex st;
      bregf := regf st;
      bdepf := depf st;
      bectrl := ectrl st |}. 

  Definition min_prop {A: Type} (P: list A -> Prop)
    := forall l (Pl: P l), (forall l1 l2 (LT: l2 <> []) (SPLIT: l = l1 ++ l2), ~ P l1). 

  Lemma firstn_length_leq {A: Type} (l: list A) i:
    length (firstn i l) <= length l.
  Proof.
    generalize dependent l. induction i.
    { ins. omega. }
    ins. destruct l; vauto.
    simpl. apply le_n_S. auto.
  Qed. 
    
  (* Lemma start_block_deterministic {A: Type} P (MINPROP: min_prop P) *)
  (*       ll *)
  (*       (block' : list A) *)
  (*       (* l *) *)
  (*       (* (FLT : l = flatten (block' :: ll))         *) *)
  (*       (NE_LL : Forall (fun l : list A => l <> []) (block' :: ll)) *)
  (*       (P_LL : Forall P (block' :: ll)) *)
  (*       (block : list A) *)
  (*       (NE_B : block <> []) *)
  (*       (BLOCK_P : P block) *)
  (*       (BLOCK : block = firstn (length block) (flatten (block' :: ll))) *)
  (*       (BLOCK' : block' = firstn (length block') (block' ++ flatten ll)): *)
  (*   block = block'. *)
  (* Proof.  *)
  (*   assert (length block <= length (block' :: ll)) as LEN_B. *)
  (*   { (* rewrite <- FLT in BLOCK. *) *)
  (*     apply (@f_equal _ _ (@length _)) in BLOCK. *)
  (*     pose proof (firstn_length_leq (block' :: ll)(length block)). *)
  (*     simpl in *. omega. } *)
  (*   assert (length block' <= length l) as LEN_BLOCK'.  *)
  (*   { subst l. simpl. rewrite app_length. omega. } *)
  (*   destruct (lt_eq_lt_dec (length block) (length block')) as [[LT | EQ] | GT]. *)
  (*   2: { forward eapply (@firstn_ge_incl _ (block' :: ll)(length block) (length block')) as PREF; [omega| ]. *)
  (*        rewrite EQ in PREF at 2. rewrite skipn_firstn_nil in PREF. *)
  (*        rewrite app_nil_r in PREF. simpl in BLOCK. congruence. } *)
  (*   { forward eapply (@firstn_ge_incl _ (block' :: ll)(length block) (length block')) as PREF; [omega| ]. *)
  (*     exfalso. *)
  (*     subst l. simpl in *. rewrite <- BLOCK, <- BLOCK' in PREF. *)
  (*     inversion  P_LL. subst.  *)
  (*     red in MINPROP. specialize (MINPROP block' H1 block (skipn (length block) block')). *)
  (*     apply MINPROP; vauto. *)
  (*     apply (@f_equal _ _ (@length _)) in PREF. rewrite app_length in PREF. *)
  (*     red. ins. apply NE_B. apply length_zero_iff_nil. *)
  (*     apply length_zero_iff_nil in H. omega. } *)
  (*   forward eapply (@firstn_ge_incl _ (block' :: ll)(length block') (length block)) as PREF; [omega| ]. *)
  (*   exfalso.  *)
  (*   subst l. simpl in *. rewrite <- BLOCK, <- BLOCK' in PREF. *)
  (*   inversion  P_LL. subst.  *)
  (*   red in MINPROP. specialize (MINPROP block BLOCK_P block' (skipn (length block') block)). *)
  (*   apply MINPROP; vauto. *)
  (*   apply (@f_equal _ _ (@length _)) in PREF. rewrite app_length in PREF. *)
  (*   red. ins. inversion NE_LL. subst. apply H4. *)
  (*   apply length_zero_iff_nil.  apply length_zero_iff_nil in H. omega. *)
  (* Qed.  *)

  Lemma start_block_deterministic
        (A : Type)
        (P : list A -> Prop)
        (block : list A)
        (block' : list A)
        (ll : list (list A))
        (MINPROP : min_prop P)
        (NEblock: block <> [])
        (Pblock: P block)
        (NE_B : block' <> [])
        (BLOCK'_P : P block')
        (BLOCK' : block' = firstn (length block') (flatten (block :: ll))):
    block' = block.
  Proof.
    assert (block = firstn (length block) (block ++ flatten ll)) as L0. 
    { rewrite <- Nat.add_0_r with (n := length block).
      rewrite firstn_app_2. simpl. symmetry. apply app_nil_r. }
    assert (length block' <= length (flatten (block :: ll))) as LEN_B.
    { apply (@f_equal _ _ (@length _)) in BLOCK'.
      pose proof (firstn_length_leq (flatten (block :: ll)) (length block')). omega. }
    assert (length block <= length (flatten (block :: ll))) as LEN_L0. 
    { simpl. rewrite app_length. omega. }
    destruct (lt_eq_lt_dec (length block') (length block)) as [[LT | EQ] | GT].
    2: { forward eapply (@firstn_ge_incl _ (flatten (block :: ll)) (length block') (length block)) as PREF; [omega| ].
         rewrite EQ in PREF at 2. rewrite skipn_firstn_nil in PREF.
         rewrite app_nil_r in PREF. simpl in BLOCK'. congruence. }
    { forward eapply (@firstn_ge_incl _ (flatten (block :: ll)) (length block') (length block)) as PREF; [omega| ].
      exfalso.
      simpl in *. rewrite <- BLOCK', <- L0 in PREF.
      red in MINPROP. specialize (MINPROP block Pblock block' (skipn (length block') block)).
      apply MINPROP; vauto.
      apply (@f_equal _ _ (@length _)) in PREF. rewrite app_length in PREF.
      red. ins. apply NE_B. apply length_zero_iff_nil.
      apply length_zero_iff_nil in H. omega. }
    forward eapply (@firstn_ge_incl _ (flatten (block :: ll)) (length block) (length block')) as PREF; [omega| ].
    exfalso. 
    simpl in *. rewrite <- BLOCK', <- L0 in PREF.
    red in MINPROP. specialize (MINPROP block' BLOCK'_P block (skipn (length block) block')).
    apply MINPROP; vauto.
    apply (@f_equal _ _ (@length _)) in PREF. rewrite app_length in PREF.
    red. ins. apply NEblock.
    apply length_zero_iff_nil.  apply length_zero_iff_nil in H. omega. 
  Qed. 
        
  Lemma ll_l_corr {A: Type} ll (l: list A) (FLT: l = flatten ll) block b
        (NE_LL: Forall (fun l => l <> []) ll)
        P (MINPROP: min_prop P)
        (P_LL: Forall P ll)
        (NE_B: block <> [])
        (BLOCK_P: P block):
    block = sublist l (length (flatten (firstn b ll))) (length block)
    <-> Some block = nth_error ll b.
  Proof.
    generalize dependent block. generalize dependent ll. generalize dependent l. 
    induction b.
    { intros. unfold sublist. rewrite FLT. simpl.
      split.
      { intros BLOCK. destruct ll.
        { simpl in BLOCK. rewrite firstn_nil in BLOCK. vauto. }
        f_equal.
        eapply start_block_deterministic; eauto; [inv NE_LL| inv P_LL]. }
      intros BLOCK. destruct ll; vauto. simpl.
      rewrite <- Nat.add_0_r with (n := length l0). rewrite firstn_app_2.
      simpl. symmetry. apply app_nil_r. } 
    ins. destruct ll; vauto.
    { simpl. unfold sublist. simpl. rewrite firstn_nil. vauto. }
    simpl. rewrite app_length. unfold sublist.
    rewrite skipn_app.
    replace (skipn (length l0 + length (flatten (firstn b ll))) l0) with (@nil A).
    2: { clear NE_LL. clear P_LL. induction l0.
         { simpl. destruct (length (flatten (firstn b ll))); vauto. }
         simpl. auto. }
    rewrite app_nil_l.
    replace (length l0 + length (flatten (firstn b ll)) - length l0) with (length (flatten (firstn b ll))) by omega.    
    apply IHb; vauto.
    { inversion NE_LL. vauto. }
    inversion P_LL. vauto.
  Qed. 

  Lemma instr_compiled_min_prop:
    min_prop (fun blk : list Instr.t =>
                exists oinstr : Instr.t, is_instruction_compiled oinstr blk).
  Proof.
    red. intros block [oinstr COMP] block' block'' NE'' BLOCK_STRUCT.
    red. intros [oinstr' COMP'].
    inversion COMP; subst.
    all: (inversion COMP'; subst; inversion H0; subst; auto).
  Qed. 

  Lemma Forall_index {A: Type} (l: list A) P:
    Forall P l <-> forall x i (XI: Some x = nth_error l i), P x.
  Proof.
    split.
    { intros FORALL x i XI.
      forward eapply (@Forall2_index _ _ l l (fun x _ => P x)); eauto. 
      clear XI. generalize dependent l. intros l. induction l.
      { ins. }
      ins. inversion FORALL. subst. apply Forall2_cons; auto. }
    ins. induction l; auto.    
    apply Forall_cons. split.
    { apply H with (i := 0). auto. }
    apply IHl. ins.
    apply H with (i := S i). simpl. auto. 
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

    Lemma ll_l_corr_helper BPI PI (FLT: PI = flatten BPI) block b
        (COMP: exists PO, is_thread_block_compiled PO BPI)
        (COMP_BLOCK: exists oinstr, is_instruction_compiled oinstr block)
    :
    block = sublist PI (length (flatten (firstn b BPI))) (length block)
    <-> Some block = nth_error BPI b.
  Proof.
    eapply ll_l_corr with (P := fun blk => exists oinstr, is_instruction_compiled oinstr blk); vauto.
    { desc. eapply COMPILED_NONEMPTY; eauto. }
    { apply instr_compiled_min_prop. }
    { clear COMP_BLOCK. eapply Forall_index. ins.
      desc. eapply resulting_block_compiled; eauto.
      eapply COMPILED_NONEMPTY; eauto. } 
    desc. inversion COMP_BLOCK; vauto.
  Qed. 
        
  Lemma st_bst_prog_blocks bst block (COMP: exists PO, is_thread_block_compiled PO (binstrs bst)):
    on_block (bst2st bst) block <-> Some block = nth_error (binstrs bst) (bpc bst).
  Proof.
    desc.
    assert (Forall (fun l : list Instr.t => l <> []) (binstrs bst)) as BPI_NE. 
    { eapply COMPILED_NONEMPTY; eauto. }
    split.
    { intros ON_BLOCK. red in ON_BLOCK. desc.
      unfold bst2st in PROG_BLOCK. simpl in PROG_BLOCK.
      eapply ll_l_corr_helper in PROG_BLOCK; eauto. }
    intros BLOCK. red.
    forward eapply resulting_block_compiled as COMP'; eauto. 
    splits; auto. 
    eapply ll_l_corr_helper; vauto.
  Qed. 

  Definition on_block_pc pc PI block := 
    ⟪BLOCK: block = sublist PI pc (length block)⟫ /\
    ⟪COMP_BLOCK: exists oinstr : Instr.t, is_instruction_compiled oinstr block⟫. 
  
  (* TODO: remove it since exact instruction is known when block_start is called? *)
  Lemma block_start pc PI block instr (BLOCK: on_block_pc pc PI block)
        (AT_PC: Some instr = nth_error PI pc):
    (exists mode, instr = Prog.Instr.fence mode) \/
    (exists loc expr, instr = Prog.Instr.load Orlx loc expr) \/
    (exists cond loc, instr = Prog.Instr.ifgoto cond loc) \/
    (exists reg expr, instr = Prog.Instr.assign reg expr).
  Proof.
    red in BLOCK. desc.
    inversion COMP_BLOCK.
    all: subst; simpl in *.
    (* TODO: refactor *)
    - assert (AT_PC1: Some ld = nth_error PI pc).
      { apply eq_trans with (y := nth_error [ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r pc).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      right. left. subst ld. eauto.
    - assert (AT_PC1: Some f = nth_error PI pc).
      { apply eq_trans with (y := nth_error [f; st] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r pc).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some f = nth_error PI pc).
      { apply eq_trans with (y := nth_error [f; ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r pc).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some f = nth_error PI pc).
      { apply eq_trans with (y := nth_error [f; exc] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r pc).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some asn = nth_error PI pc).
      { apply eq_trans with (y := nth_error [asn] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r pc).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      do 3 right. subst asn. eauto.
    - assert (AT_PC1: Some igt = nth_error PI pc).
      { apply eq_trans with (y := nth_error [igt] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r pc).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      do 2 right. left. subst igt. eauto.
  Qed.

  (* Lemma block_start_st st block instr (BLOCK: on_block st block) *)
  (*       (AT_PC: Some instr = nth_error (instrs st) (pc st)): *)
  (*   (exists mode, instr = Prog.Instr.fence mode) \/ *)
  (*   (exists loc expr, instr = Prog.Instr.load Orlx loc expr) \/ *)
  (*   (exists cond loc, instr = Prog.Instr.ifgoto cond loc) \/ *)
  (*   (exists reg expr, instr = Prog.Instr.assign reg expr). *)
  (* Proof. *)
  (*   red in BLOCK. desc. *)
  (*   inversion COMP_BLOCK. *)
  (*   all: subst; simpl in *. *)
  (*   (* TODO: refactor *) *)
  (*   - assert (AT_PC1: Some ld = nth_error (instrs st) (pc st)). *)
  (*     { apply eq_trans with (y := nth_error [ld] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc st)). *)
  (*       eapply sublist_items; eauto. } *)
  (*     rewrite <- AT_PC in AT_PC1. inversion AT_PC1. *)
  (*     right. left. subst ld. eauto. *)
  (*   - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)). *)
  (*     { apply eq_trans with (y := nth_error [f; st0] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc st)). *)
  (*       eapply sublist_items; eauto. } *)
  (*     rewrite <- AT_PC in AT_PC1. inversion AT_PC1. *)
  (*     left. subst f. eauto. *)
  (*   - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)). *)
  (*     { apply eq_trans with (y := nth_error [f; ld] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc st)). *)
  (*       eapply sublist_items; eauto. } *)
  (*     rewrite <- AT_PC in AT_PC1. inversion AT_PC1. *)
  (*     left. subst f. eauto. *)
  (*   - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)). *)
  (*     { apply eq_trans with (y := nth_error [f; exc] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc st)). *)
  (*       eapply sublist_items; eauto. } *)
  (*     rewrite <- AT_PC in AT_PC1. inversion AT_PC1. *)
  (*     left. subst f. eauto. *)
  (*   - assert (AT_PC1: Some asn = nth_error (instrs st) (pc st)). *)
  (*     { apply eq_trans with (y := nth_error [asn] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc st)). *)
  (*       eapply sublist_items; eauto. } *)
  (*     rewrite <- AT_PC in AT_PC1. inversion AT_PC1. *)
  (*     do 3 right. subst asn. eauto. *)
  (*   - assert (AT_PC1: Some igt = nth_error (instrs st) (pc st)). *)
  (*     { apply eq_trans with (y := nth_error [igt] 0); auto. *)
  (*       rewrite <- (NPeano.Nat.add_0_r (pc st)). *)
  (*       eapply sublist_items; eauto. } *)
  (*     rewrite <- AT_PC in AT_PC1. inversion AT_PC1. *)
  (*     do 2 right. left. subst igt. eauto. *)
  (* Qed. *)

  Lemma block_mid pc PI block instr (BLOCK: on_block_pc pc PI block)
        (BLOCK_LEN: length block >= 2)
        (AT_PC1: Some instr = nth_error PI (pc + 1)):
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
    { assert (AT_PC1': Some st = nth_error PI (pc + 1)).
      { apply eq_trans with (y := nth_error [f; st] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with st; [| congruence].
      subst st. eauto. }
    { assert (AT_PC1': Some ld = nth_error PI (pc + 1)).
      { apply eq_trans with (y := nth_error [f; ld] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with ld; [| congruence].
      subst ld. eauto. }
    { assert (AT_PC1': Some exc = nth_error PI (pc + 1)).
      { apply eq_trans with (y := nth_error [f; exc] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with exc; [| congruence].
      subst exc. eauto. }
  Qed.

  (* Lemma block_mid_st st block instr (BLOCK: on_block st block) *)
  (*       (BLOCK_LEN: length block >= 2) *)
  (*       (AT_PC1: Some instr = nth_error (instrs st) (pc st + 1)): *)
  (*   (exists loc expr, instr = Prog.Instr.store Orlx loc expr) \/ *)
  (*   (exists loc expr, instr = Prog.Instr.load Osc loc expr) \/ *)
  (*   (exists expr loc, instr = Prog.Instr.update (Prog.Instr.exchange expr) Xpln Osc Osc exchange_reg loc). *)
  (* Proof. *)
  (*   red in BLOCK. desc. *)
  (*   inversion COMP_BLOCK. *)
  (*   all: (rename H into OINSTR; rename H0 into BLOCK_CONTENTS). *)
  (*   all: subst block; simpl in *. *)
  (*   (* trivial cases for single instruction blocks *) *)
  (*   all: try omega. *)
  (*   (* now only 2-blocks remain*) *)
  (*   (* TODO: refactor *) *)
  (*   { assert (AT_PC1': Some st0 = nth_error (instrs st) (pc st + 1)). *)
  (*     { apply eq_trans with (y := nth_error [f; st0] 1); auto. *)
  (*       eapply sublist_items; eauto. } *)
  (*     replace instr with st0; [| congruence]. *)
  (*     subst st0. eauto. } *)
  (*   { assert (AT_PC1': Some ld = nth_error (instrs st) (pc st + 1)). *)
  (*     { apply eq_trans with (y := nth_error [f; ld] 1); auto. *)
  (*       eapply sublist_items; eauto. } *)
  (*     replace instr with ld; [| congruence]. *)
  (*     subst ld. eauto. } *)
  (*   { assert (AT_PC1': Some exc = nth_error (instrs st) (pc st + 1)). *)
  (*     { apply eq_trans with (y := nth_error [f; exc] 1); auto. *)
  (*       eapply sublist_items; eauto. } *)
  (*     replace instr with exc; [| congruence]. *)
  (*     subst exc. eauto. } *)
  (* Qed. *)

  Lemma no_acb_between_pc pc1 pc2 n (PC2: pc2 = pc1 + n)
        block (* (BLOCK: on_block st1 block) *)
        PI (BLOCK: on_block_pc pc1 PI block)
        (LT: n < length block) (NZ: n <> 0):
    not ((exists block', on_block_pc pc2 PI block') \/ pc2 >= length PI).
  Proof.
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
    { assert (AT_PC1: Some st = nth_error PI (pc1 + 1)).
      { apply eq_trans with (y := nth_error [f; st] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error PI pc1).
      { apply eq_trans with (y := nth_error [f; st] 0); auto.
        replace pc1 with (pc1 + 0) by omega.
        eapply sublist_items; eauto. }
      (* assert (NEXT_PC: pc st2 = pc st1 + 1). *)
      (* { apply (same_relation_exp (pow_unit (step tid))) in STEPS. *)
      (*   red in STEPS. desc. red in STEPS. desc. *)
      (*   inversion ISTEP0; auto. *)
      (*   rewrite II, <- AT_PC in ISTEP. discriminate. } *)
      
      red. intros ACB2. (* red in ACB2. *)
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { subst pc2.           
           red in TERM2. (* rewrite NEXT_PC, SAME_INSTRS in TERM2. *)
           pose proof (nth_error_None PI (pc1 + 1)) as CONTRA.
           apply not_iff_compat in CONTRA. destruct CONTRA as [CONTRA _].
           forward eapply CONTRA; [apply OPT_VAL; eauto| ].
           ins. } 
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite PC2. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    { assert (AT_PC1: Some ld = nth_error PI (pc1 + 1)).
      { apply eq_trans with (y := nth_error [f; ld] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error PI pc1).
      { apply eq_trans with (y := nth_error [f; ld] 0); auto.
        replace pc1 with (pc1 + 0) by omega.
        eapply sublist_items; eauto. }
      (* assert (NEXT_PC: pc st2 = pc st1 + 1). *)
      (* { apply (same_relation_exp (pow_unit (step tid))) in STEPS. *)
      (*   red in STEPS. desc. red in STEPS. desc. *)
      (*   inversion ISTEP0; auto. *)
      (*   rewrite II, <- AT_PC in ISTEP. discriminate. } *)
      
      red. intros ACB2. 
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. (* rewrite NEXT_PC, SAME_INSTRS in TERM2. *)
           pose proof (nth_error_None PI (pc1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite PC2. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    { assert (AT_PC1: Some exc = nth_error PI (pc1 + 1)).
      { apply eq_trans with (y := nth_error [f; exc] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error PI pc1).
      { apply eq_trans with (y := nth_error [f; exc] 0); auto.
        replace pc1 with (pc1 + 0) by omega.
        eapply sublist_items; eauto. }      
      red. intros ACB2. 
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite PC2 in TERM2.
           pose proof (nth_error_None PI (pc1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite PC2. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
  Qed. 
    
  Lemma no_acb_between st1 st2 tid block n (STEPS: (step tid) ^^ n st1 st2)
        (BLOCK: on_block st1 block) (LT: n < length block) (NZ: n <> 0):
    not (at_compilation_block st2).
  Proof.
    assert (SAME_INSTRS: instrs st2 = instrs st1).
    { symmetry. apply steps_same_instrs. eexists. eapply crt_num_steps. eauto. }
    pose proof BLOCK as BLOCK1.
    red in BLOCK. desc.

    cut (not ((exists block', on_block_pc (pc st2) (instrs st1) block') \/ (pc st2 >= length (instrs st1)))).
    { ins. red. ins. apply H. red in H0. des.
      { left. exists block0. red in H0.
        rewrite SAME_INSTRS in H0. 
        desc. red. splits; eauto. }
      right. apply is_terminal_new in H0. congruence. }

    eapply no_acb_between_pc; eauto.
    assert (length block = 2 -> exists md, Some (Instr.fence md) = nth_error (instrs st1) (pc st1)).
    { ins. inversion COMP_BLOCK; vauto.
      all: subst f.
      { exists Oacqrel.
        apply eq_trans with (y := nth_error [Instr.fence Oacqrel; st] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega.
        eapply sublist_items; vauto. }
      { exists Oacq.
        apply eq_trans with (y := nth_error [Instr.fence Oacq; ld] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega.
        eapply sublist_items; vauto. }
      exists Oacq.
      apply eq_trans with (y := nth_error [Instr.fence Oacq; exc] 0); auto.
      replace (pc st1) with (pc st1 + 0) by omega.
      eapply sublist_items; vauto. }
    inversion COMP_BLOCK; subst; simpl in *; try omega.
    all: replace n with 1 in * by omega.
    all: apply (same_relation_exp (pow_unit (step tid))) in STEPS.
    all: red in STEPS; desc; red in STEPS; desc.
    all: inversion ISTEP0; vauto.
    all: destruct H as [md FENCE]; auto.
    all: rewrite <- FENCE in ISTEP.
    all: inversion ISTEP.
  Qed.         

  Lemma skipn_0 {A: Type} (l: list A): skipn 0 l = l.
  Proof. destruct l; vauto. Qed. 
  
  Lemma on_block_iff_bindex BPI
        block pc (SL: block = sublist (flatten BPI) pc (length block))
        (COMP: exists PO, is_thread_block_compiled PO BPI):
    (exists oinstr, is_instruction_compiled oinstr block) <->
    exists b, Some block = nth_error BPI b /\ pc = length (flatten (firstn b BPI)). 
  Proof.
    split.
    2: { ins. desc. eapply resulting_block_compiled; eauto.
         eapply COMPILED_NONEMPTY; eauto. }
    intros COMP_BLOCK.
    assert (COMP': exists PO, itbc_weak PO BPI).
    { desc. exists PO. red. red in COMP. desc. eauto. }
    clear COMP. 
    generalize dependent BPI.
    set (P := fun pc =>   forall BPI : list (list Instr.t),
  block = sublist (flatten BPI) pc (length block) ->
  (exists PO : list Instr.t, itbc_weak PO BPI) ->
  exists b : nat, Some block = nth_error BPI b /\ pc = length (flatten (firstn b BPI))).
    generalize dependent pc. apply (strong_induction P).
    intros pc IH. red. intros BPI BLOCK COMP.
    destruct BPI as [| blk0 BPI']. 
    { exfalso. unfold sublist in BLOCK.
      desc. 
      destruct pc; simpl in BLOCK; rewrite firstn_nil in BLOCK; inversion COMP_BLOCK; vauto. }
    destruct (ge_dec pc (length blk0)) as [GE | LT].
    { assert (block = sublist (flatten BPI') (pc - length blk0) (length block)).
      { rewrite BLOCK at 1.
        simpl. unfold sublist at 1.
        rewrite skipn_app. unfold sublist.
        rewrite firstn_app.
        rewrite skipn_all2; [| omega]. rewrite firstn_nil. simpl.
        rewrite Nat.sub_0_r. auto. }
      forward eapply (IH (pc - length blk0)) as IHprev. 
      { desc. forward eapply COMPILED_NONEMPTY_weak as NE; eauto.
        inversion NE. subst. destruct blk0; vauto. simpl in *. omega. }
      red in IHprev. forward eapply (IHprev BPI' H) as [b' BLOCK']. 
      { desc. destruct PO as [| oinstr_ PO']. 
        { red in COMP. desc. inversion COMP. subst. inversion COMP0. }
        exists PO'. red. red in COMP. destruct COMP as [BPI0 [BPI0' [COMP CORR]]].
        inversion CORR. subst. inversion COMP. subst. eauto. }
      exists (S b'). desc. split; auto. 
      simpl. rewrite app_length. omega. }
    apply not_ge in LT.
    assert (blk0 = firstn (length blk0) (blk0 ++ flatten BPI')) as BLK0.
    { rewrite <- Nat.add_0_r with (n := length blk0). rewrite firstn_app_2.
      rewrite firstn_O. symmetry. apply app_nil_r. }
    destruct (gt_0_eq pc).
    2: { subst. exists 0. simpl in *. split; auto. f_equal.
         unfold sublist in BLOCK. rewrite skipn_0 in BLOCK.
         eapply (start_block_deterministic (P := fun blk => exists oinstr, is_instruction_compiled oinstr blk)); eauto.
         { apply instr_compiled_min_prop. }
         { desc. pose proof (COMPILED_NONEMPTY_weak COMP).
           inv H. }
         { desc.
           eapply resulting_block_compiled_weak; eauto.
           { eapply COMPILED_NONEMPTY_weak; eauto. }
           Unshelve. 2: exact 0. vauto. }
         desc. inversion COMP_BLOCK; vauto. }
    exfalso.
    forward eapply (@no_acb_between_pc 0 pc pc) as NOACB; eauto. 
    { Unshelve. 2: exact (blk0 ++ flatten BPI'). 
      red. splits; vauto.
      desc. eapply resulting_block_compiled_weak; eauto.
      { eapply COMPILED_NONEMPTY_weak; eauto. }
      Unshelve. 2: exact 0. auto. }
    { omega. }
    apply not_or in NOACB. desc.
    apply NOACB. exists block. red. splits; eauto.
  Qed. 
      
  Lemma acb_iff_bst st BPI
        (COMP: exists PO, is_thread_compiled_with PO (instrs st) BPI):
    at_compilation_block st <-> exists bst, ⟪ST: st = bst2st bst⟫ /\
                                     ⟪BINSTRS: binstrs bst = BPI⟫ /\
                                     ⟪BPC: bpc bst <= length BPI⟫. 
  Proof.
    split.
    { intros ACB. desc. red in COMP. desc.
      red in ACB. des.
      2: { exists (bst_from_st st BPI (length BPI)). splits; auto. 
           unfold bst2st. simpl. rewrite firstn_all. rewrite <- COMP0.
           apply is_terminal_pc_bounded in ACB. rewrite <- ACB.
           apply state_record_equality. }
      red in ACB. desc. 
      forward eapply (@on_block_iff_bindex BPI block (pc st)) as [BLOCK_INDEX _]; vauto. 
      { congruence. }
      forward eapply BLOCK_INDEX as [b [BLOCK PC]]; eauto.
      exists (bst_from_st st BPI b). splits; auto.
      2: { apply Nat.lt_le_incl. apply nth_error_Some, OPT_VAL. eauto. } 
      unfold bst2st, bst_from_st. simpl.
      rewrite <- PC, <- COMP0. apply state_record_equality. }
    intros. desc. red. red in COMP. desc.
    subst. 
    destruct (ge_dec (bpc bst) (length (binstrs bst))) as [TERM | NONTERM].
    { right. apply is_terminal_pc_bounded. 
      simpl.
      rewrite <- firstn_skipn with (n := bpc bst) (l := binstrs bst) at 2.
      rewrite skipn_all2; [| auto]. 
      rewrite app_nil_r. auto. }
    apply not_ge in NONTERM. left.
    apply nth_error_Some, OPT_VAL in NONTERM. destruct NONTERM as [block BLOCK].
    exists block. apply st_bst_prog_blocks; eauto. 
  Qed. 

  Lemma ll_index_shift' {A: Type} (ll: list (list A)) i j
         block (ITH: Some block = nth_error ll i) (NE: Forall (fun l => l <> []) ll)
         (J_BOUND: j <= length ll)
         (JI: j = i + 1):
    length (flatten (firstn j ll)) = length (flatten (firstn i ll)) + length block.
  Proof.
    subst. erewrite first_end; eauto.
    rewrite flatten_app, length_app. simpl. rewrite app_nil_r. auto.
  Qed.       

  Definition non_igt instr :=
    ~ match instr with | Instr.ifgoto _ _ => True | _ => False end. 

  Lemma regular_pc_change st1 st2 tid (STEP: step tid st1 st2)
        instr (AT_PC: Some instr = nth_error (instrs st1) (pc st1))
        (NOT_IGT: non_igt instr):
    pc st2 = pc st1 + 1.
  Proof.
    do 2 (red in STEP; desc). red in NOT_IGT. 
    inversion ISTEP0; auto.
    assert (instr = instr0) by congruence. subst. vauto.
  Qed. 
                                                    
  Lemma steps_pc_change st1 st2 tid block (ON_BLOCK: on_block st1 block)
        (STEPS: (step tid) ^^ (length block) st1 st2):
  pc st2 = pc st1 + length block \/
  (exists (cond : Instr.expr) (addr : nat),
      block = [Instr.ifgoto cond addr] /\ pc st2 = addr).
  Proof.
    red in ON_BLOCK. desc.
    destruct block as [| instr block'].
    { inversion COMP_BLOCK. }
    assert ([instr] = sublist (instrs st1) (pc st1) 1).
    { unfold sublist in *. simpl in PROG_BLOCK.
      simpl. destruct (skipn (pc st1) (instrs st1)); vauto. }
    assert (AT_PC: Some instr = nth_error (instrs st1) (pc st1)).
    { apply eq_trans with (y := nth_error [instr] 0); auto.
      rewrite <- (NPeano.Nat.add_0_r (pc st1)).
      eapply sublist_items; eauto. }
    destruct block' as [| instr' block''].
    { 
      inversion COMP_BLOCK.
      3: { subst. simpl in *.
           apply (same_relation_exp (seq_id_l (step tid))) in STEPS.
           do 2 (red in STEPS; desc).
           (* actually most cases here are nonsense, but they still fit into lemma statement *)
           inversion ISTEP0; auto.
           subst instr.
           destruct (Const.eq_dec (RegFile.eval_expr (regf st1) expr) 0); auto.
           right. exists e. exists n. split; eauto. 
           assert (igt = Instr.ifgoto expr shift) by congruence.
           inversion H0. auto. }    
      all: left; subst; simpl in *.
      all: try apply (same_relation_exp (seq_id_l (step tid))) in STEPS.
      all: eapply regular_pc_change; vauto. }
    left. 
    assert ([instr;  instr'] = sublist (instrs st1) (pc st1) 2).
    { unfold sublist in *. simpl in PROG_BLOCK.
      simpl. destruct (skipn (pc st1) (instrs st1)); vauto.
      destruct l; vauto. }
    assert (AT_PC': Some instr' = nth_error (instrs st1) (pc st1 + 1)).
    { apply eq_trans with (y := nth_error [instr; instr'] 1); auto.
      eapply sublist_items; eauto. }
    simpl. 
    simpl in STEPS. red in STEPS. desc. red in STEPS. desc.
    assert (forall st' (STEP1: step tid st1 st') (STEP2: step tid st' st2)
              (NOT_IGT1: non_igt instr) (NOT_IGT2: non_igt instr'),
               pc st2 = pc st1 + 2) as STEPS2_HELPER. 
    { ins.
      assert (pc st' = pc st1 + 1) by (eapply regular_pc_change; eauto). 
      replace (pc st2) with (pc st' + 1); [omega| ]. 
      symmetry. eapply regular_pc_change; eauto.
      replace (instrs st') with (instrs st1); [congruence |].
      do 2 (red in STEP1; desc). auto. }
    
    inversion COMP_BLOCK; subst; simpl in *; red in STEPS; subst; desc.
    all: forward eapply STEPS2_HELPER; vauto.
  Qed.
    
  Lemma oseq_continuos st1 st2 tid (OSEQ: (oseq_step tid) st1 st2)
        (COMP: exists PO, is_thread_compiled PO (instrs st1)):
    at_compilation_block st2.
  Proof.
    red in OSEQ. desc.
    red in COMP. desc. 
    assert (exists bst1, st1 = bst2st bst1 /\ binstrs bst1 = BPI /\ bpc bst1 <= length BPI) as [bst1 [BST1 [BINSTRS1 BPC1]]].
    { apply acb_iff_bst; eauto. red. eauto. }
    assert (Some block = nth_error (binstrs bst1) (bpc bst1)) as BLOCK. 
    { apply st_bst_prog_blocks; vauto.
      exists PO. red in COMP. desc. auto. }
    forward eapply steps_pc_change as PC2; eauto.
    assert (forall blc (STEPS: (step tid) ^^ (length blc) st1 st2)
              (BLC: Some blc = nth_error (binstrs bst1) (bpc bst1))
              (PC_PLUS: pc st2 = pc st1 + length blc),
               at_compilation_block st2) as NEXT_BLOCK. 
    { ins. forward eapply acb_iff_bst as [_ ACB_IF_BST].  
      { exists PO. rewrite <- (@steps_same_instrs st1 st2); eauto.
        exists tid. apply crt_num_steps. eauto. }
      apply ACB_IF_BST. 
      exists (bst_from_st st2 (binstrs bst1) (bpc bst1 + 1)).
      splits; auto.
      2: { simpl. apply le_lt_or_eq in BPC1. destruct BPC1; [omega |]. 
           subst.
           pose proof (proj2 (nth_error_None (binstrs bst1) (bpc bst1))).
           forward eapply H0; [omega| ]. ins. congruence. }      
      unfold bst2st. simpl.
      replace (flatten (binstrs bst1)) with (instrs st2).
      2: { rewrite <- (@steps_same_instrs st1 st2); [subst; eauto| ].
           exists tid. apply crt_num_steps. eauto. }
      red in OSEQ. desc.
      clear dependent oinstr. (* to avoid confusion with actual initial oinstr *)
      erewrite ll_index_shift'; eauto.
      3: { cut (bpc bst1 < length (binstrs bst1)); [ins; omega|].
           apply nth_error_Some, OPT_VAL. vauto. }
      2: { eapply COMPILED_NONEMPTY. Unshelve. 2: exact PO.
           red in COMP. desc. vauto. }
      subst st1. unfold bst2st in PC_PLUS. simpl in PC_PLUS. 
      rewrite <- PC_PLUS. 
      apply state_record_equality. }
    
    destruct PC2 as [PC2 | PC2]. 
    - eapply NEXT_BLOCK; eauto. 
    - desc. subst addr. (* subst block. *) simpl in *. 
      red in COMP. desc.
      subst BPI. 
      red in COMP. desc. 
      assert (exists oinstr, Some oinstr = nth_error PO (bpc bst1)) as [oinstr OINSTR]. 
      { apply OPT_VAL. apply nth_error_Some.
        replace (length PO) with (length (binstrs bst1)).
        { apply nth_error_Some, OPT_VAL. eauto. }
        symmetry. apply compilation_same_length. red; vauto. }    
      assert (exists block0, Some block0 = nth_error BPI0 (bpc bst1)) as [block0 BLOCK0].
      { apply OPT_VAL. apply nth_error_Some.
        replace (length BPI0) with (length (binstrs bst1)).
        { apply nth_error_Some, OPT_VAL. eauto. }
        symmetry. eapply Forall2_length. eauto. }
      assert (is_instruction_compiled oinstr block0) as COMP_BLOCK.
      { eapply Forall2_index; eauto. } 
      assert (block_corrected BPI0 block0 block) as CORR_BLOCK.
      { eapply Forall2_index; eauto. } 
      subst block.
      inversion CORR_BLOCK. inversion H3. subst. 
      inversion H2; vauto. subst addr.
      inversion COMP_BLOCK. subst. 
      simpl in OSEQ0. apply (same_relation_exp (seq_id_l (step tid))) in OSEQ0.
      do 2 (red in OSEQ0; desc).
      assert (instr = Instr.ifgoto cond (pc st2)).
      { forward eapply (@near_pc (Instr.ifgoto cond (pc st2)) _ 0) as AT_PC; eauto.
        { vauto. }
        { apply nth_error_Some, OPT_VAL. eauto. }
        rewrite Nat.add_0_r in AT_PC. congruence. }
      subst instr. 
      inversion ISTEP0. 
      all: try discriminate.
      destruct (Const.eq_dec (RegFile.eval_expr (regf (bst2st bst1)) expr) 0). 
      + eapply NEXT_BLOCK; eauto. simpl.
        apply (same_relation_exp (seq_id_l (step tid))).
        red. eexists. red. eauto.
      + subst.
        inversion CORR_BLOCK. subst. inversion H4; vauto.
        forward eapply acb_iff_bst as [_ ACB_IF_BST]. 
        { rewrite <- INSTRS. exists PO. simpl. red. splits; eauto. 
          vauto. }
        apply ACB_IF_BST. 
        exists (bst_from_st st2 (binstrs bst1) addr0). splits; auto.
        2: { simpl.
             replace (length (binstrs bst1)) with (length PO).
             2: { apply compilation_same_length. vauto. }
             eapply compilation_addresses_restricted; vauto. }
        unfold bst2st. simpl.
        replace (flatten (binstrs bst1)) with (instrs st2).
        replace (length (flatten (firstn addr0 (binstrs bst1)))) with (length (flatten (firstn addr0 BPI0))).
        2: { apply SAME_STRUCT_PREF. eapply correction_same_struct; eauto. } 
        rewrite H5. apply state_record_equality.
  Qed.   
  
  (* had to define it separately since otherwise Coq doesn't understand what P is *)
  Definition StepProp n := forall st1 st2 tid (STEPS: (step tid) ^^ n st1 st2)
                             bst1 (BST1: st1 = bst2st bst1)
                             bst2 (BST2: st2 = bst2st bst2)
                             (BOUND1: bpc bst1 <= length (binstrs bst1))
                             (BOUND2: bpc bst2 <= length (binstrs bst2))
                             (COMP: exists PO, is_thread_block_compiled PO (binstrs bst1))
                             (SAME_BINSTRS: binstrs bst1 = binstrs bst2),
      (omm_block_step tid)＊ bst1 bst2.

  Lemma oseq_between_acb: forall n, StepProp n.
  Proof.
    apply strong_induction. 
    unfold StepProp. intros n IH. ins. desc.
    assert (at_compilation_block st1) as ACB1.
    { eapply acb_iff_bst; eauto.
      unfold is_thread_compiled_with. exists PO.
      split; [congruence| ]. rewrite BST1. simpl. congruence. }
    assert (at_compilation_block st2) as ACB2.
    { forward eapply (@acb_iff_bst st2) as [_ ACB_IF_BST]; eauto.
      { exists PO. red. split; eauto. rewrite SAME_BINSTRS. vauto. }
      apply ACB_IF_BST. exists bst2. splits; vauto. congruence. }
    assert (bst2st bst1 = bst2st bst2 -> (omm_block_step tid)＊ bst1 bst2) as WHEN_SAME_BST. 
    { intros SAME_BST2ST. 
      replace bst2 with bst1; [apply rt_refl| ].
      rewrite blockstate_record_equality.
      rewrite blockstate_record_equality with (bst := bst1).
      f_equal; vauto. 
      rewrite <- SAME_BINSTRS in BOUND2. 
      eapply (@NONEMPTY_PREF _ (binstrs bst1)); eauto.
      2: congruence.
      eapply COMPILED_NONEMPTY; eauto. }
      
    unfold at_compilation_block in ACB1. desf. 
    2: { destruct n.
         { apply WHEN_SAME_BST. apply steps0 in STEPS. auto. }
         forward eapply (@steps_sub _ (step tid) (S n) _ _ 1) as [st' STEP];
           [omega | eauto |].
         apply (same_relation_exp (pow_unit (step tid))) in STEP.
         do 2 (red in STEP; desc). 
         cut (None = nth_error (instrs (bst2st bst1)) (pc (bst2st bst1))); [congruence| ].
         symmetry. apply nth_error_None. red in ACB1. omega. }
    pose proof (le_lt_dec (length block) n) as LEN. destruct LEN.
    { forward eapply (steps_split (step tid) (length block) (n - length block)) as SPLIT.
      { symmetry. apply le_plus_minus. auto. }
      apply SPLIT in STEPS. destruct STEPS as  [st' [PREV_STEPS NEXT_STEPS]]. clear SPLIT.
      assert (oseq_step tid (bst2st bst1) st') as OSEQ. 
      { red. eexists. eauto. }
      forward eapply (oseq_continuos OSEQ) as ACB'; vauto.
      assert (exists PO', is_thread_compiled PO' (instrs st')) as COMP'.
      { replace (instrs st') with (instrs (bst2st bst1)); vauto.
        apply steps_same_instrs. exists tid.
        (* remove duplicated proof *)
        red in OSEQ. desc. rewrite crt_num_steps. eexists. eauto. }
      assert (LEN': n - length block < n).
      { red in ACB1. desc. inversion COMP_BLOCK; subst; simpl in *; omega. }
      forward eapply (@acb_iff_bst st' (binstrs bst1)) as [BST_IF_ACB _].
      { exists PO. red. split; auto.
        replace (instrs st') with (instrs (bst2st bst1)); auto.
        apply steps_same_instrs; eauto. exists tid. apply crt_num_steps. eauto. }
      specialize (BST_IF_ACB ACB'). destruct BST_IF_ACB as [bst' [BST' [SAME_BINSTRS' BPC']]]. 
      forward eapply IH as IH_; eauto.
      { rewrite SAME_BINSTRS'. auto. }
      { exists PO. congruence. }
      { congruence. }
      apply clos_trans_in_rt. apply t_step_rt. exists bst'. split; auto. 
      red. splits; vauto. 
      exists block. red. splits; auto.
      apply st_bst_prog_blocks; eauto. rewrite <- BST'. auto. }
    destruct (NPeano.Nat.eq_0_gt_0_cases n).
    { subst. apply steps0 in STEPS. apply WHEN_SAME_BST. auto. }
    forward eapply no_acb_between; eauto; [omega | vauto]. 
  Qed. 
    
  Definition is_block_terminal bst := bpc bst >= length (binstrs bst). 

  Lemma steps_imply_ommblocks bfin (BPC_LIM: bpc bfin <= length (binstrs bfin)) tid (* (TERM: is_block_terminal bfin) *)
        (COMP: exists PO, is_thread_block_compiled PO (binstrs bfin)):
    let fin := (bst2st bfin) in 
    (step tid)＊ (init (instrs fin)) fin -> (omm_block_step tid)＊ (binit (binstrs bfin)) bfin.
  Proof.
    intros fin STEPS. apply crt_num_steps in STEPS as [n STEPS].
    eapply oseq_between_acb; eauto.
    simpl. omega.
  Qed. 
    
  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI) (* (WFL: Wf_local SGI) *):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI
           (* /\ Wf_local SGO *)
  . 
  Proof.
    red in ExI. destruct ExI as [sti_fin ExI]. desc.
    apply (@crt_num_steps _ (step tid) (init PI) sti_fin) in STEPS as [n_isteps ISTEPS].
    assert (SAME_INSTRS: PI = instrs sti_fin). 
    { replace PI with (instrs (init PI)); auto. 
      apply steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
    red in COMP. desc.
    set (bsti_fin := {|
          binstrs := BPI;
          bpc := length BPI;
          bG := G sti_fin;
          beindex := eindex sti_fin;
          bregf := regf sti_fin;
          bdepf := depf sti_fin;
          bectrl := ectrl sti_fin |}). 
    assert (sti_fin = bst2st bsti_fin) as BST. 
    { unfold bst2st. 
      simpl.
      rewrite firstn_all.
      red in COMP. desc.
      rewrite <- COMP0.
      rewrite SAME_INSTRS.
      apply is_terminal_pc_bounded in TERMINAL. 
      rewrite <- TERMINAL; auto.
      (* TODO: why so complicated? *)      
      apply state_record_equality. } 
    
    assert (is_block_terminal bsti_fin) as BLOCK_TERM. 
    { red. destruct (dec_ge (bpc bsti_fin) (length (binstrs bsti_fin))); auto. }
    assert (exists n_osteps, (omm_block_step tid) ^^ n_osteps (binit BPI) bsti_fin) as [n_osteps OMM_STEPS]. 
    { apply crt_num_steps.
      forward eapply (@steps_imply_ommblocks bsti_fin _ tid); eauto.
      { exists PO. red in COMP. desc. auto. }
      Unshelve. 2: simpl; omega. 
      rewrite <- BST. apply crt_num_steps.
      rewrite <- SAME_INSTRS. eauto. }
    
    assert (BY_STEPS:
              forall i bsti_i (INDEX: i <= n_osteps)
                (STEPS_TO: (omm_block_step tid)^^i (binit BPI) bsti_i)
                (STEPS_FROM: (omm_block_step tid)^^(n_osteps - i) bsti_i bsti_fin),
                 exists sto_i,
                 (Ostep tid)^^i (init PO) sto_i /\
                 mm_similar_states sto_i bsti_i /\
                 pc sto_i <= length PO).
    { induction i.
      - intros bsti_i _ STEPS_TO STEPS_FROM.
        exists (init PO). splits; [basic_solver| | simpl; omega].
        replace (bsti_i) with (binit BPI); [apply init_mm_same; auto| ].
        { red in COMP. desc. auto. }
        generalize STEPS_TO. simpl. basic_solver 10.
      - intros bsti_i INDEX STEPS_TO STEPS_FROM.
        rewrite step_prev in STEPS_TO.
        destruct STEPS_TO as [bsti_i' [STEPS_TO' STEPS_FROM']].
        forward eapply IHi as [sto' [OSTEPS' [MM_SIM' PCO_BOUND]]]. 
        { omega. }
        { eauto. }
        { apply (@steps_split _ _ _ 1 (n_osteps - S i)); [omega| ].
          eexists. split; eauto. simpl. basic_solver. }

        forward eapply (@clos_refl_trans_mori _ (omm_block_step tid) (block_step tid)).
        { red. ins. apply bs_extract. auto. }
        intros OB_B.
        assert (bpc bsti_i <= length (binstrs bsti_i')) as BPC_BOUND.
        { replace (binstrs bsti_i') with (binstrs bsti_i).
          2: { red in STEPS_FROM'. desc. auto. }
          destruct (gt_0_eq (n_osteps - S i)) as [GT | FIN].
          2: { rewrite <- FIN in STEPS_FROM.
               apply (steps0 (omm_block_step tid)) in STEPS_FROM.
               subst bsti_i. auto. }
          apply Nat.lt_le_incl. apply nth_error_Some, OPT_VAL. 
          apply steps_sub with (m := 1) in STEPS_FROM; [| omega].
          destruct STEPS_FROM as [bst_next STEP_NEXT].
          apply (same_relation_exp (pow_unit (omm_block_step tid))) in STEP_NEXT. 
          red in STEP_NEXT. desc. red in BLOCK_STEP. desc. eauto. }          
        assert (bpc bsti_i' <= length (binstrs bsti_i')).
        { red in MM_SIM'. desc. rewrite <- MM_SIM'0.
          replace (length (binstrs bsti_i')) with (length PO); auto.
          apply compilation_same_length.
          replace PO with (instrs sto'); auto.
          replace PO with (instrs (init PO)) by vauto.
          symmetry. apply omm_steps_same_instrs. exists tid. apply <- crt_num_steps. eauto. }
        assert (SAME_BINSTRS': BPI = binstrs bsti_i').
        { replace BPI with (binstrs bsti_fin); auto. symmetry. 
          apply (@inclusion_t_ind _ (block_step tid) (fun x y => binstrs x = binstrs y)).
          { red. ins. eapply SAME_BINSTRS. eauto. }
          { red. ins. congruence. }
          apply t_step_rt. exists bsti_i. split.
          { apply bs_extract. auto. }
          apply OB_B. apply crt_num_steps. eexists. eauto. }

        forward eapply (pair_step MM_SIM' STEPS_FROM') as [sto [OSTEP MM_SIM]]; eauto. 
        { apply OB_B. apply crt_num_steps. exists i.
          replace (binstrs bsti_i') with BPI; auto. }
        exists sto. splits; eauto.
        2: { red in MM_SIM. desc.
             replace (length PO) with (length (binstrs bsti_i')); [omega|].
             replace (binstrs bsti_i') with BPI; auto.
             symmetry. apply compilation_same_length.
             red in COMP. desc. auto. }
        apply step_prev. eexists. splits; eauto. }
    
    forward eapply (BY_STEPS n_osteps bsti_fin (Nat.le_refl n_osteps)) as [sto_fin [OSTEPS [MM_SIM PC_BOUND]]].
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
      replace (length (instrs sto_fin)) with (length (binstrs bsti_fin)).
      2: { symmetry. apply compilation_same_length. rewrite <- SAME_OINSTRS.
           subst bsti_fin. simpl. red in COMP. desc. auto. }
      replace (pc sto_fin) with (bpc bsti_fin).
      2: { red in MM_SIM. desc. auto. }
      apply BLOCK_TERM. }
    { red in MM_SIM. desc.
      replace SGI with (bG bsti_fin); auto. }
  Qed. 

  (* Lemma same_beh_implies_similar_rels GO GI (SB: same_behavior GO GI): *)
  (*   ⟪ SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘⟫ /\ *)
  (*   (* ⟪ SC': Sc GO ≡₁ Sc GI ⟫ /\ *) *)
  (*   ⟪ SC': Sc GO ≡₁ RWO GI ∩₁ Sc GI ⟫ /\ *)
  (*   ⟪ FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI ⟫. *)
  (* Proof. *)
  (*   red in SB. des. red in SAME_LOCAL. desc. *)
  (*   splits. *)
  (*   { unfold Execution.sb. *)
  (*     rewrite !seqA. do 2 seq_rewrite <- id_inter. *)
  (*     rewrite set_interC.       *)
  (*     rewrite <- RESTR_EVENTS. auto. } *)
  (*   { admit. } *)
  (*   admit.  *)
  (* (*   red in SB. desc. red in SAME_LOCAL. desc.  *) *)
  (* (*   assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘). *) *)
  (* (*   { unfold Execution.sb.         *) *)
  (* (*     rewrite !seqA. do 2 seq_rewrite <- id_inter. *) *)
  (* (*     rewrite set_interC.  *) *)
  (* (*     rewrite RESTR_EVENTS.  *) *)
  (* (*     basic_solver. } *) *)
  (* (*   splits; auto.  *) *)
  (* (*   { rewrite SAME_LAB. auto. } *) *)
  (* (*   { unfold fr. rewrite SAME_CO. rewrite <- seqA. apply seq_more; [| basic_solver]. *) *)
  (* (*     rewrite EXT_RF.  basic_solver. } *) *)
  (*   (* Qed.  *) *)
  (* Admitted.  *)

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

  Lemma same_beh_implies_similar_intrarels GO GI (SB: same_behavior GO GI):
    ⟪DATA_SIM: data GO ≡ restr_rel (RWO GI) (data GI) ⟫ /\
    ⟪CTRL_SIM: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI) ⟫ /\ 
    ⟪ADDR_SIM: addr GO ≡ restr_rel (RWO GI) (addr GI) ⟫ /\
    ⟪SB_SIM: sb GO ≡ restr_rel (RWO GI) (sb GI) ⟫ /\
    ⟪NO_RMW: rmw GO ≡ ∅₂ ⟫ /\
    ⟪NO_RMWDEP: rmw_dep GO ≡ ∅₂ ⟫.
  Proof. Admitted.     

  Lemma SUPSET_RESTR {A: Type} (r1 r2: relation A) S (INCL: r1 ⊆ r2) (RESTR: r2 ≡ ⦗S⦘ ⨾ r2 ⨾ ⦗S⦘):
    r1 ≡ ⦗S⦘ ⨾ r1 ⨾ ⦗S⦘. 
  Proof.
    ins. split; [| basic_solver].
    red. ins. apply seq_eqv_lr.
    red in RESTR. desc. red in RESTR.
    red in INCL. 
    pose proof (INCL x y H) as R2.
    specialize (RESTR x y R2). apply seq_eqv_lr in RESTR. desc.
    splits; auto.
  Qed.

  Lemma RESTR_SEQ (r1 r2: relation actid) (D: actid -> Prop):
    restr_rel D r1 ⨾ restr_rel D r2 ⊆ restr_rel D (r1 ⨾ r2). 
  Proof. ins. basic_solver. Qed.

  (* TODO: generalize all of it*)
  Lemma W_SIM GO GI (SBL: same_behavior_local GO GI):
    E GO ∩₁ W GO ≡₁ E GO ∩₁ W GI.
  Proof. 
    red in SBL. apply set_equiv_exp_iff.
    ins. split.
    { ins. red in H. desc. red. split; auto.
      unfold is_w. rewrite <- (SAME_LAB); auto. }
    { ins. red in H. desc. red. split; auto.
      unfold is_w. rewrite (SAME_LAB); auto. }
  Qed.
  
  Lemma R_SIM GO GI (SBL: same_behavior_local GO GI):
    E GO ∩₁ R GO ≡₁ E GO ∩₁ R GI.
  Proof.
    red in SBL. apply set_equiv_exp_iff.
    ins. split.
    { ins. red in H. desc. red. split; auto.
      unfold is_r. rewrite <- (SAME_LAB); auto. }
    { ins. red in H. desc. red. split; auto.
      unfold is_r. rewrite (SAME_LAB); auto. }
  Qed. 

  Lemma RW_SIM GO GI (SBL: same_behavior_local GO GI)
    : E GO ∩₁ RW GO ≡₁ E GO ∩₁ RW GI.
  Proof. rewrite !set_inter_union_r. rewrite W_SIM, R_SIM; eauto. Qed. 

  
  Lemma SC_SIM GO GI (SBL: same_behavior_local GO GI):
    E GO ∩₁ Sc GO ≡₁ E GO ∩₁ Sc GI.
  Proof.
    red in SBL. apply set_equiv_exp_iff.
    ins. split.
    { ins. red in H. desc. red. split; auto.
      unfold is_sc, Events.mod. rewrite <- (SAME_LAB); auto. }
    { ins. red in H. desc. red. split; auto.
      unfold is_sc, Events.mod. rewrite (SAME_LAB); auto. }
  Qed. 

  Lemma Wf_subgraph GO GI (SAME_BEH: same_behavior GO GI) (WF: Wf GI): Wf GO.
  Proof.
    pose proof SAME_BEH as SAME_BEH'.
    red in SAME_BEH. desc. red in SAME_LOCAL. desc.
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { unfold Execution.sb.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC.
      rewrite RESTR_EVENTS.
      basic_solver. }
    (* pose proof (same_beh_implies_similar_rels SAME_BEH).  *)
    symmetry in SAME_CO.
    assert (forall (r1 r2 r3: relation actid), r1 ⊆ r2 -> r1 \ r3 ⊆ r2 \r3) as MINUS_INCL. 
    { ins. basic_solver. }
    assert (forall (r1 r3: relation actid) S1 S2, r1 ≡ ⦗S1⦘ ⨾ r1 ⨾ ⦗S2⦘ -> r1 \ r3 ≡ ⦗S1⦘ ⨾ (r1 \ r3) ⨾ ⦗S2⦘) as MINUS_EQUIV. 
    { ins. seq_rewrite H. basic_solver. }
    (* TODO: should we include addr, ctrl equality in same_behavior? *)
    pose proof (same_beh_implies_similar_intrarels SAME_BEH'). desc. 
    inversion WF. 
    (* assert (rf GO ≡ restr_rel (RWO GI) (rf GI)) as RF_SIM.  *)
    (* { rewrite EXT_RF. rewrite wf_rfD. rewrite restr_relE. *)
    (*   rewrite !seqA. *)
    (*   arewrite (⦗(RWO GI)⦘ ⨾ ⦗W GI⦘ ≡ ⦗W GI⦘). *)
    (*   { rewrite <- id_inter. apply eqv_rel_more. split; [basic_solver| ]. *)
    (*     apply set_subset_inter_r. split; auto. *)
    (*     unfold RWO.  *)
    (*     rewrite wf_rmwD. *)
    (*     red. ins. red. split; [basic_solver| ].  *)
    (*     red. ins. red in H0. desc. apply seq_eqv_lr in H0. desc. *)
    (*     type_solver. } *)
    (*   arewrite (⦗R GI⦘ ⨾ ⦗(RWO GI)⦘ ≡ ⦗R GI⦘ ⨾ ⦗set_compl (dom_rel (rmw GI))⦘); [| basic_solver]. *)
    (*   rewrite <- !id_inter. apply eqv_rel_more. *)
    (*   unfold RWO.  *)
    (*   seq_rewrite set_inter_minus_r. *)
    (*   arewrite (R GI ∩₁ RW GI ≡₁ R GI) by basic_solver. } *)
    assert (co GO ≡ ⦗E GO⦘ ⨾ co GO ⨾ ⦗E GO⦘) as ECO. 
    { rewrite RESTR_EVENTS, <- SAME_CO.
      rewrite !id_inter. rewrite seq_eqvC. rewrite seqA. rewrite seq_eqvC.
      seq_rewrite <- wf_coE.
      split; [| basic_solver].
      rewrite wf_coD at 1.
      assert (W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
      { apply inclusion_minus. split; [basic_solver |].
        rewrite wf_rmwD. type_solver. }
      apply seq_mori.
      { apply eqv_rel_mori. auto. }
      apply seq_mori; [basic_solver|].
      apply eqv_rel_mori. auto. }
    assert (rf GO ≡ ⦗E GO⦘ ⨾ rf GO ⨾ ⦗E GO⦘) as ERF. 
    { rewrite RESTR_RF, RESTR_EVENTS. fold (RWO GI).
      rewrite set_interC at 1. do 2 rewrite id_inter.
      rewrite !seqA. do 2 seq_rewrite <- restr_relE.
      rewrite restrC with (d' := (RWO GI)). rewrite restr_restr, set_interK.
      apply restr_rel_more; [basic_solver|].
      rewrite restr_relE. auto. }
    
    assert (DATA_INCL: data GO ⊆ sb GO).
    { rewrite DATA_SIM, SB_SIM. apply restr_rel_mori; basic_solver. }
    assert (ADDR_INCL: addr GO ⊆ sb GO).
    { rewrite ADDR_SIM, SB_SIM. apply restr_rel_mori; basic_solver. }
    assert (CTRL_INCL: ctrl GO ⊆ sb GO).
    { rewrite CTRL_SIM, SB_SIM. apply restr_rel_mori; basic_solver. }
    
    (* red in SAME_BEH'. desc.   *)
    split; vauto.
    all: try (seq_rewrite NO_RMW; basic_solver). 
    all: try (seq_rewrite NO_RMWDEP; basic_solver). 
    { ins. des.
      specialize (wf_index a b). forward eapply wf_index; auto.
      destruct RESTR_EVENTS as [EGO_EGI _]. red in EGO_EGI.
      splits; auto.
      { specialize (EGO_EGI a H). red in EGO_EGI. desc. auto. } 
      specialize (EGO_EGI b H0). red in EGO_EGI. desc. auto. }
    { rewrite (@SUPSET_RESTR _ (data GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite W_SIM, R_SIM; eauto. 
      rewrite set_interC with (s' := W GI). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗W GI⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite DATA_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      apply restr_rel_more; auto. red. splits; auto. red. splits; auto. }
    { rewrite (@SUPSET_RESTR _ (addr GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite R_SIM, RW_SIM; eauto. 
      rewrite set_interC with (s' := RW GI). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗RW GI⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite ADDR_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l. 
      apply restr_rel_more; auto. red. splits; auto. red. splits; auto. }
    { rewrite <- (seq_id_r (ctrl GO)) at 2.  
      rewrite (@SUPSET_RESTR _ (ctrl GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite R_SIM; eauto. (* TRUE_SIM. *)
      rewrite set_interC with (s' := (fun _ : actid => True)). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗fun _ : actid => True⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite CTRL_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      rewrite seq_id_r. 
      apply restr_rel_more; auto.
      red. splits; auto. }
    { rewrite CTRL_SIM, SB_SIM. rewrite RESTR_SEQ. apply restr_rel_mori; auto. }
    { rewrite ERF.
      rewrite RESTR_RF; eauto. 
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. rewrite W_SIM, R_SIM; eauto. 
      rewrite set_interC with (s' := R GI). rewrite !id_inter.
      rewrite !seqA. seq_rewrite <- !restr_relE.
      rewrite <- seqA with  (r3 := ⦗E GO⦘). rewrite <- seqA with  (r1 := ⦗W GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; [basic_solver|].
      rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      apply restr_rel_more; [basic_solver|]. auto.
      red. splits; auto. red. splits; auto. }
    { rewrite ERF. red. ins.
      apply seq_eqv_lr in H. desc.
      red.
      rewrite (same_relation_exp RESTR_RF) in H0. red in H0. desc. 
      replace (loc (lab GO) x) with (loc (lab GI) x).
      replace (loc (lab GO) y) with (loc (lab GI) y).
      apply wf_rfl; auto.
      all: unfold loc; rewrite SAME_LAB; auto. }
    { red. ins.
      rewrite (same_relation_exp ERF) in H. apply seq_eqv_lr in H. desc.
      rewrite (same_relation_exp RESTR_RF) in H0. red in H0. desc.
      replace (val (lab GO) a) with (val (lab GI) a).
      replace (val (lab GO) b) with (val (lab GI) b).
      apply wf_rfv; auto. 
      all: unfold val; rewrite SAME_LAB; auto. }
    { rewrite RESTR_RF. rewrite restr_relE. rewrite !transp_seq.
      rewrite !transp_eqv_rel. rewrite seqA, <- restr_relE.
      apply functional_restr. auto. }
    { rewrite ECO at 2.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. rewrite W_SIM; eauto. 
      rewrite set_interC at 2. do 2 rewrite id_inter.
      rewrite <- SAME_CO at 2. rewrite !seqA. seq_rewrite <- wf_coD.
      rewrite SAME_CO. apply ECO.
      red. splits; auto. }
    { rewrite ECO. red. ins.
      apply seq_eqv_lr in H. desc.
      red.
      symmetry in SAME_CO. 
      rewrite (same_relation_exp SAME_CO) in H0.
      replace (loc (lab GO) x) with (loc (lab GI) x).
      replace (loc (lab GO) y) with (loc (lab GI) y).
      apply wf_col; auto.
      all: unfold loc; rewrite SAME_LAB; auto. }
    { rewrite <- SAME_CO. auto. }
    { ins. specialize (wf_co_total ol).
      forward eapply (@is_total_more _ (E GI ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol)) (E GO ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol))).
      { apply set_equiv_inter; [| basic_solver].
        rewrite RESTR_EVENTS.
        unfold RWO. 
        rewrite set_interA. rewrite set_inter_minus_l.
        arewrite (RW GI ∩₁ W GI ≡₁ W GI) by basic_solver.
        rewrite empty_inter_minus_same; [auto| ]. 
        rewrite wf_rmwD. type_solver. }
      { eapply SAME_CO. }
      intros [impl _].
      arewrite (E GO ∩₁ W GO ∩₁ (fun x : actid => loc (lab GO) x = ol) ≡₁ E GO ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol)). 
      2: { apply impl. auto. }
      rewrite W_SIM; eauto. 
      apply set_equiv_exp_iff. ins. split.
      { ins. desc. red in H. desc. red in H. desc.
        red. split; [basic_solver|].
        rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. } 
      { ins. desc. red in H. desc. red in H. desc.
        red. split; [basic_solver|].
        rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. }
      red. splits; auto. }
    { rewrite <- SAME_CO. auto. }
    { ins.
      eapply SAME_INIT.
      red. splits; auto.
      apply wf_init. desc.
      exists b. split.
      { apply RESTR_EVENTS. auto. }
      rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. }
    intros. rewrite SAME_INIT_LAB. 
    apply wf_init_lab. 
  Qed.

  
End OCamlMM_TO_IMM_S_PROG.

Section CompCorrHelpers.

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

  Fixpoint find_max_event default events :=
    match events with
    | [] => default
    | ev :: events' => find_max_event (if Nat.leb (index default) (index ev) then ev else default) events'
    end. 

  Lemma step_label_ext_helper st1 st2 tid new_label index
        (IND: index >= eindex st1)
        (ADD: exists foo bar baz bazz,
            G st2 = add (G st1) tid index new_label foo bar baz bazz)
        n (REACH: (step tid) ^^ n (init (instrs st1)) st1):
    let lbl_ext (S: (actid -> label) -> actid -> bool)
                (matcher : label -> bool) :=
        S (lab (G st2)) ≡₁ S (lab (G st1)) ∪₁ (if matcher new_label then eq (ThreadEvent tid index) else ∅) in
    ⟪E_EXT: E (G st2) ≡₁ E (G st1) ∪₁ eq (ThreadEvent tid index) ⟫ /\
    ⟪RMW_EXT: rmw (G st2) ≡ rmw (G st1) ⟫ /\
    ⟪SB_EXT: E (G st1) ≡₁ ∅ \/ exists max_event,
         immediate (sb (G st2)) ≡ immediate (sb (G st1)) ∪ singl_rel  max_event (ThreadEvent tid index) ⟫ /\
    ⟪R_EXT: lbl_ext (@is_r actid) r_matcher ⟫ /\
    ⟪W_EXT: lbl_ext (@is_w actid) w_matcher ⟫ /\
    ⟪F_EXT: lbl_ext (@is_nonnop_f actid) nonnop_f_matcher ⟫ /\
    ⟪ACQ_EXT: lbl_ext (@is_acq actid) acq_matcher ⟫ /\
    ⟪SC_EXT: lbl_ext (@is_sc actid) sc_matcher⟫ .
  Proof. 
    pose proof label_set_step as LBL_STEP. 
    specialize LBL_STEP with (st1 := st1) (st2 := st2) (tid := tid) (index := index).
    Hint Resolve r_pl w_pl nonnop_f_pl acq_pl sc_pl : label_ext. 
    simpl. splits.
    { desc. rewrite ADD. unfold acts_set. basic_solver. }
    { desc. rewrite ADD. basic_solver. }
    { destruct (acts (G st1)) eqn:events.
      { left. unfold acts_set. rewrite events. basic_solver. }
      right. exists (find_max_event a l). 
      desc. rewrite ADD. simpl. admit. } 
    all: apply LBL_STEP; eauto with label_ext.
    all: eapply nonnop_bounded; eauto with label_ext; vauto.
  Admitted. 

  (* Lemma single_event_helper st1 st2 tid index *)
  (*       (IND: index >= eindex st1) *)
  (*       (ADD: exists new_label foo bar baz bazz, *)
  (*           G st2 = add (G st1) tid index new_label foo bar baz bazz) *)
  (*       n (REACH: (step tid) ^^ n (init (instrs st1)) st1) *)
  (*       (EMPTY1: E (G st1) ≡₁ ∅) *)
  (*       (OMM1: omm_premises_hold (G st1)): *)
  (*   omm_premises_hold (G st2). *)
  (* Proof. *)
  (*   desc.  *)
  (*   assert (E (G st2) ≡₁ eq (ThreadEvent tid index)) as E2. *)
  (*   { unfold acts_set in EMPTY1. *)
  (*     destruct (acts (G st1)) eqn:acts1.  *)
  (*     2: { exfalso. generalize EMPTY1. basic_solver. } *)
  (*     rewrite ADD. unfold add, acts_set. rewrite acts1. simpl. *)
  (*     basic_solver. } *)
  (*   red. splits. *)
  (*   2: { red. splits; [| basic_solver].  *)
  (*        arewrite (rmw (G st2) ≡ rmw (G st1)) by (rewrite ADD; vauto). *)
  (*        suffices: Sc (G st2) ≡₁ Sc (G st1) *)
         
    
  Lemma GI_1thread_omm_premises_block bst tid PO BPI
        (COMP: is_thread_block_compiled PO BPI) 
        (BLOCK_STEPS: (omm_block_step tid)＊ (binit BPI) bst):
    omm_premises_hold (bG bst).
  Proof.
    apply crt_num_steps in BLOCK_STEPS. destruct BLOCK_STEPS as [n_steps BLOCK_STEPS].
    generalize dependent bst. induction n_steps.
    { ins. red in BLOCK_STEPS. desc. subst. simpl.
      red. simpl. splits; basic_solver. }
    ins. red in BLOCK_STEPS. destruct BLOCK_STEPS as [bst_prev [STEPS_PREV STEP_NEXT]].
    specialize (IHn_steps bst_prev STEPS_PREV). 
    red in STEP_NEXT. desc.
    assert (PO0 = PO) by admit. subst PO0. 
    red in BLOCK_STEP. desc.
    assert (binstrs bst_prev = BPI) as BINSTRS by admit. 
    remember (bpc bst_prev) as b. remember (bst2st bst_prev) as st_prev.
    rewrite BINSTRS in *.
    assert (exists oinstr, is_instruction_compiled oinstr block) as [oinstr COMP_BLOCK].
    { eapply resulting_block_compiled; eauto. eapply COMPILED_NONEMPTY. eauto. }
    assert (forall i block_i, Some block_i = nth_error block i -> Some block_i = nth_error (instrs st_prev) (pc st_prev + i)) as BLOCK_CONTENTS. 
    { ins. forward eapply (@near_pc block_i block i H bst_prev); eauto.
      { congruence. }
      apply nth_error_Some, OPT_VAL. exists block. congruence. }
    assert (forall i instr (BLOCK_I: Some instr = nth_error block i) instr' (OTHER: Some instr' = nth_error (instrs st_prev) (pc st_prev + i)) (NEQ: instr <> instr'), False).
    { admit. }
    assert (exists k, (step tid) ^^ k (init (instrs st_prev)) st_prev) as [k REACH] by admit.
    inv COMP_BLOCK; simpl in *.
    { remember (bst2st bst_prev) as st_prev.
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP0.
      do 2 (red in BLOCK_STEP0; desc).
      forward eapply (BLOCK_CONTENTS 0 ld) as INSTR; eauto.
      inversion ISTEP0.
      all: try (forward eapply (@H 0 ld eq_refl instr); vauto; rewrite Nat.add_0_r; vauto).
      assert (instr = ld). 
      { cut (Some instr = Some ld); [ins; vauto| ].
        rewrite ISTEP, INSTR. rewrite Nat.add_0_r.
        vauto. }
      subst instr. inversion H0. subst ord. subst reg. subst lexpr. 
      remember (Aload false Orlx (RegFile.eval_lexpr (regf st_prev) loc) val) as lbl. 
      remember (bst2st bst) as st.
      replace (init (flatten (binstrs bst_prev))) with (init (instrs st_prev)) in * by vauto. 
      red.
      replace (bG bst) with (G st) by vauto.
      forward eapply step_label_ext_helper as LBL_EXT; eauto. 
      simpl in LBL_EXT. desc. 
      (* forward eapply (@label_set_step (@is_rlx actid) orlx_matcher st_prev st tid lbl (eindex st_prev) _ _ orlx_pl (@nonnop_bounded _ (@is_rlx actid) orlx_matcher _ _ orlx_pl (eq_refl false) REACH)) as ORLX_EXT; eauto. *)
      assert (forall max_event index (IND: index >= eindex st_prev),
                 singl_rel max_event (ThreadEvent tid (eindex st_prev)) ⨾ rmw (G st_prev) ≡ ∅₂) as SB_RMW_HELPER. 
      { split; [| basic_solver].
        rewrite rmw_bibounded; vauto. 
        red. ins. red in H1. desc. red in H1. desc. subst.
        simpl in H2. omega. }
      subst lbl. simpl in *.
      des.
      {
        (* splits.  *)
        (* 2: { rewrite RMW_EXT, SC_EXT. remove_emptiness.  *)
        (*      red in IHn_steps. desc. vauto. } *)
        (* all: unfold Execution.sb; rewrite E_EXT; rewrite SB_EXT; remove_emptiness.  *)
        admit. }
      splits.
      { rewrite E_EXT, W_EXT, SC_EXT, F_EXT, ACQ_EXT, RMW_EXT, SB_EXT. 
        rewrite seq_union_l.
        remove_emptiness. 
        rewrite set_inter_union_l.
        arewrite (eq (ThreadEvent tid (eindex st_prev)) ∩₁ W (G st_prev) ≡₁ ∅).
        { rewrite set_interC. 
          forward eapply (@label_set_bound_inter st_prev tid _ _ _ (@is_w actid) w_matcher w_pl); eauto.
          vauto. }
        rewrite SB_RMW_HELPER; eauto. remove_emptiness. 
        red in IHn_steps. desc. vauto. }
      { rewrite RMW_EXT, SC_EXT. remove_emptiness. 
        red in IHn_steps. desc. vauto. }
      { rewrite E_EXT. admit. }
      { rewrite E_EXT, R_EXT, SC_EXT, F_EXT, ACQ_EXT, SB_EXT_WRONG.
        remove_emptiness. 
        rewrite seq_union_r, codom_union.
        apply set_subset_union_r. left.
        rewrite set_interA. 
        rewrite set_inter_union_l.
        arewrite (eq (ThreadEvent tid (eindex st_prev))
                     ∩₁ ((R (G st_prev) ∪₁ eq (ThreadEvent tid (eindex st_prev)))
                           ∩₁ Sc (G st_prev)) ≡₁
                     (R (G st_prev) ∪₁ eq (ThreadEvent tid (eindex st_prev))) ∩₁
                     (eq (ThreadEvent tid (eindex st_prev)) ∩₁ Sc (G st_prev))) by basic_solver. 
        rewrite set_inter_union_l.
        arewrite (eq (ThreadEvent tid (eindex st_prev)) ∩₁ Sc (G st_prev) ≡₁ ∅).
        { rewrite set_interC.
          forward eapply (@label_set_bound_inter st_prev tid _ _ _ (@is_sc actid) sc_matcher sc_pl); eauto.
          vauto. }
        remove_emptiness. rewrite <- set_interA. 
        red in IHn_steps. desc. vauto. } }
    
                     
        rewrite <- set_interA with (s := eq (ThreadEvent tid (eindex st_prev))). 
        (* assert (exists oinstr, Some oinstr = nth_error PO b) as [oinstr OINSTR].  *)
    (* { apply OPT_VAL. apply nth_error_Some. *)
    (*   replace (length PO) with (length BPI). *)
    (*   { apply nth_error_Some, OPT_VAL. eauto. } *)
    (*   symmetry. apply compilation_same_length. red. eauto. }     *)
    (* red in BLOCK_STEP. desc. rename BLOCK_STEP0 into BLOCK_STEP. *)
    (* assert (exists block0, Some block0 = nth_error BPI0 (bpc bsti)) as [block0 BLOCK0]. *)
    (* { apply OPT_VAL. apply nth_error_Some. *)
    (*   replace (length BPI0) with (length (binstrs bsti)). *)
    (*   { apply nth_error_Some, OPT_VAL. eauto. } *)
    (*   symmetry. eapply Forall2_length. eauto. } *)
    (* assert (is_instruction_compiled oinstr block0) as COMP_BLOCK. *)
    (* { eapply Forall2_index; eauto. }  *)
    (* assert (block_corrected BPI0 block0 block) as CORR_BLOCK. *)
    (* { eapply Forall2_index; eauto. }  *)
        
    red. splits.
    
    foobar. 
  Admitted. 

  Lemma GI_1thread_omm_premises tid PO PI (COMP: is_thread_compiled PO PI) Gi
        (EXEC: thread_execution tid PI Gi):
    omm_premises_hold Gi.
  Proof.
    red in EXEC. destruct EXEC as [st_fin [STEPS [TERM GRAPH]]]. 
    red in COMP. desc. red in COMP. desc.
    set (bst_fin := bst_from_st st_fin BPI (length BPI)).
    assert (st_fin = bst2st bst_fin) as BST.
    { replace PI with (instrs st_fin) in *.
      2: { apply eq_trans with (y := instrs (init PI)); auto.
           symmetry. apply steps_same_instrs. eauto. }
      unfold bst2st. simpl. rewrite firstn_all.
      red in TERM. apply is_terminal_pc_bounded in TERM. 
      rewrite <- COMP0 in *.
      rewrite <- TERM. apply state_record_equality. }
    forward eapply (@steps_imply_ommblocks bst_fin) as BLOCK_STEPS; eauto.
    { simpl. rewrite <- COMP0, <- BST. eauto. }
    replace Gi with (bG bst_fin).
    eapply GI_1thread_omm_premises_block; eauto. 
  Qed. 

End CompCorrHelpers.

Section CorrectedDefinitions.

  Notation "'E' G" := G.(acts_set) (at level 1).

  Definition program_execution_corrected (prog : Prog.t) G :=
    (forall e : actid, E G e -> is_init e \/ IdentMap.In (tid e) prog) /\
    (forall (thread : IdentMap.key) (PIi : list Instr.t)
       (THREAD: Some PIi = IdentMap.find thread prog)
       Gi (THREAD_EXEC: thread_restricted_execution G thread Gi),
        thread_execution thread PIi Gi).

  Definition Oprogram_execution_corrected prog (OPROG: OCamlProgram prog) G :=
    (forall e (IN: G.(acts_set) e), is_init e \/ IdentMap.In (tid e) prog) /\
    (forall (thread : IdentMap.key) (POi : list Instr.t)
       (THREAD: Some POi = IdentMap.find thread prog)
       Gi (THREAD_EXEC: thread_restricted_execution G thread Gi),
        Othread_execution thread POi Gi).
  
  Lemma program_execution_equiv (prog : Prog.t) G:
    program_execution_corrected prog G <-> program_execution prog G.
  Proof. Admitted. 

  Lemma Oprogram_execution_equiv prog G (OPROG: OCamlProgram prog):
    Oprogram_execution_corrected OPROG G <-> Oprogram_execution OPROG G.
  Proof. Admitted. 

End CorrectedDefinitions.   

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


  Lemma find_iff_in {A: Type} (M: IdentMap.t A) k: 
    IdentMap.In k M <-> exists elt, Some elt = IdentMap.find k M. 
  Proof.
    pose proof (@UsualFMapPositive.UsualPositiveMap.Facts.in_find_iff _ M k).
    pose proof OPT_VAL (IdentMap.find k M).
    eapply iff_stepl.
    - eapply H0. 
    - symmetry. eauto.
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
    

  (* Lemma omm_premises_thread_local TSG (OMM_PREM_THREADS: forall tid Gi (THREAD_Gi: Some Gi = IdentMap.find tid (Gis TSG)), omm_premises_hold Gi): *)
  (*   omm_premises_hold (tsg2g TSG).  *)
  (* Proof. *)
  (*   remember (tsg2g TSG) as G. *)
  (*   (* assert (merge : relation actid -> thread_separated_graph -> relation actid). *) *)
  (*   (* { admit. } *) *)
  (*   (* assert (forall (P: execution -> actid -> Prop), *) *)
  (*   (*            P G ≡₁ fun e => exists tid Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ *) *)
  (*   (*                                   P Gi e) as EV_PROPS_UNION by admit.  *) *)
  (*   (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_w G.(lab) a))). *) *)
  (*   (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_r G.(lab) a))).  *) *)
  (*   (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_sc G.(lab) a))). *) *)
  (*   (* assert (forall (r1 r2: relation actid), codom_rel (r1 ∪ r2) ≡₁ codom_rel r1 ∪₁ codom_rel r2). *) *)
  (*   (* { ins. basic_solver. } *) *)
  (*   assert (E G ≡₁ set_bunion (fun _ => True) (fun tid e => exists Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ E (Gi) e)) as E_BUNION by admit.      *)
  (*   (* red. splits. *) *)
  (*   (* { seq_rewrite H. rewrite H1.  *) *)
  (*   (*   rewrite (EV_PROPS_UNION (fun G a => is_true (is_f G.(lab) a))). *) *)
  (*   (* assert (E G ≡₁ fun e => exists tid Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ *) *)
  (*   (*                                E Gi e) by admit. *) *)
    
    
  (* Admitted.   *)

  Lemma omm_premises_thread_local:
    (forall tid Pi (THREAD: Some Pi = IdentMap.find tid ProgI)
       Gi (THREAD_Gi: thread_restricted_execution GI tid Gi),
        omm_premises_hold Gi) -> omm_premises_hold GI.
  Proof. Admitted. 

  Lemma GI_omm_premises : omm_premises_hold GI.
  Proof.
    apply omm_premises_thread_local.
    ins.
    apply program_execution_equiv in ExecI. red in ExecI.
    (* bug? desf hangs here *)
    destruct ExecI as [EVENTS THREAD_EXEC]. clear ExecI.
    red in Compiled. destruct Compiled as [SAME_KEYS THREADS_COMP]. 
    assert (exists POi, is_thread_compiled POi Pi) as [POi POi_COMP].
    { assert (exists POi, Some POi = IdentMap.find tid ProgO) as [POi POi_THREAD]. 
      { apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. }
      exists POi. eapply THREADS_COMP; eauto. } 
    eapply GI_1thread_omm_premises; eauto.
  Qed. 
    
  (* currently rlx fences are used as default value for label function *)
  (* it forces us to (temporarily?) assert that there are no actual rlx fence nodes in a graph *)
  Lemma only_nontrivial_fences_workaround:
    F GI ≡₁ (fun a => is_true (is_f GI.(lab) a)). 
  Proof. Admitted.

  (* Definition option_default {A: Type} (opt: option A) (default: A) := *)
  (*   match opt with *)
  (*   | Some a => a *)
  (*   | None => default *)
  (*   end.  *)

  Lemma locations_separated_compiled Prog Prog' (COMP: is_compiled Prog Prog')
        (LOC_SEP: locations_separated Prog): locations_separated Prog'.
  Proof. Admitted. 

  Lemma instr_of_event Prog G (EXEC: program_execution Prog G):
    exists (f: actid -> Prog.Instr.t),
      forall e (Ee: E G e) (NINITe: ~ is_init e)
        l (LOC: Some l = loc (lab G) e),
      exists tid Pi, Some Pi = IdentMap.find tid Prog /\
                In (f e) Pi /\ In l (instr_locs (f e))
                /\ Some (Events.mod G.(lab) e) = instr_mode (f e). 
  Proof. Admitted. 

  Lemma GI_locations_separated: 
    let Loc_ := fun l e => loc (lab GI) e = Some l in
    forall l : location,
      E GI ∩₁ Loc_ l \₁ (fun a : actid => is_init a) ⊆₁ ORlx GI \/
      E GI ∩₁ Loc_ l \₁ (fun a : actid => is_init a) ⊆₁ Sc GI.
  Proof.
    pose proof (instr_of_event ExecI) as LOC_MAP. 
    destruct LOC_MAP as [ev2in ev2in_props]. 
    simpl. ins.
    destruct (classic (E GI ∩₁ (fun e : actid => loc (lab GI) e = Some l) \₁
                         (fun a : actid => is_init a) ⊆₁ ORlx GI \/
                       E GI ∩₁ (fun e : actid => loc (lab GI) e = Some l) \₁
                         (fun a : actid => is_init a) ⊆₁ Sc GI)) as [|DECIDE]; auto. 
    exfalso. apply not_or_and in DECIDE. desc.
    assert (forall (r1 r2: actid -> Prop), ~ r1 ⊆₁ r2 -> exists e, r1 e /\ ~ r2 e) as NON_SUBSET. 
    { ins. unfold set_subset in H.
      apply not_all_ex_not in H. desc. exists n. apply imply_to_and. auto. }
    apply NON_SUBSET in DECIDE. apply NON_SUBSET in DECIDE0. clear NON_SUBSET. 
    destruct DECIDE as [e e_props]. destruct DECIDE0 as [e0 e0_props].
    destruct e_props as [[[Ee Le] NINITe] NRLXe]. 
    destruct e0_props as [[[Ee0 Le0] NINITe0] NSC0].
    symmetry in Le, Le0.
    pose proof (ev2in_props e Ee NINITe l Le) as [tid [PI [THREAD_PI [INSTR_PI INSTR_L]]]].
    pose proof (ev2in_props e0 Ee0 NINITe0 l Le0) as [tid0 [PI0 [THREAD_PI0 [INSTR0_PI0 INSTR0_L]]]].
    clear ev2in_props. 
    remember (ev2in e) as instr. remember (ev2in e0) as instr0.
    desc. 
    pose proof (locations_separated_compiled Compiled (proj2 OCamlProgO)) as IMM_LOC_SEP. red in IMM_LOC_SEP. specialize (IMM_LOC_SEP l). 
    destruct IMM_LOC_SEP as [m [OMMm PROPSm]].
    pose proof (PROPSm tid PI (eq_sym THREAD_PI) instr INSTR_PI INSTR_L) as INSTR_m. 
    pose proof (PROPSm tid0 PI0 (eq_sym THREAD_PI0) instr0 INSTR0_PI0 INSTR0_L) as INSTR0_m.
    unfold is_only_rlx in NRLXe. unfold is_sc in NSC0.
    replace (Events.mod (lab GI) e) with m in *; [| congruence]. 
    replace (Events.mod (lab GI) e0) with m in *; [| congruence].
    type_solver. 
  Qed. 

  Lemma imm_implies_omm:
    ocaml_consistent GI.
  Proof.
    pose proof GI_omm_premises as GI_OMM_PREM. red in GI_OMM_PREM. desc.
    pose proof GI_locations_separated. 
    rewrite only_nontrivial_fences_workaround in *. 
    eapply (@OCamlToimm_s.imm_to_ocaml_consistent GI); eauto.
  Qed.

  Lemma IdentMap_explicit {A B: Type} (P: IdentMap.key -> A -> Prop) (orig: IdentMap.t B):
    (exists (imap: IdentMap.t A),
        same_keys imap orig
        /\ forall key value (KEY: Some value = IdentMap.find key imap), P key value)
    <-> forall key (KEY: IdentMap.In key orig), exists value, P key value. 
  Proof. Admitted. 
    
  (* Lemma build_GOi_map TSGI (WFG: Wf (tsg2g TSGI)) (TSG_EXECI : program_execution_tsg ProgI TSGI): *)
  (*   exists GOis, same_keys GOis (Gis TSGI) /\ *)
  (*           forall tid GOi (THREAD_GRAPH: Some GOi = IdentMap.find tid GOis) *)
  (*             GIi (THREAD: Some GIi = IdentMap.find tid (Gis TSGI)) *)
  (*             Po (THREAD_O: Some Po = IdentMap.find tid ProgO), *)
  (*             same_behavior_local GOi GIi /\ *)
  (*             Othread_execution tid Po GOi.  *)
  (* Proof. *)
  (*   set (P := fun tid GOi => *)
  (*               forall GIi (THREAD: Some GIi = IdentMap.find tid (Gis TSGI)) *)
  (*                 Po (THREAD_O: Some Po = IdentMap.find tid ProgO), *)
  (*                 same_behavior_local GOi GIi /\ *)
  (*                 Othread_execution tid Po GOi).  *)
  (*   apply (@IdentMap_explicit execution execution P (Gis TSGI)). *)
  (*   intros tid THREAD. *)
  (*   red in TSG_EXECI. desc. *)
  (*   red in Compiled. destruct Compiled as [SAME_THREADS THREADS_COMPILED]. clear Compiled. *)
  (*   assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI].  *)
  (*   { apply find_iff_in. apply SAME_KEYS. auto. } *)
  (*   assert (exists Po, Some Po = IdentMap.find tid ProgO) as [Po THREAD_PROGO].  *)
  (*   { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. } *)
  (*   apply find_iff_in in THREAD. destruct THREAD as [Gi THREAD_EXEC].  *)
  (*   specialize (THREAD_GRAPH_EXEC tid Pi THREAD_PROGI Gi THREAD_EXEC).  *)
  (*   forward eapply thread_execs; eauto. *)
  (*   (* { pose proof (proj1 (Wf_tsg (tsg2g TSGI))). apply H in WFG. desc. *) *)
  (*   (*   eapply WFG. rewrite (proj2 tsg_g_bijection). eauto. } *) *)
  (*   ins. unfold P. destruct H as [GOi GOi_PROPS]. *)
  (*   exists GOi. ins. *)
  (*   (* TODO: correct this duplication? *) *)
  (*   replace GIi with Gi; [| congruence]. replace Po0 with Po; [| congruence]. *)
  (*   desc. split; auto.  *)
  (* Qed.  *)

  (* Lemma TSGO_exists TSGI (WFG: Wf (tsg2g TSGI)) (TSG_EXECI : program_execution_tsg ProgI TSGI): *)
  (*   exists TSGO, *)
  (*   Oprogram_execution_tsg TSGO OCamlProgO /\ *)
  (*   co_tsg TSGO ≡ co_tsg TSGI /\ *)
  (*   rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘ /\ *)
  (*   (forall tid : IdentMap.key, *)
  (*       IdentMap.In tid (Gis TSGO) -> *)
  (*       forall GOi GIi : execution, *)
  (*         Some GOi = IdentMap.find tid (Gis TSGO) -> *)
  (*         Some GIi = IdentMap.find tid (Gis TSGI) -> same_behavior_local GOi GIi).  *)
  (* Proof. *)
  (*   pose proof (build_GOi_map WFG TSG_EXECI) as [GOis [SAME_TIDS GOis_PROPS]].  *)
  (*   set (TSGO := {| Gis := GOis; *)
  (*                   Einit_tsg := Einit_tsg TSGI; *)
  (*                   rf_tsg := rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘; *)
  (*                   co_tsg := co_tsg TSGI; *)
  (*                   rmw_tsg := ∅₂; |} ). *)
  (*   exists TSGO. *)
  (*   destruct Compiled as [SAME_THREADS THREADS_COMPILED]. clear Compiled. *)
  (*   splits; [| basic_solver | subst TSGO; basic_solver |].  *)
  (*   { red. ins.  *)
  (*     specialize (SAME_THREADS tid). *)
  (*     assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI].  *)
  (*     { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. } *)
  (*     assert (exists GIi, Some GIi = IdentMap.find tid (Gis TSGI)) as [Gi THREAD_EXECI]. *)
  (*     { red in TSG_EXECI. desc. red in SAME_KEYS. specialize (SAME_KEYS tid). *)
  (*       apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. } *)
  (*     assert (exists GOi, Some GOi = IdentMap.find tid (Gis TSGO)) as [GOi THREAD_EXECO]. *)
  (*     { simpl. apply find_iff_in, SAME_TIDS, find_iff_in. eauto. } *)
  (*     forward eapply GOis_PROPS; eauto. *)
  (*     ins. desc. eauto. } *)
  (*   ins. *)
  (*   assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI].  *)
  (*   { red in TSG_EXECI. desc. red in SAME_KEYS. apply find_iff_in. *)
  (*     apply SAME_KEYS. apply find_iff_in. eauto. } *)
  (*   assert (exists Po, Some Po = IdentMap.find tid ProgO) as [Po THREAD_PROGO].  *)
  (*   { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. } *)
  (*   forward eapply GOis_PROPS; eauto. ins. desc. auto.  *)
  (* Qed.  *)
    
  Definition  thread_execs_fun tid PIi (THREADI: Some PIi = IdentMap.find tid ProgI):
    inhabited {GOi | forall POi (COMP: Some POi = IdentMap.find tid ProgO), Othread_execution tid POi GOi}.
    apply exists_to_inhabited_sig. 
    assert (exists Po, Some Po = IdentMap.find tid ProgO). 
    { (* apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. *) admit.  }
    desc.
  Admitted.

  Definition merge (GOis: list execution): execution.
  Admitted.

  (* Lemma sbl_restricted GO (OEXEC: Oprogram_execution_corrected OCamlProgO GO) *)
  (*       (* (BY_THREADS: forall tid GOi GIi *) *)
  (*       (*                (RESTRO: thread_restricted_execution GO tid GOi) *) *)
  (*       (*                (RESTRI: thread_restricted_execution GI tid GIi), *) *)
  (*           (* same_behavior_local GOi GIi): *):  *)
  (*   same_behavior_local GO GI. *)
  (* Proof. *)
  (*   red. splits. *)
  (*   { apply program_execution_equiv in ExecI. red in ExecI. *)
  (*     destruct ExecI as [INIT EXEC]. clear ExecI. *)
  (*     destruct OEXEC as [INIT' EXEC']. *)

  Lemma thread_execs_helper: exists GO,
      ⟪ E_STRUCT: forall e : actid, E GO e -> is_init e \/ IdentMap.In (tid e) ProgO ⟫/\
      ⟪ SAME_INIT: E GO ∩₁ is_init ≡₁ E GI ∩₁ is_init⟫ /\
      ⟪ SAME_CO: co GI ≡ co GO⟫ /\
      ⟪ EXT_RF: rf GO ≡ rf GI ⨾ ⦗set_compl (dom_rel (rmw GI))⦘ ⟫ /\
      ⟪ RESTR_SIM: forall tid POi
        (THREAD: Some POi = IdentMap.find tid ProgO)
        GOi (RESTR: thread_restricted_execution GO tid GOi)
        GIi (RESTR: thread_restricted_execution GI tid GIi),
        Othread_execution tid POi GOi /\ same_behavior_local GOi GIi ⟫.
  Proof.
    eexists. 
  Admitted.

  Lemma restr_graph G tid: exists Gi, thread_restricted_execution G tid Gi.
  Proof.
    set (Gi :=   {| acts := filterP (fun e => Events.tid e = tid) (acts G);
                    lab := lab G;
                    rmw := ⦗Tid_ tid⦘ ⨾ rmw G ⨾ ⦗Tid_ tid⦘;
                    data :=  ⦗Tid_ tid⦘ ⨾ data G ⨾ ⦗Tid_ tid⦘;
                    addr :=  ⦗Tid_ tid⦘ ⨾ addr G ⨾ ⦗Tid_ tid⦘;
                    ctrl :=  ⦗Tid_ tid⦘ ⨾ ctrl G ⨾ ⦗Tid_ tid⦘;
                    rmw_dep :=  ⦗Tid_ tid⦘ ⨾ rmw_dep G ⨾ ⦗Tid_ tid⦘;
                    rf := ∅₂;
                    co := ∅₂;
                 |}). 
    exists Gi.
    split.
    all: subst Gi; try unfold acts_set; simpl; auto. 
    simpl. apply set_equiv_exp_iff. ins.
    red. split.
    - ins. apply in_filterP_iff in H. desc.  red. split; auto.
    - ins. apply in_filterP_iff. red in H. desc. split; vauto.
  Qed. 
      
  Lemma into_restr G e (Ee: E G e):
    is_init e \/
    (exists tid Gi ind,
        ⟪ TRE: thread_restricted_execution G tid Gi ⟫ /\
        ⟪ EGi: E Gi e ⟫ /\
        ⟪ SAME_TID: e = ThreadEvent tid ind ⟫).
  Proof.
    destruct e; auto. right.
    pose proof (restr_graph G thread). desc.
    exists thread. exists Gi. exists index. split; auto.
    destruct H. split; auto. 
    apply (set_equiv_exp tr_acts_set). red. split; auto.
  Qed.

  Lemma tid_restr G Gi e tid (Gie: E Gi e)
        (TRE: thread_restricted_execution G tid Gi): 
    Events.tid e = tid.
  Proof.
    destruct TRE. apply (set_equiv_exp tr_acts_set) in Gie.
    red in Gie. desc. auto.
  Qed. 

  Lemma E_restr_iff G Gi tid e (TRE: thread_restricted_execution G tid Gi)
    (TID: Events.tid e = tid):
    E G e <-> E Gi e.
  Proof. Admitted. 

  Lemma GO_exists: exists GO,
      Oprogram_execution_corrected OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    pose proof thread_execs_helper as T_E_H. desc.
    exists GO. split.
    { red. split; auto. 
      ins. specialize (RESTR_SIM _ _ THREAD Gi THREAD_EXEC).
      pose proof (restr_graph GI thread) as [GIi RESTRI]. 
      desc. specialize (RESTR_SIM GIi RESTRI). desc. auto. }
    red. splits; auto.
    { red. splits. 
      2: { ins. pose proof EGOx as EGOx_. apply into_restr in EGOx. destruct x.
           { admit. }
         destruct EGOx; vauto.
         desc. inversion SAME_TID. subst. rename Gi into GOi. 
         replace (lab GO (ThreadEvent tid ind)) with (lab GOi (ThreadEvent tid ind)).
         2: { destruct TRE. intuition. }
         specialize (E_STRUCT (ThreadEvent tid ind)).
         edestruct E_STRUCT; eauto. 
         - intuition.
         - simpl in H.
           apply find_iff_in in H. destruct H as [POi THREADO]. 
           specialize (RESTR_SIM tid POi THREADO _ TRE).
           pose proof (restr_graph GI tid). desc.
           specialize (RESTR_SIM Gi H). desc.
           replace (lab GI (ThreadEvent tid ind)) with (lab Gi (ThreadEvent tid ind)).
           2: { destruct H. apply tr_lab.
                destruct RESTR_SIM0. red in H.
                apply (set_equiv_exp H) in EGi.
                red in EGi. desc. auto. }
           red in RESTR_SIM0. desc. apply SAME_LAB. auto. }
    apply set_equiv_exp_iff. ins.
    red. split.
    { intros EGOx. red.
      pose proof (into_restr _ _ EGOx). 
      destruct H.
      { split.
        { apply SAME_INIT. split; auto. }
        red. split.
        { cut (W GI x); [basic_solver| ].
          apply (init_w WFI); auto. }
        red. intros RMW. red in RMW. desc. 
        pose proof (proj1 (rmw_from_non_init WFI)).
        apply (hahn_inclusion_exp H0) in RMW. apply seq_eqv_l in RMW. desc. 
        auto. }
      desc. rename Gi into GOi.
      specialize (E_STRUCT x EGOx). destruct E_STRUCT; vauto.
      simpl in H. apply find_iff_in in H. destruct H as [PO THREADO]. 
      assert (exists GIi, thread_restricted_execution GI tid GIi) by apply restr_graph. desc.  
      forward eapply RESTR_SIM as [OTHREADEXEC SAME_BEHL]; eauto.
      split. 
      { eapply E_restr_iff; eauto.
        red in SAME_BEHL. desc. 
        apply (set_equiv_exp RESTR_EVENTS) in EGi.
        red in EGi. desc. auto. }
      red in SAME_BEHL. desc.
      apply (set_equiv_exp RESTR_EVENTS) in EGi.
      desc. red in EGi. desc. red in EGi0. desc. auto.       
      red. split.
      { replace (RW GI (ThreadEvent tid ind)) with (RW GIi (ThreadEvent tid ind)); auto.
        destruct H. unfold is_r, is_w, set_union. 
        rewrite tr_lab; auto. }
      cut (~ dom_rel (rmw GIi) (ThreadEvent tid ind)); vauto. 
      red. ins. red in H0. 
      forward eapply H0; auto.  
      unfold dom_rel. unfold dom_rel in H1. desc. exists y.
      destruct H. apply (same_relation_exp tr_rmw).
      apply seq_eqv_lr. splits; auto.
      apply (hahn_inclusion_exp (rmw_in_sb WFI)) in H1.
      apply sb_tid_init in H1. simpl in H1. destruct H1; vauto. }
    ins. red in H. desc.
    destruct x.
    { apply SAME_INIT. split; auto. }
    pose proof (restr_graph GO thread) as [GOi TRE]. 
    eapply E_restr_iff; eauto.     
    { assert (exists PIi, Some PIi = IdentMap.find thread ProgI) by admit.
      assert (exists POi, Some POi = IdentMap.find thread ProgO) as [POi THREADO]. 
      { apply find_iff_in. red in Compiled. destruct Compiled.
        apply H2. apply find_iff_in. auto. }
      assert (exists GIi, thread_restricted_execution GI thread GIi) as [GIi TREI] by apply restr_graph.      
      forward eapply RESTR_SIM as [OEXEC SAME_BEHL]; eauto.
      destruct SAME_BEHL. apply (set_equiv_exp H2).
      pose proof TREI as TREI_. destruct TREI. 
      assert (E GIi (ThreadEvent thread index)) as EGIi. 
      { apply (@E_restr_iff _ _ _ _ TREI_); auto. }
      red. split; auto.       
      red. red in H0. desc. split. 
      { replace (RW GIi (ThreadEvent thread index)) with (RW GI (ThreadEvent thread index)); auto.
        unfold is_r, is_w, set_union. 
        rewrite tr_lab; auto. }
      cut (~ dom_rel (rmw GI) (ThreadEvent thread index)); vauto. 
      red. ins. red in H5.  
      apply H5. 
      unfold dom_rel. unfold dom_rel in H6. desc. exists y.
      apply (same_relation_exp tr_rmw) in H6. apply seq_eqv_lr in H6. desc. auto. } }
    
  Admitted. 

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI)
        (ExecO: Oprogram_execution OCamlProgO GO):
    ocaml_consistent GO.
  Proof.
    (* pose proof (same_beh_implies_similar_rels SB). *)
    pose proof (same_beh_implies_similar_intrarels SB) as SIMILAR_INTRA. 
    pose proof (Wf_subgraph SB WFI) as WFO. 
    red in SB. desc. red in SAME_LOCAL. desc.
    assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘).
    { (* TODO: extract and remove duplicate *)
      unfold Execution.sb.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC.
      rewrite RESTR_EVENTS.
      basic_solver. }
    
    assert (HBO': hbo GO ⊆ hbo GI).
    { unfold OCaml.hb.
      apply clos_trans_mori.
      apply union_mori; [rewrite SB'; basic_solver | ].
      destruct WFO. rewrite wf_coE, wf_rfE at 1.
      repeat rewrite <- restr_relE.
      rewrite union_restr, restr_restr.
      arewrite (E GO ∩₁ Sc GO ≡₁ E GO ∩₁ Sc GI).
      { (* TODO: generalize with ..._SIM *)
        apply set_equiv_exp_iff.
        ins. split.
        { ins. red in H. desc. red. split; auto.
          unfold is_sc, Events.mod. rewrite <- (SAME_LAB); auto. }
        { ins. red in H. desc. red. split; auto.
          unfold is_sc, Events.mod. rewrite (SAME_LAB); auto. } }
      apply restr_rel_mori; [basic_solver| ].
      rewrite SAME_CO, RESTR_RF. basic_solver. }
    red. red in OMM_I.
    splits; auto.
    { red.
      rewrite R_SIM.
      2: { red. splits; eauto. }
      rewrite RESTR_EVENTS, RESTR_RF. fold (RWO GI). 
      desc. red in Comp.
      rewrite restr_relE, <- seqA.
      rewrite set_interC, <- set_interA. rewrite set_interC with (s := R GI).
      arewrite (E GI ∩₁ R GI ⊆₁ codom_rel (rf GI)).
      rewrite <- seqA. rewrite codom_eqv1.
      apply set_subset_inter; [| basic_solver].      
      red. ins. red in H. destruct H as [w RFwx]. red. exists w.
      apply seq_eqv_l. split; auto. red. red.
      cut (W GI w).
      { ins. split; [basic_solver| ].
        pose proof wf_rmwD WFI.
        pose proof (same_relation_exp_iff (rmw GI) (⦗R_ex GI⦘ ⨾ rmw GI ⨾ ⦗W GI⦘)) as [IMPL _].
        red. ins. red in H1. desc. 
        specialize (IMPL H0 w y). destruct IMPL as [IMPL _]. specialize (IMPL H1).
        apply seq_eqv_lr in IMPL. desc. type_solver. }
      pose proof (wf_rfD WFI).
      pose proof (same_relation_exp_iff (rf GI) (⦗W GI⦘ ⨾ rf GI ⨾ ⦗R GI⦘)) as [IMPL _].
      specialize (IMPL H w x). destruct IMPL. specialize (H0 RFwx).
      apply seq_eqv_lr in H0. desc. auto. }
    { red. arewrite (rmw GO ≡ ∅₂); basic_solver. }
    { rewrite HBO', SAME_CO. desc.  auto. }
    { unfold fr. rewrite HBO', SAME_CO. 
      arewrite (rf GO ⊆ rf GI) by rewrite RESTR_RF; auto. 
      auto. desc. auto. }    
    assert (W_RMW: W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
    { rewrite set_minusE.
      apply set_subset_inter_r. split; [basic_solver| ].
      rewrite (WFI.(wf_rmwD)).
      rewrite dom_eqv1. rewrite set_compl_inter.
      unionR left. type_solver. }
    arewrite (rfe GO ⊆ rfe GI).
    { unfold rfe. rewrite SB', RESTR_RF.
      fold (RWO GI). rewrite <- restr_relE.
      rewrite <- restr_minus. basic_solver. }
    assert (FR' : fr GO ≡ restr_rel (RWO GI) (fr GI)).
    { unfold Execution.fr. rewrite RESTR_RF.
      repeat rewrite restr_relE. do 2 rewrite transp_seq.
      rewrite transp_eqv_rel. 
      rewrite SAME_CO.
      rewrite !seqA. do 2 (apply seq_more; [basic_solver| ]).
      rewrite (wf_coD WFI), !seqA.
      rewrite seq_eqvC.
      rewrite <- seqA. 
      arewrite (⦗RWO GI⦘ ⨾ ⦗W GI⦘ ≡ ⦗W GI⦘); [| basic_solver]. 
      rewrite <- id_inter. apply eqv_rel_more.
      split; [basic_solver| ].
      apply set_subset_inter_r. split; [| basic_solver].
      auto. }
    
    rewrite <- restr_relE.
    arewrite (restr_rel Sc GO (coe GO ∪ fre GO) ≡ restr_rel (E GO ∩₁ Sc GO) (coe GO ∪ fre GO)).
    { split; try basic_solver.
      red. ins. red in H. desc.
      assert (E GO x /\ E GO y).
      { red in H. des. 
        { red in H. red in H. desc.
          apply (same_relation_exp (wf_coE WFO)) in H.
          apply seq_eqv_lr in H. desc; auto. }
        red in H. red in H. desc.
        apply (same_relation_exp (wf_frE WFO)) in H.
        apply seq_eqv_lr in H. desc; auto. }
      desc. red. splits; red; splits; auto. }
    seq_rewrite SC_SIM .
    2: { red. splits; eauto. }
    arewrite (E GO ∩₁ Sc GI ⊆₁ Sc GI) by basic_solver. 
        
    arewrite (fre GO ⊆ fre GI).
    { unfold fre. rewrite SB', FR'. fold (RWO GI).
      apply inclusion_minus_l.
      rewrite fri_union_fre at 1.
      rewrite <- union_restr.
      apply union_mori.
      { rewrite <- restr_relE.
        apply restr_rel_mori; [basic_solver| ].
        arewrite (fri GI ⊆ sb GI). basic_solver. }
      apply inclusion_restr. }
    
    arewrite (coe GO ≡ coe GI).
    { unfold coe.      
      rewrite SB', SAME_CO. fold (RWO GI). 
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
    
    arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
    rewrite restr_relE. 
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
    apply Oprogram_execution_equiv in OMM_EXEC. 
    splits; auto.    
    apply graph_switch; auto.
    apply (imm_implies_omm). 
  Qed.  

End CompilationCorrectness.       