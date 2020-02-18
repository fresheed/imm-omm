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
Require Import OCamlToimm_s_prog_bounded_properties. 
Require Import ClosuresProperties. 
Require Import Prog.
Require Import ProgToExecution.
Require Import ProgToExecutionProperties.
Require Import Logic.Decidable. 
From PromisingLib Require Import Basic Loc.
Require Import Basics. 
Set Implicit Arguments.

Section SEQ_STEPS.
  
  Definition sublist {A: Type} (l: list A) (start len: nat) := firstn len (skipn start l). 

  (* Definition on_block st block := *)
  (*   ⟪ PROG_BLOCK: block = sublist (instrs st) (pc st) (length block) ⟫ /\ *)
  (*   ⟪ COMP_BLOCK: (exists oinstr, is_instruction_compiled oinstr block) ⟫.  *)

  (* Definition at_compilation_block st := *)
  (*   (exists block, on_block st block) \/ is_terminal st.  *)

  (* Definition oseq_step (tid : thread_id) sti1 sti2 := *)
  (*   exists block, on_block sti1 block /\ *)
  (*            (step tid) ^^ (length block) sti1 sti2.  *)
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


End SEQ_STEPS. 
  


  
Section ThreadSeparatedGraph.
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
    

  Definition same_behavior_local (GO GI: execution) :=
    ⟪ RESTR_EVENTS: E GO ≡₁ E GI ∩₁ (RW GI \₁ dom_rel (GI.(rmw))) ⟫ /\
    ⟪ SAME_LAB: forall x (EGOx: E GO x), lab GO x = lab GI x ⟫. 

  Definition same_behavior (GO GI: execution) :=
    ⟪SAME_LOCAL: same_behavior_local GO GI ⟫ /\
    ⟪SAME_CO: GI.(co) ≡ GO.(co)⟫ /\
    ⟪EXT_RF: GO.(rf) ≡ GI.(rf) ⨾ ⦗set_compl (dom_rel GI.(rmw))⦘⟫.        

  Record thread_separated_graph :=
    {
      Gis: IdentMap.t execution;
      Einit_tsg: actid -> Prop;
      rf_tsg: relation actid;
      co_tsg: relation actid;
      rmw_tsg: relation actid;
    }.

  Definition same_keys {A B: Type} (map1: IdentMap.t A) (map2: IdentMap.t B)
    := forall key, IdentMap.In key map1 <-> IdentMap.In key map2. 
  
  Definition program_execution_tsg P tsg :=
    ⟪ SAME_KEYS: same_keys P (Gis tsg) ⟫ /\
    ⟪ THREAD_GRAPH_EXEC: forall tid Pi (THREAD_PROG: Some Pi = IdentMap.find tid P)
    Gi (THREAD_GRAPH: Some Gi = IdentMap.find tid tsg.(Gis)),
      thread_execution tid Pi Gi ⟫. 

  Definition Oprogram_execution_tsg P tsg (OCAML_P: OCamlProgram P) :=
    forall tid Po (THREAD_PROG: Some Po = IdentMap.find tid P),
    exists Go, Some Go = IdentMap.find tid tsg.(Gis) /\
          Othread_execution tid Po Go.
  
  Definition same_behavior_tsg TSGO TSGI :=
    (forall tid (THREAD: IdentMap.In tid (Gis TSGO))
       GOi GIi
       (THREAD_GRAPHO: Some GOi = IdentMap.find tid (Gis TSGO))
       (THREAD_GRAPHI: Some GIi = IdentMap.find tid (Gis TSGI)),
        same_behavior_local GOi GIi)
    (* /\ Einit_tsg TSGO ≡₁ Einit_tsg TSGI *)
    /\ co_tsg TSGO ≡ co_tsg TSGI
    /\ rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘. 

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
 
  Definition g2tsg: execution -> thread_separated_graph. Admitted. 
  Definition tsg2g: thread_separated_graph -> execution. Admitted. 

  Lemma program_execution_defs_equiv P G:
    program_execution P G <-> program_execution_tsg P (g2tsg G).
  Proof. Admitted. 

  Lemma Oprogram_execution_defs_equiv P G (OCAML_P: OCamlProgram P):
    Oprogram_execution OCAML_P G <-> Oprogram_execution_tsg (g2tsg G) OCAML_P. 
  Proof. Admitted.

  Lemma same_behavior_defs_equiv GO GI:
    same_behavior GO GI <-> same_behavior_tsg (g2tsg GO) (g2tsg GI).
  Proof. Admitted. 
    
  Lemma tsg_g_bijection:
    (forall G, tsg2g (g2tsg G) = G) /\
    (forall TSG, g2tsg (tsg2g TSG) = TSG).
  Proof. Admitted. 

  (* tids should be equal *)
  (* tsg should include a fact that Gis are 1thread *)
  Lemma tsg_todo: True. Proof. Admitted.
  
End ThreadSeparatedGraph.


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

  Lemma Wf_tsg G:
    Wf G <-> (forall tid Gi (THREAD_GRAPH: Some Gi = IdentMap.find tid (Gis (g2tsg G))),
               Wf_local Gi)
           /\ Wf_global G. 
  Proof. Admitted.
  
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
  
  
  (* TODO: update Coq version? *)
  (* this lemma is mentioned on https://coq.inria.fr/library/Coq.Lists.List.html *)
  Lemma skipn_all2 {A: Type} (l: list A) n: length l <= n -> skipn n l = [].
  Proof. Admitted. 

  Lemma flatten_split {A: Type} (ll: list (list A)) bi (INDEX: bi < length ll):
    flatten ll = flatten (firstn bi ll) ++ flatten (skipn bi ll).
  Proof. ins. rewrite <- flatten_app. rewrite firstn_skipn. auto. Qed. 
    
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

  Lemma OPT_VAL: forall {A: Type} (opt: option A), opt <> None <-> exists o, Some o = opt.
  Proof. 
    ins. destruct opt; [vauto | ]. 
    split; [ins| ]. 
    intros [o CONTRA]. vauto.
  Qed.  

  
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

  Lemma inclusion_minus {A: Type} (s u m: A -> Prop):
    s ⊆₁ u \₁ m <-> s ⊆₁ u /\ s ∩₁ m ⊆₁ ∅.
  Proof.
    (*link to similar lemma here*)
  Admitted. 

  Lemma bs_extract bst bst' tid (OSEQ_STEP: omm_block_step tid bst bst'):
    block_step tid bst bst'.
  Proof. do 2 (red in OSEQ_STEP; desc). vauto. Qed.

  Lemma same_relation_exp_iff {A: Type} (r r': relation A):
    r ≡ r' <-> (forall x y, r x y <-> r' x y).
  Proof.
    red. split.
    { apply same_relation_exp. }
    ins. red. split.
    all: red; ins; apply H; auto.
  Qed.  
   
  Lemma blockstep_implies_steps bst1 bst2 tid
        (BLOCK_STEPS: (block_step tid)＊ bst1 bst2): 
    (step tid)＊ (bst2st bst1) (bst2st bst2). 
  Proof.
    apply crt_num_steps. apply crt_num_steps in BLOCK_STEPS. desc.
    generalize dependent bst1. generalize dependent bst2. induction n.
    { ins. red in BLOCK_STEPS. desc.
      exists 0. apply steps0. congruence. }
    ins. red in BLOCK_STEPS. destruct BLOCK_STEPS as [bst' [BLOCK_STEPS1 BLOCK_STEPS2]].
    specialize (IHn _ _ BLOCK_STEPS1). destruct IHn as [n' STEPS1].
    red in BLOCK_STEPS2. desc. red in BLOCK_STEPS2. desc. 
    exists (n' + length block).
    forward eapply (steps_split (step tid) n' (length block) _ (bst2st bst1) (bst2st bst2)) as SPLIT; auto. 
    apply SPLIT. exists (bst2st bst'). split; auto.
    Unshelve. auto.
  Qed. 

  Lemma pair_step sto bsti (MM_SIM: mm_similar_states sto bsti)
        tid bsti' (OSEQ_STEP: omm_block_step tid bsti bsti')
        (BLOCK_REACH: (block_step tid)＊ (binit (binstrs bsti)) bsti):
    exists sto', Ostep tid sto sto' /\ mm_similar_states sto' bsti'.
  Proof.
    pose proof (block_step_nonterminal (bs_extract OSEQ_STEP)) as BST_NONTERM. 
    pose proof (BPC_CHANGE OSEQ_STEP) as BPC'. 
    red in OSEQ_STEP. destruct OSEQ_STEP as [block [BLOCK_STEP_ COMP_BLOCK]].
    forward eapply (@SAME_BINSTRS bsti bsti' tid) as BINSTRS_SAME.
    { red. eauto. }
    desc.
    red in BLOCK_STEP_. desc.
    inversion COMP_BLOCK.
    all: rename H into OINSTR.
    all: rename H0 into BLOCK_CONTENTS.
    all: subst; simpl in *.
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'. 
      apply (same_relation_exp (seq_id_l (step tid))) in BLOCK_STEP.
      assert (AT_PC: Some ld = nth_error (instrs sti) (pc sti)).
      { replace (instrs sti) with (flatten (binstrs bsti)).
        2: { unfold bst2st in Heqsti. subst. auto. }
        replace (pc sti) with (length (flatten (firstn (bpc bsti) (binstrs bsti)))).
        2: { unfold bst2st in Heqsti. subst. auto. }
        rewrite <- (firstn_skipn (bpc bsti) (binstrs bsti)) in AT_BLOCK. 
        rewrite nth_error_app2 in AT_BLOCK.
        2: { apply firstn_le_length. }
        rewrite firstn_length_le in AT_BLOCK; [| omega]. 
        rewrite Nat.sub_diag in AT_BLOCK.
        rewrite (@flatten_split _ (binstrs bsti) (bpc bsti)); [| auto]. 
        rewrite nth_error_app2; [| omega].
        rewrite Nat.sub_diag.        
        assert (forall {A: Type} l (x: A), Some x = nth_error l 0 -> exists l', l = x :: l'). 
        { ins. destruct l; vauto. }
        apply H in AT_BLOCK. desc.
        rewrite AT_BLOCK. simpl. auto. }
      red in BLOCK_STEP. desc. red in BLOCK_STEP. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto + 1;
                G := add (G sto) tid (eindex sto)
                         (Aload false ord (RegFile.eval_lexpr (regf sti) lexpr) val) ∅
                         (DepsFile.lexpr_deps (depf sti) lexpr) (ectrl sti) ∅;
                         eindex := eindex sto + 1;
                regf := RegFun.add reg val (regf sto);
                depf := RegFun.add reg (eq (ThreadEvent tid (eindex sti))) (depf sto);
                ectrl := ectrl sto |}).
      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      exists sto'. splits.
      { red. exists lbls. red. splits; [subst; simpl; auto| ].
        exists ld. exists 0. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (ld = oinstr); [congruence| ].
          inversion COMP. vauto. }
        pose proof (@Oload tid lbls sto sto' ld 0 Orlx reg lexpr val l) as OMM_STEP.
        assert (ORD_RLX: ord = Orlx). 
        { subst ld. congruence. }
        rewrite ORD_RLX, REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. 
        forward eapply OMM_STEP; eauto.
        { subst sto'. simpl. rewrite ORD_RLX, EINDEX_EQ, Nat.add_0_r. auto. }
        { subst sto'. simpl. rewrite EINDEX_EQ, Nat.add_0_r.  auto. }
        { subst sto'. simpl. rewrite REGF_EQ. auto. }
        subst sto'. simpl. rewrite DEPF_EQ. auto. }
      (* assert (LAB_EQ: lab (G sto) = lab (G sti)). *)
      (* { red in MM_SIM1. desc. vauto. } *)
      red. splits.
      { subst sto'. simpl. rewrite <- BINSTRS_SAME. auto. }
      {  subst sto'. simpl. destruct BPC' as [BPC' | BPC']. 
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { red.
        assert (exists n_steps, (step tid) ^^ n_steps (init (instrs sti)) sti) as [n_steps REACH].
        { apply crt_num_steps. 
          subst sti.
          replace (init (instrs (bst2st bsti))) with (bst2st (binit (binstrs bsti))). 
          { apply blockstep_implies_steps. auto. }
          unfold bst2st, init. simpl. auto. }
        splits.
        { replace (bG bsti') with (G sti') by vauto.
          rewrite (@E_ADD).
          2: { repeat eexists. } 
          rewrite (@E_ADD (G sti) (G sti')).
          2: { repeat eexists. eapply UG. }

          desc. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti sti' tid) as R_EXT; eauto. 
          { apply r_pl. }
          { forward eapply nonnop_bounded; eauto.
            { generalize r_pl. eauto. }
            vauto. } 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti sti' tid) as W_EXT; eauto. 
          { apply w_pl. }
          { forward eapply nonnop_bounded; eauto.
            { generalize w_pl. eauto. }
            vauto. } 
          rewrite R_EXT, W_EXT. simpl in *.
          arewrite (rmw (G sti') ≡ rmw (G sti)).
          { rewrite UG. vauto. }
          rewrite EINDEX_EQ, set_union_empty_r. 
          remember (eq (ThreadEvent tid (eindex sti))) as nev.
          rewrite set_unionA, (set_unionC _ (W (G sti))), <- set_unionA.
          rewrite set_inter_union_l. apply set_equiv_union.
          { rewrite set_inter_minus_r.
            arewrite (E (G sti) ∩₁ (RW (G sti) ∪₁ nev) ≡₁ E (G sti) ∩₁ RW (G sti)).
            { rewrite set_inter_union_r. 
              arewrite (E (G sti) ∩₁ nev ≡₁ ∅); [| basic_solver ].
              split; [| basic_solver].
              rewrite E_bounded; eauto. vauto.
              red. ins. red in H. desc. rewrite <- H0 in H. simpl in H. omega. }
            red in MM_SIM1. desc.
            replace (G sti) with (bG bsti) by vauto.
            rewrite <- set_inter_minus_r. auto. }
          split; [| basic_solver].
          apply set_subset_inter_r. split; [basic_solver| ].
          apply inclusion_minus. split; [basic_solver| ]. 
          subst nev. red. ins. red in H. desc. red. 
          forward eapply rmw_bibounded; eauto.
          ins. red in H1. desc.
          red in H0. desc. specialize (H1 x y).
          pose proof (H1 H0). desc. 
          rewrite <- H in H2. simpl in H2. omega. }
        (* **** *)
        replace (bG bsti') with (G sti'); [| vauto ]. 
        subst sto'. rewrite UG. simpl.
        ins. unfold add, acts_set in EGOx. simpl in EGOx.
        red in MM_SIM. rewrite <- EINDEX_EQ. destruct EGOx.
        + rewrite H. do 2 rewrite upds. auto.
        + assert (x <> ThreadEvent tid (eindex sto)) as NEQ.
          { red. ins. rewrite H0 in H.
            forward eapply E_bounded as BOUND; eauto.
            rewrite  EINDEX_EQ in H0, H.
            assert (E (G sti) x) as EGIx.
            { red in MM_SIM1. desc. red in RESTR_EVENTS. desc.
              red in RESTR_EVENTS. forward eapply (RESTR_EVENTS x); vauto.
              basic_solver. }
            red in BOUND. specialize (BOUND x EGIx).
            rewrite H0 in BOUND. simpl in BOUND. omega. }
          rewrite updo; auto. rewrite updo; auto. 
          red in MM_SIM1. desc. replace (G sti) with (bG bsti); [| vauto ]. 
          apply SAME_LAB. auto. }
      { subst sto'. replace (bregf bsti') with (regf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti') with (depf sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti') with (ectrl sti'); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti') with (eindex sti'); [| vauto ].
        simpl. congruence. }
    - remember (bst2st bsti) as sti. remember (bst2st bsti') as sti'.
      apply (same_relation_exp (seqA _ _ _)) in BLOCK_STEP. 
      rewrite (same_relation_exp (seq_id_l _)) in BLOCK_STEP.
      rename sti' into sti''. rename bsti' into bsti''.
      red in BLOCK_STEP. destruct BLOCK_STEP as [sti' [STEP' STEP'']]. 
      assert (AT_PC: Some f = nth_error (instrs sti) (pc sti)).
      { replace (instrs sti) with (flatten (binstrs bsti)).
        2: { unfold bst2st in Heqsti. subst. auto. }
        replace (pc sti) with (length (flatten (firstn (bpc bsti) (binstrs bsti)))).
        2: { unfold bst2st in Heqsti. subst. auto. }
        rewrite <- (firstn_skipn (bpc bsti) (binstrs bsti)) in AT_BLOCK. 
        rewrite nth_error_app2 in AT_BLOCK.
        2: { apply firstn_le_length. }
        rewrite firstn_length_le in AT_BLOCK; [| omega]. 
        rewrite Nat.sub_diag in AT_BLOCK.
        rewrite (@flatten_split _ (binstrs bsti) (bpc bsti)); [| auto]. 
        rewrite nth_error_app2; [| omega].
        rewrite Nat.sub_diag.        
        assert (forall {A: Type} l (x: A), Some x = nth_error l 0 -> exists l', l = x :: l'). 
        { ins. destruct l; vauto. }
        apply H in AT_BLOCK. desc.
        rewrite AT_BLOCK. simpl. auto. }
      assert (AT_PC': Some st = nth_error (instrs sti) (pc sti + 1)).
      { replace (instrs sti) with (flatten (binstrs bsti)).
        2: { unfold bst2st in Heqsti. subst. auto. }
        replace (pc sti) with (length (flatten (firstn (bpc bsti) (binstrs bsti)))).
        2: { unfold bst2st in Heqsti. subst. auto. }
        rewrite <- (firstn_skipn (bpc bsti) (binstrs bsti)) in AT_BLOCK. 
        rewrite nth_error_app2 in AT_BLOCK.
        2: { apply firstn_le_length. }
        rewrite firstn_length_le in AT_BLOCK; [| omega]. 
        rewrite Nat.sub_diag in AT_BLOCK.
        rewrite (@flatten_split _ (binstrs bsti) (bpc bsti)); [| auto]. 
        rewrite nth_error_app2; [| omega].
        rewrite minus_plus. 
        assert (forall {A: Type} l (x: A), Some x = nth_error l 0 -> exists l', l = x :: l'). 
        { ins. destruct l; vauto. }
        apply H in AT_BLOCK. desc.
        rewrite AT_BLOCK. simpl. auto. }      

      red in STEP'. desc. red in STEP'. desc.
      rewrite <- AT_PC in ISTEP. inversion ISTEP as [EQ]. clear ISTEP. 
      inversion ISTEP0.
      all: rewrite II in EQ.
      all: try discriminate.
      rewrite EQ in *. subst instr. 
      set (sto' :=
             {| instrs := instrs sto;
                pc := pc sto;
                G := G sto;
                eindex := eindex sto;
                regf := regf sto;
                depf := depf sto;
                ectrl := ectrl sto |}).

      red in STEP''. desc. red in STEP''. desc.
      rewrite <- INSTRS, UPC, <- AT_PC' in ISTEP. inversion ISTEP as [EQ']. clear ISTEP. 
      inversion ISTEP1.
      all: rewrite II in EQ'.
      all: try discriminate.
      rewrite EQ' in *. subst instr.
      rename x into xmd. 
      set (sto'' :=
             {| instrs := instrs sto;
                pc := pc sto' + 1;
                (* G := add (G sto') tid (eindex sto') (Astore x ord0 l v) *)
                G := add (G sto') tid (eindex sto' + 1) (Astore xmd ord0 l v)
                         (DepsFile.expr_deps (depf sto') expr)
                         (DepsFile.lexpr_deps (depf sto') lexpr) (ectrl sto') ∅;
                eindex := eindex sto' + 2;
                regf := regf sto';
                depf := depf sto';
                ectrl := ectrl sto' |}).

      red in MM_SIM. desc.
      assert (REGF_EQ: regf sto = regf sti). 
      { rewrite MM_SIM2. vauto. }
      assert (DEPF_EQ: depf sto = depf sti). 
      { rewrite MM_SIM3. vauto. }
      assert (EINDEX_EQ: eindex sto = eindex sti). 
      { rewrite MM_SIM5. vauto. }
      assert (ECTRL_EQ: ectrl sto = ectrl sti). 
      { rewrite MM_SIM4. vauto. }
      
      exists sto''. splits.
      { red. exists lbls0. red. splits; [subst; simpl; auto| ].
        exists st. exists 1. splits.
        { assert (exists oinstr, Some oinstr = nth_error (instrs sto) (pc sto)).
          { apply OPT_VAL. apply nth_error_Some.
            rewrite MM_SIM0.
            replace (length (instrs sto)) with (length (binstrs bsti)); auto. 
            symmetry. apply compilation_same_length. auto. }
          desc. pose proof (every_instruction_compiled MM_SIM (pc sto)).
          forward eapply H0 as COMP; eauto.
          { replace (pc sto) with (bpc bsti). eauto. }
          cut (st = oinstr); [congruence| ].
          inversion COMP. vauto. }
        assert (ORD_RLX: ord0 = Orlx). 
        { subst st. congruence. }
        rewrite ORD_RLX in *. 
        assert (Instr.store Orlx lexpr expr = Instr.store Orlx loc val) by vauto.
        inversion H. subst lexpr. subst expr. clear H. 

        
        (* pose proof (@Ostore tid lbls0 sto sto'' st 2 (gt_Sn_O 1) Orlx loc val l v) as OMM_STEP. *)
        pose proof (@Ostore tid lbls0 sto sto'' st 1 Orlx loc val l v) as OMM_STEP.

        
        (* TODO: ???*)
        (* rewrite ORD_RLX, REGF_EQ, DEPF_EQ, EINDEX_EQ, ECTRL_EQ in *. *)
        (*********)
        forward eapply OMM_STEP; eauto.
        (* TODO: modify equalities above to operate with sti' ? *)
        { rewrite REGF_EQ, <- UREGS. auto. }
        { rewrite REGF_EQ, <- UREGS. auto. }
        { subst sto''. subst sto'. simpl. rewrite ORD_RLX, EINDEX_EQ.
          unfold add at 1. simpl. basic_solver.  }
        subst sto''. subst sto'. simpl. omega. }
      red. splits.
      { subst sto''. simpl. rewrite <- BINSTRS_SAME. auto. }
      { subst sto''. simpl. destruct BPC' as [BPC' | BPC']. 
         - rewrite BPC'. rewrite MM_SIM0. auto.
         - desc. congruence. }
      { red.
        assert (exists n_steps, (step tid) ^^ n_steps (init (instrs sti)) sti) as [n_steps REACH].
        { apply crt_num_steps. 
          subst sti.
          replace (init (instrs (bst2st bsti))) with (bst2st (binit (binstrs bsti))). 
          { apply blockstep_implies_steps. auto. }
          unfold bst2st, init. simpl. auto. }
          assert (exists n_steps', (step tid) ^^ n_steps' (init (instrs sti')) sti') as [n_steps' REACH'].
          { exists (n_steps + 1). rewrite Nat.add_1_r. apply step_prev.
            exists sti. split.
            { rewrite <- INSTRS. auto. }
            red. exists lbls. red. splits; auto.
            eexists. eauto. }        
        splits.
        { replace (bG bsti'') with (G sti'') by vauto.
          rewrite (@E_ADD).
          2: { repeat eexists. } 
          rewrite (@E_ADD (G sti') (G sti'') tid (eindex sti + 1)).
          2: { repeat eexists. rewrite <- UINDEX. eapply UG0. }
          rewrite (@E_ADD (G sti) (G sti') tid (eindex sti)).
          2: { repeat eexists. eapply UG. }
          
          desc. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti sti' tid) as R_EXT; eauto. 
          { apply r_pl. }
          { forward eapply (@nonnop_bounded n_steps); eauto.
            { generalize r_pl. eauto. }
            vauto. } 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti sti' tid) as W_EXT; eauto. 
          { apply w_pl. }
          { forward eapply (@nonnop_bounded n_steps); eauto.
            { generalize w_pl. eauto. }
            vauto. } 
          
          desc. 
          forward eapply (@label_set_step (@is_r actid) r_matcher sti' sti'' tid) as R_EXT'; eauto. 
          { apply r_pl. }
          { forward eapply (@nonnop_bounded n_steps'); eauto.
            { generalize r_pl. eauto. }
            vauto. } 
          forward eapply (@label_set_step (@is_w actid) w_matcher sti' sti'' tid) as W_EXT'; eauto. 
          { apply w_pl. }
          { forward eapply (@nonnop_bounded n_steps'); eauto.
            { generalize w_pl. eauto. }
            vauto. } 

          rewrite W_EXT', R_EXT', R_EXT, W_EXT. simpl in *.
          arewrite (rmw (G sti'') ≡ rmw (G sti)).
          { rewrite UG0, UG. vauto. }
          rewrite EINDEX_EQ, !set_union_empty_r. 
          remember (eq (ThreadEvent tid (eindex sti))) as nev.
          rewrite UINDEX. remember (eq (ThreadEvent tid (eindex sti + 1))) as nev'.
          rewrite <- set_unionA, set_unionA. 
          rewrite set_inter_union_l. apply set_equiv_union.
          { rewrite set_inter_minus_r.
            arewrite (E (G sti) ∩₁ (RW (G sti) ∪₁ nev') ≡₁ E (G sti) ∩₁ RW (G sti)).
            { rewrite set_inter_union_r. 
              arewrite (E (G sti) ∩₁ nev' ≡₁ ∅); [| basic_solver ].
              split; [| basic_solver].
              rewrite E_bounded; eauto. vauto.
              red. ins. red in H. desc. rewrite <- H0 in H. simpl in H. omega. }
            red in MM_SIM1. desc.
            replace (G sti) with (bG bsti) by vauto.
            rewrite <- set_inter_minus_r. auto. }
          split.
          2: { rewrite set_inter_union_l. apply set_subset_union_l.
               split; [| basic_solver].
               rewrite set_inter_minus_r. rewrite set_inter_union_r.
               arewrite (nev ∩₁ nev' ≡₁ ∅).
               { subst. red. split; [| basic_solver].
                 red. ins. red in H. desc. rewrite <- H in H0.
                 inversion H0. omega. }
               arewrite (nev ∩₁ RW (G sti) ≡₁ ∅).
               2: basic_solver.
               red. split; [| basic_solver]. 
               red. ins. red in H. desc. rewrite Heqnev in H.
               red in H0. destruct H0.
               + forward eapply (@nonnop_bounded n_steps (@is_r actid) r_matcher sti tid) as R_BOUNDED; eauto. 
               { apply r_pl. }
               { red. vauto. }
                 do 2 red in R_BOUNDED. specialize (R_BOUNDED x H0).
                 rewrite <- H in R_BOUNDED. simpl in R_BOUNDED. omega.
               + forward eapply (@nonnop_bounded n_steps (@is_w actid) w_matcher sti tid) as W_BOUNDED; eauto. 
               { apply w_pl. }
               { red. vauto. }
                 do 2 red in W_BOUNDED. specialize (W_BOUNDED x H0).
                 rewrite <- H in W_BOUNDED. simpl in W_BOUNDED. omega. }
               
          apply set_subset_inter_r. split; [basic_solver| ].
          apply inclusion_minus. split; [basic_solver| ]. 
          subst nev. red. ins. red in H. desc. red. 
          forward eapply rmw_bibounded; eauto.
          ins. red in H1. desc.
          red in H0. desc. specialize (H1 x y).

          assert (rmw (G sti') x y) as RMW'xy. 
          { assert (rmw (G sti') ≡ rmw (G sti)). 
            { rewrite UG. vauto. }
            apply (same_relation_exp H2). auto. }
          
          pose proof (H1 RMW'xy). desc. 
          rewrite Heqnev' in H. rewrite <- H in H2. simpl in H2. omega. }
        replace (bG bsti'') with (G sti''); [| vauto ]. 
        subst sto''. rewrite UG0, UG. simpl.
        ins. unfold add, acts_set in EGOx. simpl in EGOx.
        rewrite UINDEX, <- EINDEX_EQ.
        destruct EGOx.
        + rewrite H. do 2 rewrite upds. auto.
        + assert (index x < eindex sto) as NEQ.
          { destruct (Const.lt_decidable (index x) (eindex sto)); auto.
            exfalso. 
            forward eapply (@E_bounded n_steps tid sti) as BOUND; eauto.
            assert (E (G sti) x) as EGIx.
            { red in MM_SIM1. desc. red in RESTR_EVENTS. desc.
              red in RESTR_EVENTS. forward eapply (RESTR_EVENTS x); vauto.
              basic_solver. }
            red in BOUND. specialize (BOUND x EGIx).
            omega. }
          rewrite updo. rewrite updo. rewrite updo.
          2, 3, 4: red; ins; rewrite H0 in NEQ; simpl in NEQ; omega.
          red in MM_SIM1. desc. replace (G sti) with (bG bsti); [| vauto ]. 
          apply SAME_LAB. auto. }
      { subst sto'. replace (bregf bsti'') with (regf sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bdepf bsti'') with (depf sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (bectrl bsti'') with (ectrl sti''); [| vauto ].
        simpl. congruence. }
      { subst sto'. replace (beindex bsti'') with (eindex sti''); [| vauto ].
        simpl. rewrite UINDEX0, UINDEX. omega. }
      (* - .....*)
      (* - .....*)
      (* - .....*)
  Admitted.
  
  Lemma init_mm_same: forall PO BPI (COMP: is_thread_block_compiled PO BPI),
      mm_similar_states (init PO) (binit BPI).
  Proof.
    ins. red. simpl. splits; auto.
    unfold init_execution. red. simpl. basic_solver. 
  Qed.
      
  Lemma Wfl_subgraph SG' SG (SB: same_behavior_local SG SG') (WFL: Wf_local SG'): Wf_local SG.
  Proof.  Admitted.
      

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


  Lemma lt_ind: forall (P: nat -> Prop), P 0 -> (forall n, (forall y, y < n -> P y) -> P n) -> (forall n, P n).
  Proof. 
    intros.
    assert (forall y : nat, y < n -> P y).
    { induction n; [intros; omega| ]. 
      intros. pose proof (H0 n IHn) as Pn.
      apply H0. intros.
      assert (y0 < n) by omega.
      apply IHn. auto. }
    apply H0. auto.
  Qed.

  Lemma oseq_same_instrs bst bst' (STEPS: exists tid, (block_step tid)＊ bst bst'):
    binstrs bst = binstrs bst'.
  Proof.
    desc. 
  (*   apply steps_same_instrs. desc. exists tid. *)
  (*   apply oseq_implies_steps. auto. *)
    (* Qed.  *)
  Admitted.

  Definition on_block st block :=
    ⟪ PROG_BLOCK: block = sublist (instrs st) (pc st) (length block) ⟫ /\
    ⟪ COMP_BLOCK: (exists oinstr, is_instruction_compiled oinstr block) ⟫.
  
  Definition at_compilation_block st :=
    (exists block, on_block st block) \/ is_terminal st.

  (* Lemma block_steps_selection st1 st2 tid n (STEPS: (step tid) ^^ n st1 st2) *)
  (*       block (BLOCK: on_block st1 block) (ENOUGH: n >= length block): *)
  (*   exists bst1 bst2 st', (block_step tid) bst1 bst2 /\ *)
  (*                    st1 = bst2st bst1 /\ *)
  (*                    st' = bst2st bst2 /\ *)
  (*                    (step tid) ^^ (n - length block) st' st2. *)
  (* Proof. *)
  (*   eapply steps_split in STEPS as [st' [STEPS_TO STEPS_FROM]]. *)
  (*   2: { forward eapply (le_plus_minus (length block) n) as SPLIT; [omega| ]. *)
  (*        eauto. } *)
  (*   exists st'. split; auto. *)
  (*   red. eexists. split; eauto. *)
  (* Qed. *)
  Definition oseq_step (tid : thread_id) sti1 sti2 :=
    exists block, on_block sti1 block /\
             (step tid) ^^ (length block) sti1 sti2. 

  Lemma block_steps_selection st1 st2 tid n (STEPS: (step tid) ^^ n st1 st2)
        block (BLOCK: on_block st1 block) (ENOUGH: n >= length block):
    exists st', (oseq_step tid) st1 st' /\ (step tid) ^^ (n - length block) st' st2.
  Proof.
    eapply steps_split in STEPS as [st' [STEPS_TO STEPS_FROM]]. 
    2: { forward eapply (le_plus_minus (length block) n) as SPLIT; [omega| ].
         eauto. }
    exists st'. split; auto.
    red. eexists. split; eauto. 
  Qed.
  
  
  Lemma is_terminal_new st: pc st >= length (instrs st) <-> is_terminal st.
  Proof. Admitted.

  (* TODO: finish definition *)
  Definition is_corrector (corr: list nat) (PO PI: list Prog.Instr.t) :=
    length corr = length PO + 1 /\
    True.

  Lemma compilation_correction PO PI:
    is_thread_compiled PO PI <-> exists (corrector: list nat),
      ⟪CORR: is_corrector corrector PO PI  ⟫.
  Proof. Admitted.

  Lemma acb_iff_corr PO PI corr (CORR: is_corrector corr PO PI):
    forall st (INSTRS: instrs st = PI),
      (exists block, on_block st block) \/ pc st = length PI
      <-> (exists i, Some (pc st) = nth_error corr i).
  Proof. Admitted.

  Lemma next_corr PO PI corr (CORR: is_corrector corr PO PI):
      forall st (INSTRS: instrs st = PI) block (BLOCK: on_block st block),
      exists i, Some (pc st + length block) = nth_error corr i.
  Proof. Admitted.
        
  Lemma ifgoto_corr PO PI corr (CORR: is_corrector corr PO PI):
      forall cond adr (IN_PROG: In (Instr.ifgoto cond adr) PI),
      In adr corr.
  Proof. Admitted.
        
  Lemma oseq_continuos st1 st2 tid (OSEQ: (oseq_step tid) st1 st2)
        (COMP: exists PO, is_thread_compiled PO (instrs st1)):
    at_compilation_block st2.
  Proof.
    red in OSEQ. desc.
    remember (instrs st1) as PI.
    pose proof COMP as COMP_.
    apply (compilation_correction PO PI) in COMP_. desc.
    pose proof (acb_iff_corr CORR) as IN_CORR'.
    assert (exists i : nat, Some (pc st1) = nth_error corrector i).
    { apply IN_CORR'; eauto. }
    destruct H as [i1 PC1].
    forward eapply (next_corr CORR) as [i1' PC1']; eauto.
    assert (PC2: pc st2 = pc st1 + length block
            \/ exists cond adr, block = [Instr.ifgoto cond adr]).
    { admit. }
    assert (SAME_INSTRS: instrs st1 = instrs st2).
    { apply steps_same_instrs. exists tid. apply crt_num_steps. eauto. }
    assert (BLOCK_STEP: pc st2 = pc st1 + length block -> at_compilation_block st2).
    { intros PC2_BLOCK. rewrite <- PC2_BLOCK in PC1'.
      forward eapply (IN_CORR' st2) as [_ IN_CORR2]; [congruence | ].
      forward eapply (IN_CORR2) as IN_CORR2'; eauto.
      destruct IN_CORR2'.
      { red. left. eauto. }
      red. right. red. apply is_terminal_new. rewrite PC2_BLOCK, <- SAME_INSTRS, <- HeqPI. omega. }
    des.
    { apply BLOCK_STEP. auto. }
    subst. simpl in *.
    apply (same_relation_exp (seq_id_l (step tid))) in OSEQ0.
    do 2 (red in OSEQ0; desc).
    red in OSEQ. desc.
    assert (AT_PC1: Some (Instr.ifgoto cond adr) = nth_error (instrs st1) (pc st1)).
    { apply eq_trans with (y := nth_error [Instr.ifgoto cond adr] 0); auto.
      rewrite <- (NPeano.Nat.add_0_r (pc st1)).
      eapply sublist_items; eauto. }
    rewrite <- AT_PC1 in ISTEP. injection ISTEP as INSTR_IFGOTO.
    inversion ISTEP0; try (rewrite II in INSTR_IFGOTO; discriminate).
    subst. injection II. intros. subst.
    destruct (Const.eq_dec (RegFile.eval_expr (regf st1) expr) 0).
    { apply BLOCK_STEP. auto. }
    forward eapply (ifgoto_corr CORR expr shift) as TO_CORR.
    { eapply nth_error_In. eauto. }
    specialize (IN_CORR' st2 (eq_sym SAME_INSTRS)) as [_ IN_CORR''].
    forward eapply IN_CORR'' as IN_CORR'''.
    { pose proof (In_nth_error corrector shift TO_CORR). desc.
      exists n0. congruence. }
    des.
    { red. eauto. }
    red. right. red. apply is_terminal_new. rewrite IN_CORR''',  <- SAME_INSTRS.
    omega.
  Admitted.

  (* TODO: remove it since exact instruction is known when block_start is called? *)
  Lemma block_start st block instr (BLOCK: on_block st block)
        (AT_PC: Some instr = nth_error (instrs st) (pc st)):
    (exists mode, instr = Prog.Instr.fence mode) \/
    (exists loc expr, instr = Prog.Instr.load Orlx loc expr) \/
    (exists cond loc, instr = Prog.Instr.ifgoto cond loc) \/
    (exists reg expr, instr = Prog.Instr.assign reg expr).
  Proof.
    red in BLOCK. desc.
    inversion COMP_BLOCK.
    all: subst; simpl in *.
    (* TODO: refactor *)
    - assert (AT_PC1: Some ld = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      right. left. subst ld. eauto.
    - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [f; st0] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [f; ld] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some f = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [f; exc] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      left. subst f. eauto.
    - assert (AT_PC1: Some asn = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [asn] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      do 3 right. subst asn. eauto.
    - assert (AT_PC1: Some igt = nth_error (instrs st) (pc st)).
      { apply eq_trans with (y := nth_error [igt] 0); auto.
        rewrite <- (NPeano.Nat.add_0_r (pc st)).
        eapply sublist_items; eauto. }
      rewrite <- AT_PC in AT_PC1. inversion AT_PC1.
      do 2 right. left. subst igt. eauto.
  Qed.

  Lemma block_mid st block instr (BLOCK: on_block st block)
        (BLOCK_LEN: length block >= 2)
        (AT_PC1: Some instr = nth_error (instrs st) (pc st + 1)):
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
    { assert (AT_PC1': Some st0 = nth_error (instrs st) (pc st + 1)).
      { apply eq_trans with (y := nth_error [f; st0] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with st0; [| congruence].
      subst st0. eauto. }
    { assert (AT_PC1': Some ld = nth_error (instrs st) (pc st + 1)).
      { apply eq_trans with (y := nth_error [f; ld] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with ld; [| congruence].
      subst ld. eauto. }
    { assert (AT_PC1': Some exc = nth_error (instrs st) (pc st + 1)).
      { apply eq_trans with (y := nth_error [f; exc] 1); auto.
        eapply sublist_items; eauto. }
      replace instr with exc; [| congruence].
      subst exc. eauto. }
  Qed.
    
  Lemma no_acb_between st1 st2 tid block n (STEPS: (step tid) ^^ n st1 st2)
        (BLOCK: on_block st1 block) (LT: n < length block) (NZ: n <> 0):
    not (at_compilation_block st2).
  Proof.
    assert (SAME_INSTRS: instrs st2 = instrs st1).
    { symmetry. apply steps_same_instrs. eexists. eapply crt_num_steps. eauto. }
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
    { assert (AT_PC1: Some st = nth_error (instrs st1) (pc st1 + 1)).
      { apply eq_trans with (y := nth_error [f; st] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error (instrs st1) (pc st1)).
      { apply eq_trans with (y := nth_error [f; st] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega.
        eapply sublist_items; eauto. }
      assert (NEXT_PC: pc st2 = pc st1 + 1).
      { apply (same_relation_exp (pow_unit (step tid))) in STEPS.
        red in STEPS. desc. red in STEPS. desc.
        inversion ISTEP0; auto.
        rewrite II, <- AT_PC in ISTEP. discriminate. }
      
      red. intros ACB2. red in ACB2.
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite NEXT_PC, SAME_INSTRS in TERM2.
           pose proof (nth_error_None (instrs st1) (pc st1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite NEXT_PC, SAME_INSTRS. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    { assert (AT_PC1: Some ld = nth_error (instrs st1) (pc st1 + 1)).
      { apply eq_trans with (y := nth_error [f; ld] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error (instrs st1) (pc st1)).
      { apply eq_trans with (y := nth_error [f; ld] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega.
        eapply sublist_items; eauto. }
      assert (NEXT_PC: pc st2 = pc st1 + 1).
      { apply (same_relation_exp (pow_unit (step tid))) in STEPS.
        red in STEPS. desc. red in STEPS. desc.
        inversion ISTEP0; auto.
        rewrite II, <- AT_PC in ISTEP. discriminate. }
      
      red. intros ACB2. red in ACB2.
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite NEXT_PC, SAME_INSTRS in TERM2.
           pose proof (nth_error_None (instrs st1) (pc st1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite NEXT_PC, SAME_INSTRS. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    { assert (AT_PC1: Some exc = nth_error (instrs st1) (pc st1 + 1)).
      { apply eq_trans with (y := nth_error [f; exc] 1); auto.
        eapply sublist_items; eauto. }
      assert (AT_PC: Some f = nth_error (instrs st1) (pc st1)).
      { apply eq_trans with (y := nth_error [f; exc] 0); auto.
        replace (pc st1) with (pc st1 + 0) by omega.
        eapply sublist_items; eauto. }
      assert (NEXT_PC: pc st2 = pc st1 + 1).
      { apply (same_relation_exp (pow_unit (step tid))) in STEPS.
        red in STEPS. desc. red in STEPS. desc.
        inversion ISTEP0; auto.
        rewrite II, <- AT_PC in ISTEP. discriminate. }
      
      red. intros ACB2. red in ACB2.
      destruct ACB2 as [[block2 BLOCK2]| TERM2].
      2: { red in TERM2. rewrite NEXT_PC, SAME_INSTRS in TERM2.
           pose proof (nth_error_None (instrs st1) (pc st1 + 1)) as CONTRA.
           destruct CONTRA. forward eapply H0; try omega.
           intros. rewrite H1 in AT_PC1. discriminate. }
      forward eapply (block_start) as PC1_INSTR; eauto.
      { rewrite NEXT_PC, SAME_INSTRS. eauto. }
      forward eapply (block_mid BLOCK1) as PC1_INSTR'; eauto.
      des.
      all: (rewrite PC1_INSTR in PC1_INSTR'; discriminate). }
    Qed.
  
  
  (* had to define it separately since otherwise Coq doesn't understand what P is *)
  Definition StepProp n := forall st1 st2 tid (STEPS: (step tid) ^^ n st1 st2)
                             (COMP: exists PO, is_thread_compiled PO (instrs st1))
                             bst1 (BST1: st1 = bst2st bst1)
                             bst2 (BST2: st2 = bst2st bst2),
      (omm_block_step tid)＊ bst1 bst2.

  Lemma acb_iff_bst st (COMP: exists PO, is_thread_compiled PO (instrs st)):
    at_compilation_block st <-> exists bst, st = bst2st bst.
  Proof. Admitted.

  Lemma st_bst_prog_blocks bst block (COMP: exists PO, is_thread_block_compiled PO (binstrs bst)):
    on_block (bst2st bst) block <-> Some block = nth_error (binstrs bst) (bpc bst).
  Proof. Admitted. 
  
  Lemma oseq_between_acb: forall n, StepProp n.
  Proof.
    apply lt_ind.
    { red. intros. apply steps0 in STEPS. subst.
      replace bst2 with bst1; [apply rt_refl| ].
      admit. }
    unfold StepProp in *. intros. desc.
    assert (at_compilation_block st1) as ACB1 by admit. 
    assert (at_compilation_block st2) as ACB2 by admit. 
    unfold at_compilation_block in ACB1. desf. 
    2: { destruct n.
         { (* generalize it? *)
           apply steps0 in STEPS.
           (*see the same above *)
           admit.  }
         forward eapply (@steps_sub _ (step tid) (S n) _ _ 1) as [st' STEP];
           [omega | eauto |].
         apply (same_relation_exp (pow_unit (step tid))) in STEP.
         do 2 (red in STEP; desc). 
         cut (None = nth_error (instrs (bst2st bst1)) (pc (bst2st bst1))); [congruence| ].
         symmetry. apply nth_error_None. red in ACB1. omega. }
    pose proof (le_lt_dec (length block) n) as LEN. destruct LEN.
    { forward eapply block_steps_selection as [st' [OSEQ NEXT_STEPS]]; eauto.
      forward eapply (oseq_continuos OSEQ) as ACB'; eauto.
      assert (exists PO', is_thread_compiled PO' (instrs st')) as COMP'.
      { replace (instrs st') with (instrs (bst2st bst1)); eauto.
        apply steps_same_instrs. exists tid.
        (* remove duplicated proof *)
        red in OSEQ. desc. rewrite crt_num_steps. eexists. eauto. }
      assert (LEN': n - length block < n).
      { red in ACB1. desc. inversion COMP_BLOCK; subst; simpl in *; omega. }
      pose proof (proj1 (@acb_iff_bst st' COMP') ACB'). destruct H0 as [bst' BST']. 
      specialize (H (n - length block) LEN' st' (bst2st bst2) tid NEXT_STEPS COMP' bst' BST' bst2).
      apply clos_trans_in_rt. apply t_step_rt. exists bst'. split.         
      2: { apply H. auto. }
      red. exists block. split.
      2: { red in ACB1. desc. vauto. }
      red.
      splits.
      { apply st_bst_prog_blocks; eauto.
        exists PO. red in COMP. desc. replace (binstrs bst1) with BPI; auto.         
        admit. }
      subst. red in OSEQ. desc.
      replace block0 with block in * by admit.
      auto. }
    destruct (NPeano.Nat.eq_0_gt_0_cases n).
    { subst. apply steps0 in STEPS.
      (* same as above *) admit. }
    forward eapply (no_acb_between) as NO_ACB2; vauto.
    omega.
  Admitted. 
    
  Definition is_block_terminal bst := bpc bst >= length (binstrs bst). 

  Lemma steps_imply_ommblocks bfin tid (* (TERM: is_block_terminal bfin) *)
        (COMP: exists PO, is_thread_block_compiled PO (binstrs bfin)):
    let fin := (bst2st bfin) in 
    (step tid)＊ (init (instrs fin)) fin -> (omm_block_step tid)＊ (binit (binstrs bfin)) bfin.
  Proof.
    intros fin STEPS. apply crt_num_steps in STEPS as [n STEPS].
    eapply oseq_between_acb; eauto.
    unfold bst2st, binit, init. simpl.
    desc. exists PO. red. exists (binstrs bfin). split; auto. 
  Qed. 
    
  Lemma compilation_bijective: forall PI PO PO' (COMP: is_thread_compiled PO PI)
                                 (COMP': is_thread_compiled PO' PI),
      PO' = PO. 
  Proof.
  Admitted.

  Lemma firstn_injective {A: Type} (l: list A) x y
        (SAME: firstn x l = firstn y l):
    x = y \/ (x >= length l /\ y >= length l). 
  Proof.
  Admitted.

  Lemma terminal_exact_pc st (TERM: is_terminal st):
    pc st = length (instrs st).
  Proof.
    (* a program can be adjusted so all gotos pointing somewhere outside the program will point exactly where program ends *)
  Admitted.

  Lemma leibniz : forall {A:Type} (x y:A),
                  (x = y) ->
                  forall (P : A -> Prop), P x -> P y.
Proof.
  intros A x y H P.
  rewrite H.
  auto.
Qed.

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
    
  Lemma thread_execs tid PO PI (COMP: is_thread_compiled PO PI)
        SGI (ExI: thread_execution tid PI SGI) (WFL: Wf_local SGI):
    exists SGO, Othread_execution tid PO SGO /\
           same_behavior_local SGO SGI /\
           Wf_local SGO. 
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
      rewrite <- COMP0.
      rewrite SAME_INSTRS. rewrite <- terminal_exact_pc; auto.
      (* TODO: why so complicated? *)      
      apply state_record_equality. } 

    assert (is_block_terminal bsti_fin) as BLOCK_TERM. 
    { red. destruct (dec_ge (bpc bsti_fin) (length (binstrs bsti_fin))); auto. }
    assert (exists n_osteps, (omm_block_step tid) ^^ n_osteps (binit BPI) bsti_fin) as [n_osteps OMM_STEPS]. 
    { apply crt_num_steps.
      forward eapply (@steps_imply_ommblocks bsti_fin tid); eauto.
      rewrite <- BST. apply crt_num_steps.
      rewrite <- SAME_INSTRS. eauto. }
    
    assert (BY_STEPS:
              forall i bsti_i (INDEX: i <= n_osteps)
                (STEPS_TO: (omm_block_step tid)^^i (binit BPI) bsti_i)
                (STEPS_FROM: (omm_block_step tid)^^(n_osteps - i) bsti_i bsti_fin),
                 exists sto_i,
                 (Ostep tid)^^i (init PO) sto_i /\
                 mm_similar_states sto_i bsti_i ).
    { induction i.
      - intros bsti_i _ STEPS_TO STEPS_FROM.
        exists (init PO). split; [basic_solver| ].
        replace (bsti_i) with (binit BPI); [apply init_mm_same; auto| ].
        generalize STEPS_TO. simpl. basic_solver 10.
      - intros bsti_i INDEX STEPS_TO STEPS_FROM.
        rewrite step_prev in STEPS_TO.
        destruct STEPS_TO as [bsti_i' [STEPS_TO' STEPS_FROM']].
        forward eapply IHi as [sto' [OSTEPS' MM_SIM']]. 
        { omega. }
        { eauto. }
        { apply (@steps_split _ _ _ 1 (n_osteps - S i)); [omega| ].
          eexists. split; eauto. simpl. basic_solver. }

        forward eapply (@clos_refl_trans_mori _ (omm_block_step tid) (block_step tid)).
        { red. ins. apply bs_extract. auto. }
        intros OB_B.
        forward eapply (pair_step MM_SIM' STEPS_FROM') as [sto [OSTEP MM_SIM]].
        { apply OB_B. apply crt_num_steps. exists i.
          replace (binstrs bsti_i') with BPI; auto.
          replace BPI with (binstrs bsti_fin); auto. symmetry. 
          apply (@inclusion_t_ind _ (block_step tid) (fun x y => binstrs x = binstrs y)).
          { red. ins. eapply SAME_BINSTRS. eauto. }
          { red. ins. congruence. }
          apply t_step_rt. exists bsti_i. split.
          { apply bs_extract. auto. }
          apply OB_B. apply crt_num_steps. eexists. eauto. }
        exists sto. split; auto. apply step_prev. eexists. split; eauto. }
        
    forward eapply (BY_STEPS n_osteps bsti_fin (Nat.le_refl n_osteps)) as [sto_fin [OSTEPS MM_SIM]].
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
           subst bsti_fin. simpl. auto. }
      replace (pc sto_fin) with (bpc bsti_fin).
      2: { red in MM_SIM. desc. auto. }
      apply BLOCK_TERM. }
    { red in MM_SIM. desc.
      replace SGI with (bG bsti_fin); auto. }
    red in MM_SIM. desc.
    apply (Wfl_subgraph MM_SIM1).
    replace (bG bsti_fin) with SGI; auto.
  Qed.

  Definition RWO GI := (RW GI \₁ dom_rel (rmw GI)). 

  Lemma same_beh_implies_similar_rels GO GI (SB: same_behavior GO GI):
    ⟪ SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘⟫ /\
    (* ⟪ SC': Sc GO ≡₁ Sc GI ⟫ /\ *)
    ⟪ SC': Sc GO ≡₁ RWO GI ∩₁ Sc GI ⟫ /\
    ⟪ FR': fr GO ≡ ⦗set_compl (dom_rel (rmw GI))⦘ ⨾ fr GI ⟫.
  Proof.
  (*   red in SB. desc. red in SAME_LOCAL. desc.  *)
  (*   assert (SB': sb GO ≡ ⦗RW GI \₁ dom_rel (rmw GI)⦘ ⨾ sb GI ⨾ ⦗RW GI \₁ dom_rel (rmw GI)⦘). *)
  (*   { unfold Execution.sb.         *)
  (*     rewrite !seqA. do 2 seq_rewrite <- id_inter. *)
  (*     rewrite set_interC.  *)
  (*     rewrite RESTR_EVENTS.  *)
  (*     basic_solver. } *)
  (*   splits; auto.  *)
  (*   { rewrite SAME_LAB. auto. } *)
  (*   { unfold fr. rewrite SAME_CO. rewrite <- seqA. apply seq_more; [| basic_solver]. *)
  (*     rewrite EXT_RF.  basic_solver. } *)
    (* Qed.  *)
  Admitted. 

  Lemma empty_inter_minus_same {A: Type} (X Y: A -> Prop):
    X ∩₁ Y ≡₁ ∅ -> X \₁ Y ≡₁ X.
  Proof. 
    ins. red. split; [basic_solver| ].
    red. ins.
    red in H. desc.
    red. split; auto.
    red in H. specialize (H x).
    red. ins. apply H. basic_solver. 
  Qed.

  Lemma set_equiv_exp_iff {A : Type} (s s' : A -> Prop):
    s ≡₁ s' <-> forall x : A, s x <-> s' x.
  Proof.
    red. split; [apply set_equiv_exp| ].
    ins. red. split.
    all: red; ins; apply H; auto.
  Qed. 

    
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

  Lemma SAME_INIT GO GI (SB: same_behavior GO GI): forall l, E GO (InitEvent l) <-> E GI (InitEvent l). 
  Proof. Admitted. 

  Lemma ocaml_no_rmw_tmp GO GI (SB: same_behavior GO GI):
    GO.(rmw) ≡ ∅₂.
  Proof. Admitted.
  
  Lemma same_beh_implies_similar_intrarels GO GI (SB: same_behavior GO GI):
    ⟪DATA_SIM: data GO ≡ restr_rel (RWO GI) (data GI) ⟫ /\
    ⟪CTRL_SIM: ctrl GO ≡ restr_rel (RWO GI) (ctrl GI) ⟫ /\ 
    ⟪ADDR_SIM: addr GO ≡ restr_rel (RWO GI) (addr GI) ⟫ /\
    ⟪SB_SIM: sb GO ≡ restr_rel (RWO GI) (sb GI) ⟫ /\
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

  Lemma wf_init_same_beh GO GI (SB: same_behavior GO GI) (WF: Wf GI):
    forall l, lab GO (InitEvent l) = Astore Xpln Opln l 0.
  Proof. Admitted. 
  
  Lemma Wf_subgraph GO GI (SB: same_behavior GO GI) (WF: Wf GI): Wf GO.
  Proof.
    pose proof SB as SB'. 
    pose proof (same_beh_implies_similar_rels SB). 
    red in SB. desc. red in SAME_LOCAL. desc.
    symmetry in SAME_CO.
    assert (forall (r1 r2 r3: relation actid), r1 ⊆ r2 -> r1 \ r3 ⊆ r2 \r3) as MINUS_INCL. 
    { ins. basic_solver. }
    assert (forall (r1 r3: relation actid) S1 S2, r1 ≡ ⦗S1⦘ ⨾ r1 ⨾ ⦗S2⦘ -> r1 \ r3 ≡ ⦗S1⦘ ⨾ (r1 \ r3) ⨾ ⦗S2⦘) as MINUS_EQUIV. 
    { ins. seq_rewrite H. basic_solver. }
    (* TODO: should we include addr, ctrl equality in same_behavior? *)
    pose proof (same_beh_implies_similar_intrarels SB'). desc. 
    inversion WF. 
    pose proof (ocaml_no_rmw_tmp SB') as NO_RMW. 
    assert (rf GO ≡ restr_rel (RWO GI) (rf GI)) as RF_SIM. 
    { rewrite EXT_RF. rewrite wf_rfD. rewrite restr_relE.
      rewrite !seqA.
      arewrite (⦗(RWO GI)⦘ ⨾ ⦗W GI⦘ ≡ ⦗W GI⦘).
      { rewrite <- id_inter. apply eqv_rel_more. split; [basic_solver| ].
        apply set_subset_inter_r. split; auto.
        unfold RWO. 
        rewrite wf_rmwD.
        red. ins. red. split; [basic_solver| ]. 
        red. ins. red in H0. desc. apply seq_eqv_lr in H0. desc.
        type_solver. }
      arewrite (⦗R GI⦘ ⨾ ⦗(RWO GI)⦘ ≡ ⦗R GI⦘ ⨾ ⦗set_compl (dom_rel (rmw GI))⦘); [| basic_solver].
      rewrite <- !id_inter. apply eqv_rel_more.
      unfold RWO. 
      seq_rewrite set_inter_minus_r.
      arewrite (R GI ∩₁ RW GI ≡₁ R GI) by basic_solver. }
    assert (co GO ≡ ⦗E GO⦘ ⨾ co GO ⨾ ⦗E GO⦘) as ECO. 
    { rewrite RESTR_EVENTS, SAME_CO.
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
    { rewrite RF_SIM, RESTR_EVENTS. fold (RWO GI).
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

    red in SB'. desc.  
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
      apply restr_rel_more; auto. }
    { rewrite (@SUPSET_RESTR _ (addr GO) (sb GO) (E GO)); auto.
      2: { unfold Execution.sb. basic_solver. }
      rewrite !seqA. do 2 seq_rewrite <- id_inter. rewrite set_interC.
      rewrite R_SIM, RW_SIM; eauto. 
      rewrite set_interC with (s' := RW GI). do 2 seq_rewrite id_inter.
      rewrite !seqA. seq_rewrite <- restr_relE.
      rewrite <- seqA with (r2 := ⦗RW GI⦘). rewrite <- seqA with (r1 := ⦗R GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; auto. 
      rewrite ADDR_SIM. rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l. 
      apply restr_rel_more; auto. }
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
      apply restr_rel_more; auto. }
    { rewrite CTRL_SIM, SB_SIM. rewrite RESTR_SEQ. apply restr_rel_mori; auto. }
    { rewrite ERF.
      rewrite RF_SIM; eauto. 
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. rewrite W_SIM, R_SIM; eauto. 
      rewrite set_interC with (s' := R GI). rewrite !id_inter.
      rewrite !seqA. seq_rewrite <- !restr_relE.
      rewrite <- seqA with  (r3 := ⦗E GO⦘). rewrite <- seqA with  (r1 := ⦗W GI⦘).
      seq_rewrite <- restr_relE. apply restr_rel_more; [basic_solver|].
      rewrite <- restr_seq_eqv_r, <- restr_seq_eqv_l.
      apply restr_rel_more; [basic_solver|]. auto. }
    { rewrite ERF. red. ins.
      apply seq_eqv_lr in H. desc.
      red.
      rewrite (same_relation_exp EXT_RF) in H0. apply seq_eqv_r in H0. desc. 
      replace (loc (lab GO) x) with (loc (lab GI) x).
      replace (loc (lab GO) y) with (loc (lab GI) y).
      apply wf_rfl; auto.
      all: unfold loc; rewrite SAME_LAB; auto. }
    { red. ins.
      rewrite (same_relation_exp ERF) in H. apply seq_eqv_lr in H. desc.
      rewrite (same_relation_exp EXT_RF) in H0. apply seq_eqv_r in H0. desc.
      replace (val (lab GO) a) with (val (lab GI) a).
      replace (val (lab GO) b) with (val (lab GI) b).
      apply wf_rfv; auto. 
      all: unfold val; rewrite SAME_LAB; auto. }
    { rewrite RF_SIM. rewrite restr_relE. rewrite !transp_seq.
      rewrite !transp_eqv_rel. rewrite seqA, <- restr_relE.
      apply functional_restr. auto. }
    { rewrite ECO at 2.
      rewrite !seqA. do 2 seq_rewrite <- id_inter.
      rewrite set_interC. rewrite W_SIM; eauto. 
      rewrite set_interC at 2. do 2 rewrite id_inter.
      rewrite SAME_CO at 2. rewrite !seqA. seq_rewrite <- wf_coD.
      rewrite <- SAME_CO. apply ECO. }
    { rewrite ECO. red. ins.
      apply seq_eqv_lr in H. desc.
      red.
      rewrite (same_relation_exp SAME_CO) in H0.
      replace (loc (lab GO) x) with (loc (lab GI) x).
      replace (loc (lab GO) y) with (loc (lab GI) y).
      apply wf_col; auto.
      all: unfold loc; rewrite SAME_LAB; auto. }
    { rewrite SAME_CO. auto. }
    { ins. specialize (wf_co_total ol).
      forward eapply (@is_total_more _ (E GI ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol)) (E GO ∩₁ W GI ∩₁ (fun x : actid => loc (lab GI) x = ol))).
      { apply set_equiv_inter; [| basic_solver].
        rewrite RESTR_EVENTS.
        rewrite set_interA. rewrite set_inter_minus_l.
        arewrite (RW GI ∩₁ W GI ≡₁ W GI) by basic_solver.
        rewrite empty_inter_minus_same; [auto| ]. 
        rewrite wf_rmwD. type_solver. }
      { symmetry. eapply SAME_CO. }
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
        rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. } }
    { rewrite SAME_CO. auto. }
    { ins.
      eapply SAME_INIT.
      { red. splits; eauto. }
      apply wf_init. desc.
      exists b. split; auto.
      apply (proj1 RESTR_EVENTS). auto.
      rewrite <- H0. unfold loc. rewrite SAME_LAB; auto. }
    eapply wf_init_same_beh; eauto.
    red. splits; eauto. 
  Qed.

  
End OCamlMM_TO_IMM_S_PROG.

Section CompCorrHelpers.
  Lemma GI_1thread_omm_premises tid PO PI (COMP: is_thread_compiled PO PI) Gi
        (EXEC: thread_execution tid PI Gi):
    omm_premises_hold Gi.
  Proof. Admitted.

End CompCorrHelpers. 

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
    


  Lemma omm_premises_thread_local TSG (OMM_PREM_THREADS: forall tid Gi (THREAD_Gi: Some Gi = IdentMap.find tid (Gis TSG)), omm_premises_hold Gi):
    omm_premises_hold (tsg2g TSG). 
  Proof.
    remember (tsg2g TSG) as G.
    (* assert (merge : relation actid -> thread_separated_graph -> relation actid). *)
    (* { admit. } *)
    (* assert (forall (P: execution -> actid -> Prop), *)
    (*            P G ≡₁ fun e => exists tid Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ *)
    (*                                   P Gi e) as EV_PROPS_UNION by admit.  *)
    (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_w G.(lab) a))). *)
    (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_r G.(lab) a))).  *)
    (* pose proof (EV_PROPS_UNION (fun G a => is_true (is_sc G.(lab) a))). *)
    (* assert (forall (r1 r2: relation actid), codom_rel (r1 ∪ r2) ≡₁ codom_rel r1 ∪₁ codom_rel r2). *)
    (* { ins. basic_solver. } *)
    assert (E G ≡₁ set_bunion (fun _ => True) (fun tid e => exists Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ E (Gi) e)) as E_BUNION by admit.     
    (* red. splits. *)
    (* { seq_rewrite H. rewrite H1.  *)
    (*   rewrite (EV_PROPS_UNION (fun G a => is_true (is_f G.(lab) a))). *)
    (* assert (E G ≡₁ fun e => exists tid Gi, Some Gi = IdentMap.find tid (Gis TSG) /\ *)
    (*                                E Gi e) by admit. *)
    
    
  Admitted.  

  Lemma GI_omm_premises : omm_premises_hold GI.
  Proof.
    rewrite <- (proj1 tsg_g_bijection). 
    apply omm_premises_thread_local.
    ins.
    apply program_execution_defs_equiv in ExecI.
    red in ExecI.
    (* bug? desf hangs here *)
    destruct ExecI as [SAME_KEYS THREAD_EXEC]. clear ExecI. 
    assert (exists PIi, Some PIi = IdentMap.find tid ProgI) as [PIi PIi_THREAD].
    { apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. }
    red in THREAD_EXEC. specialize (THREAD_EXEC tid PIi PIi_THREAD Gi THREAD_Gi).
    destruct Compiled as [SAME_TIDS TID_COMPILED]. clear Compiled. 
    assert (exists POi, Some POi = IdentMap.find tid ProgO) as [POi POi_THREAD].
    { apply find_iff_in. apply SAME_TIDS. apply find_iff_in. eauto. }
    specialize (TID_COMPILED tid POi PIi POi_THREAD PIi_THREAD).
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
    
  Lemma build_GOi_map TSGI (WFG: Wf (tsg2g TSGI)) (TSG_EXECI : program_execution_tsg ProgI TSGI):
    exists GOis, same_keys GOis (Gis TSGI) /\
            forall tid GOi (THREAD_GRAPH: Some GOi = IdentMap.find tid GOis)
              GIi (THREAD: Some GIi = IdentMap.find tid (Gis TSGI))
              Po (THREAD_O: Some Po = IdentMap.find tid ProgO),
              same_behavior_local GOi GIi /\
              Othread_execution tid Po GOi. 
  Proof.
    set (P := fun tid GOi =>
                forall GIi (THREAD: Some GIi = IdentMap.find tid (Gis TSGI))
                  Po (THREAD_O: Some Po = IdentMap.find tid ProgO),
                  same_behavior_local GOi GIi /\
                  Othread_execution tid Po GOi). 
    apply (@IdentMap_explicit execution execution P (Gis TSGI)).
    intros tid THREAD.
    red in TSG_EXECI. desc.
    red in Compiled. destruct Compiled as [SAME_THREADS THREADS_COMPILED]. clear Compiled.
    assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI]. 
    { apply find_iff_in. apply SAME_KEYS. auto. }
    assert (exists Po, Some Po = IdentMap.find tid ProgO) as [Po THREAD_PROGO]. 
    { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. }
    apply find_iff_in in THREAD. destruct THREAD as [Gi THREAD_EXEC]. 
    specialize (THREAD_GRAPH_EXEC tid Pi THREAD_PROGI Gi THREAD_EXEC). 
    forward eapply thread_execs; eauto.
    { pose proof (proj1 (Wf_tsg (tsg2g TSGI))). apply H in WFG. desc.
      eapply WFG. rewrite (proj2 tsg_g_bijection). eauto. }
    ins. unfold P. destruct H as [GOi GOi_PROPS].
    exists GOi. ins.
    (* TODO: correct this duplication? *)
    replace GIi with Gi; [| congruence]. replace Po0 with Po; [| congruence].
    desc. split; auto. 
  Qed. 

  Lemma TSGO_exists TSGI (WFG: Wf (tsg2g TSGI)) (TSG_EXECI : program_execution_tsg ProgI TSGI):
    exists TSGO,
    Oprogram_execution_tsg TSGO OCamlProgO /\
    co_tsg TSGO ≡ co_tsg TSGI /\
    rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘ /\
    (forall tid : IdentMap.key,
        IdentMap.In tid (Gis TSGO) ->
        forall GOi GIi : execution,
          Some GOi = IdentMap.find tid (Gis TSGO) ->
          Some GIi = IdentMap.find tid (Gis TSGI) -> same_behavior_local GOi GIi). 
  Proof.
    pose proof (build_GOi_map WFG TSG_EXECI) as [GOis [SAME_TIDS GOis_PROPS]]. 
    set (TSGO := {| Gis := GOis;
                    Einit_tsg := Einit_tsg TSGI;
                    rf_tsg := rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘;
                    co_tsg := co_tsg TSGI;
                    rmw_tsg := ∅₂; |} ).
    exists TSGO.
    destruct Compiled as [SAME_THREADS THREADS_COMPILED]. clear Compiled.
    splits; [| basic_solver | subst TSGO; basic_solver |]. 
    { red. ins. 
      specialize (SAME_THREADS tid).
      assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI]. 
      { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. }
      assert (exists GIi, Some GIi = IdentMap.find tid (Gis TSGI)) as [Gi THREAD_EXECI].
      { red in TSG_EXECI. desc. red in SAME_KEYS. specialize (SAME_KEYS tid).
        apply find_iff_in. apply SAME_KEYS. apply find_iff_in. eauto. }
      assert (exists GOi, Some GOi = IdentMap.find tid (Gis TSGO)) as [GOi THREAD_EXECO].
      { simpl. apply find_iff_in, SAME_TIDS, find_iff_in. eauto. }
      forward eapply GOis_PROPS; eauto.
      ins. desc. eauto. }
    ins.
    assert (exists Pi, Some Pi = IdentMap.find tid ProgI) as [Pi THREAD_PROGI]. 
    { red in TSG_EXECI. desc. red in SAME_KEYS. apply find_iff_in.
      apply SAME_KEYS. apply find_iff_in. eauto. }
    assert (exists Po, Some Po = IdentMap.find tid ProgO) as [Po THREAD_PROGO]. 
    { apply find_iff_in. apply SAME_THREADS. apply find_iff_in. eauto. }
    forward eapply GOis_PROPS; eauto. ins. desc. auto. 
  Qed. 
    
  Lemma GO_exists: exists GO,
      Oprogram_execution OCamlProgO GO /\
      same_behavior GO GI. 
  Proof.
    pose proof (proj1 (program_execution_defs_equiv ProgI GI) ExecI) as TSG_EXECI. 
    remember (g2tsg GI) as TSGI.
    cut (exists TSGO, Oprogram_execution_tsg TSGO OCamlProgO /\
                 co_tsg TSGO ≡ co_tsg TSGI /\
                 rf_tsg TSGO ≡ rf_tsg TSGI ⨾ ⦗set_compl (dom_rel (rmw_tsg TSGI))⦘ /\
                 forall tid (PROG_THREAD: IdentMap.In tid (Gis TSGO))
                   GOi GIi (THREAD_GO: Some GOi = IdentMap.find tid (Gis TSGO))
                   (THREAD_GI: Some GIi = IdentMap.find tid (Gis TSGI)),
                   same_behavior_local GOi GIi
                   ). 
    { intros [TSGO [TSGO_ExecO [CO_SAME [RF_SIM GOis_sbl]]]]. desc.      
      exists (tsg2g TSGO). 
      split. 
      { apply (proj2 (Oprogram_execution_defs_equiv (tsg2g TSGO) OCamlProgO)).
        rewrite ((proj2 tsg_g_bijection) TSGO). auto. }
      apply ((same_behavior_defs_equiv (tsg2g TSGO) GI)).
      rewrite ((proj2 tsg_g_bijection) TSGO). rewrite <- HeqTSGI.
      red. splits; auto. }
    apply TSGO_exists; auto.
    rewrite HeqTSGI, (proj1 tsg_g_bijection). auto. 
  Qed. 

  Lemma restr_rel_empty_minus {T: Type} (r r': relation T) (A B: T -> Prop)
        (NO_INTER: A ∩₁ B ≡₁ ∅):
    restr_rel A r \ restr_rel B r' ≡ r. 
  Proof. Admitted. 
    
  Lemma ocaml_no_rmw GO (ExecO: Oprogram_execution OCamlProgO GO):
    GO.(rmw) ≡ ∅₂.
  Proof. Admitted.

  Lemma graph_switch GO (SB: same_behavior GO GI) (OMM_I: ocaml_consistent GI)
        (ExecO: Oprogram_execution OCamlProgO GO):
    ocaml_consistent GO.
  Proof.
    pose proof (same_beh_implies_similar_rels SB). 
    pose proof (Wf_subgraph SB WFI) as WFO. 
    red in SB. desc. red in SAME_LOCAL. desc.
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
      rewrite SAME_CO, EXT_RF. basic_solver. }
    red. red in OMM_I.
    splits; auto.
    { red.
      rewrite R_SIM.
      2: { red. splits; eauto. }
      rewrite RESTR_EVENTS, EXT_RF.
      desc. red in Comp.
      rewrite set_interA, set_inter_minus_l.
      arewrite (RW GI ∩₁ R GI ≡₁ R GI) by basic_solver.
      rewrite set_inter_minus_r. 
      rewrite codom_eqv1.
      rewrite set_minusE.
      apply set_subset_inter; [| basic_solver].
      vauto. }
    { red. seq_rewrite ocaml_no_rmw; auto. basic_solver. }
    { rewrite HBO', (same_relation_sym SAME_CO). desc.  auto. }
    { unfold fr. rewrite HBO', (same_relation_sym SAME_CO). 
      arewrite (rf GO ⊆ rf GI) by rewrite EXT_RF; auto. 
      auto. desc. auto. }    
    assert (W_RMW: W GI ⊆₁ RW GI \₁ dom_rel (rmw GI)).
    { rewrite set_minusE.
      apply set_subset_inter_r. split; [basic_solver| ].
      rewrite (WFI.(wf_rmwD)).
      rewrite dom_eqv1. rewrite set_compl_inter.
      unionR left. type_solver. }
    arewrite (rfe GO ⊆ rfe GI).
    { unfold rfe. rewrite SB', EXT_RF.
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
    
    arewrite (coe GO ≡ coe GI).
    { unfold coe.      
      rewrite SB', <- SAME_CO.
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

    rewrite SC'. 
    arewrite (sb GO ⊆ sb GI) by rewrite SB'; basic_solver.
    desc.
    arewrite (RWO GI ∩₁ Sc GI ⊆₁ Sc GI); auto. basic_solver. 
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
    splits; auto.
    apply graph_switch; auto.
    apply (imm_implies_omm). 
  Qed.  

End CompilationCorrectness.       