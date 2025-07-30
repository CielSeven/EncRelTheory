Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import Coq.Logic.Classical_Prop.
From SetsClass Require Import SetsClass.
From AUXLib Require Import Feq Idents  List_lemma VMap int_auto ListLib.
From compcert.lib Require Import Integers.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics ImpHoareTactics slllib GraphAdjList. 
From EncRelSeq Require Import callsem basicasrt contexthoare_imp. 
From EncRelSeq.MonadsAsHigh.AbsMonad Require Import  encimpmonad.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From AUXLib Require Import GraphLib.
From Examples Require Import  CGraphDFS dfs dfsproof.


Module CGraphDFSProof.
Import EnvProgramSem.
Import NormalContextualImp.
Import NormalImpHoareRules.
Import NormalImpHoareTac.
Import CDFS_AdjList.
Import RelImpAbsMonad.

Import SetsNotation.
Local Open Scope sets.
Import ImpRules.
Local Open Scope asrt_scope.
Local Open Scope com_scope.
Import MonadNotation.
Local Open Scope monad.

Definition vis_func (vis: Z -> Prop) (cvis : Z -> Z) : Prop := 
    forall v, (vis v <-> cvis v <> 0) /\ ((~ vis v) <-> cvis v = 0).

Definition dfs_field cvis: Vertex_field :=
 {| vist := cvis; |}.

Definition cvisupdate (v: Z) (n: Z) (cvis : Z -> Z) : Z -> Z :=
  fun x => if (x =? v) then n else cvis x.

Definition dfs_rec_spec := {|
  FS_With := (unit -> (state Z) -> Prop) * (PreGraph Z Z) * list Z * Edge_Order * Perm.t * addr ;
  FS_Pre := fun '(X, pg, vertexl, E_Order, Gsh, xv) =>
            (EX vis cvis, 
            !! (vlis_prop pg vertexl) && !! (pg.(vvalid) xv) && 
            !! (vis_func vis cvis) &&  !! (~ vis xv)  &&
            !! (Exec (fun s => s.(visited) = vis /\ s.(stack) = nil) (DFS pg xv) X) &&
            GV _arg1 @ vptr ↦ₗ xv && 
            @graphrep E_Order Gsh ➀ pg (dfs_field cvis) );
  FS_Post := fun '(X, pg, vertexl,  E_Order, Gsh, xv) =>
            (EX vis cvis, 
            !! (vis_func vis cvis) &&  
            !! (Exec  (fun s => s.(visited) = vis /\ s.(stack) = nil) 
                          (return tt) X) &&
            @graphrep E_Order Gsh ➀ pg (dfs_field cvis) )
|}.


Definition dfs_rec_spec_aux := {|
  FS_With := (unit -> (state Z) -> Prop) * (PreGraph Z Z) * list Z * Edge_Order * Perm.t * list Z * addr * Z * Z * (Z -> Prop);
  FS_Pre := fun '(X, pg, vertexl, E_Order, Gsh, stk, xv, v, e, vis) =>
            (EX cvis, 
            !! (vlis_prop pg (v :: vertexl)) && !! (pg.(vvalid) xv) && 
            !! (vis_func vis cvis) &&  !! (~ vis xv) && 
            !! (out_edges pg v e) &&
            !! (pg.(dst) e = xv) &&
            !! Exec
              (fun s : state Z => visited s = vis /\ stack s = v :: stk)
              (DFS pg xv) X &&
            GV _arg1 @ vptr ↦ₗ xv && 
            @graphrep E_Order Gsh ➀ pg (dfs_field cvis) );
  FS_Post := fun '(X, pg, vertexl, E_Order, Gsh, stk, xv, v, e, vis) =>
            (EX vis_new cvis, 
            !! (vis_func vis_new cvis) &&  !! (vis_new xv) && 
            !! (forall w, vis w -> vis_new w ) &&
            !! (Exec  (fun s => s.(visited) = vis_new /\ s.(stack) = stk) 
                          (repeat_break (body_DFS pg) v) X) &&
            @graphrep E_Order Gsh ➀ pg (dfs_field cvis) )
|}. 

Definition dfs_rec_spec_fc := {|
  FS_With := (PreGraph Z Z) * list Z * Edge_Order * Perm.t * addr ;
  FS_Pre := fun '(pg, vertexl, E_Order, Gsh, xv) =>
            (!! (vlis_prop pg vertexl) && !! (pg.(vvalid) xv) && 
            GV _arg1 @ vptr ↦ₗ xv && 
            @graphrep E_Order Gsh ➀ pg (dfs_field (fun v => 0)) );
  FS_Post := fun '(pg, vertexl, E_Order, Gsh, xv) =>
            (EX cvis, 
            !! (forall u, cvis u <> 0 <-> reachable pg xv u) &&
            @graphrep E_Order Gsh ➀ pg (dfs_field cvis) )
|}.

Lemma step_aux_elis_prop {E_Order:Edge_Order}: forall pg x y e el,
  elis_prop pg x el ->
  step_aux pg e x y -> 
  In e el.
Proof.
  intros.
  inversion H0.
  inversion H.
  apply Elis_Rep.
  unfold out_edges.
  eauto.
Qed.

Lemma push_stack_eval : forall vis stk x,
  (fun s : state Z => visited s = vis /\ stack s = stk) -@ push_stack x -⥅ (fun s : state Z => visited s = vis /\ stack s = x :: stk) ♯ tt.
Proof.
  intros.
  unfold hs_eval, push_stack.
  intros.
  exists (Build_state _ (x :: stk) vis).
  simpl.
  destruct H.
  splits;
  congruence.
Qed.

Lemma pop_stack_eval : forall vis stk x,
  (fun s : state Z => visited s = vis /\ stack s = x :: stk) -@ pop_stack -⥅ (fun s : state Z => visited s = vis /\ stack s = stk) ♯ x.
Proof.
  intros.
  unfold hs_eval, pop_stack.
  intros.
  exists (Build_state _ (stk) vis).
  simpl.
  destruct H.
  splits;
  congruence.
Qed.


Lemma visit_eval : forall vis stk x,
  (fun s : state Z => visited s = vis /\ stack s = stk) -@ visit x -⥅ (fun s : state Z => visited s = vis ∪ [x] /\ stack s = stk) ♯ tt.
Proof.
  intros.
  unfold hs_eval, visit.
  intros.
  exists (Build_state _ (stk) (vis ∪ [x])).
  simpl.
  destruct H.
  splits;
  try congruence.
  rewrite H.
  reflexivity.
Qed.


Lemma vis_func_update : forall vis cvis x,
  vis_func vis cvis ->
  vis_func (vis ∪ [x]) (cvisupdate x 1 cvis).
Proof.
  unfold vis_func.
  intros.
  split.
  - split;intros.
    + unfold cvisupdate.
      destruct (v =? x ) eqn:?;[ lia | ].
      apply H.
      sets_unfold in H0.
      destruct H0;auto.
      lia.
    + unfold cvisupdate in H0.
      destruct (v =? x ) eqn:?;auto.
      sets_unfold.
      right. lia. 
      sets_unfold.
      left. 
      apply H. auto.
  - split;intros.
    + unfold cvisupdate.
      destruct (v =? x ) eqn:?;auto.
      sets_unfold in H0. exfalso. apply H0. right. lia.
      apply H.
      sets_unfold in H0.
      auto.
    + unfold cvisupdate in H0.
      destruct (v =? x ) eqn:?;auto.
      lia.
      sets_unfold.
      unfold not. intros.
      destruct H1.
      apply H in H1;auto.  
      lia.
Qed.


Definition ρ : program := 
  (_dfs_rec, f_dfs_rec):: nil.

Definition Δ : funcspecs := 
  (_dfs_rec, dfs_rec_spec):: 
  (_dfs_rec, dfs_rec_spec_aux):: 
  (_dfs_rec, dfs_rec_spec_fc)::nil. 

Ltac hoareasrt_simpl ::= asrt_simpl_aux graph_asrt_simpl.

Lemma dfs_rec_triplesat: triple_body_nrm ρ Δ _dfs_rec dfs_rec_spec.
Proof.
  funcproof_init.
  rename z into x. rename v into Gsh. rename l into vertexl. 
  rename v0 into E_Order.  rename v1 into pg. rename v2 into vis. rename v3 into cvis.
  (* _x := % _arg1; *)
  forward_simpl.
  (* [_x + 1]:= 1; *)
  (* 取出结点x的信息*)
  pose proof vertex_in_vprop pg H H0 as [vl ?] . clear H. rename H4 into H.
  eapply hoare_conseq_pre.
  erewrite unfold_graph;[refl | eauto ].
  eapply hoare_conseq_pre.
  cbn [vertex_storage]. refl.
  hoare_simpl_pre.
  rename l into el.
  unfold AVertex, field_storage.
  hoare_simpl_pre.
  forward_simpl.
  entailer!.
  (* abs step *)
  unfold DFS in H3.
  eapply highstepbind_derive in H3.
  2: { apply visit_eval. } 
  (* _e := [_x]; *)
  forward_simpl.
  rename x into v_ptr.
  eapply hoare_conseq_pre. 
  instantiate (1:= 
  EX el1 el2 cvis_loop vis_loop,
  !! (el1 ++ el2 = el) && 
  !! (vis_func vis_loop cvis_loop) && 
  !! (isvalidptr v_ptr) && 
  !! (Exec
       (fun s : state Z =>
        visited s = vis_loop /\ stack s =  nil)
       (repeat_break (body_DFS pg) v_ptr) X) && 
   !! (forall e, List.In e el1 -> vis_loop (pg.(dst) e) ) &&
  LV _e @ vptr ↦ₗ hd 0 el2 &&
  (LV _x @ vptr ↦ₗ  v_ptr &&
    PV v_ptr + 1 @ vint ↦ₗ (vist (dfs_field cvis_loop) v_ptr) $ ➀ **
    (PV v_ptr @ vptr ↦ₗ hd 0 el $ Gsh **
    (edge_seg Gsh pg el1 (hd 0 el2) **
    (edge_storage Gsh pg el2 **
      vertex_storage Gsh ➀ pg (dfs_field cvis_loop) vl))))
  ).
  { Exists nil el (cvisupdate v_ptr 1 cvis) (vis ∪ [v_ptr]).
    quick_entailer!.
    cbn [edge_seg].
    simpl (vist (dfs_field (cvisupdate v_ptr 1 cvis))).
    unfold cvisupdate at 1.
    rewrite Z.eqb_refl.
    quick_entailer!.
    erewrite vertex_storage_app_r with (vs1:= (v_ptr :: nil)) (vf_new := (dfs_field (cvisupdate v_ptr 1 cvis))).
    entailer!.
    simpl. auto. 
    intros. simpl in H6. 
    simpl. unfold cvisupdate. 
    destruct (v' =? v_ptr) eqn:?;auto.
    lia.
    apply vis_func_update;auto.
  }
  eapply hoare_conseq_post'.
  - eapply hoare_While'.
    { Intros el1 el2 cvis_loop vis_loop.
      symbolic_execution. }
    clear vis cvis H1 H2 H3 H5. 
    hoare_simpl_pre.
    rename l into el1. rename l0 into el2. 
    rename v0 into vis. rename v into cvis.
    rename H6 into Hel1. 
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue.
      symbolic_execution. }
    hoare_simpl_pre.
    destruct el2. 
    { cbn in H6. unfold btrue in H6. contradiction. }
    rename z into e.
    cbn in H6.
    apply btrue_valneq_neq in H6.
    cbn [hd].
    (* _v := [_e]; *)
    cbn [edge_storage]. unfold data_at_t_edge_node.
    hoare_simpl_pre.
    forward_simpl.
    (* _vis := [_v + 1]; *)
    eapply hoare_conseq_pre.
    { instantiate (1:= 
       LV _v @ vptr ↦ₗ pg.(dst) e &&
      (LV _e @ vptr ↦ₗ e &&
      (LV _x @ vptr ↦ₗ v_ptr && @graphrep E_Order Gsh ➀ pg (dfs_field cvis)))).
      sep_apply fold_field_storage.
      asrt_simpl.
      sep_apply (fold_edge_node Gsh e (pg.(dst) e) (hd 0 el2)).
      asrt_simpl.
      sep_apply singleton_eseg.
      asrt_simpl.
      strongseplift (edge_storage Gsh pg el2).
      strongseplift (edge_seg Gsh pg (e :: nil) (hd 0 el2)).
      rewrite sepcon_assoc_logic_equiv.
      unfoldimpmodel.
      rewrite (edge_seg_list Gsh pg (e::nil) el2).
      asrt_simpl.
      simpl (((e :: nil) ++ el2)).
      strongseplift (edge_storage Gsh pg (e :: el2)).
      strongseplift (edge_seg Gsh pg el1 e).
      replace e with (hd 0 (e::el2)) at 1 by (cbn;auto).
      rewrite sepcon_assoc_logic_equiv.
      rewrite (edge_seg_list). unfoldimpmodel.
      rewrite <- H1.
      rewrite <- (fold_graph_field' Gsh ➀ pg (dfs_field cvis) v_ptr vl  (el1 ++ e :: el2)).
      quick_entailer!.
      all : auto.
      rewrite H1. auto.
    }
    eapply hoare_conseq_pre.
    { rewrite unfold_graph;[ | eauto].
      assert (In (pg.(dst) e) (v_ptr :: vl)).
      { apply H. auto. }
      pose proof vertex_storage_valid_pointer  Gsh ➀ pg (dfs_field cvis) (v_ptr :: vl) (pg.(dst) e) H9.
      erewrite (prop_add_left _ _ H10). 
      rewrite fold_graph.
      rewrite unfold_field_storage with (v:= (pg.(dst) e));[ | eauto].
      unfold field_storage.
      refl. 
      auto. }
    hoare_simpl_pre.
    forward_simpl.
    (* If _vis == 0 Then *)
    forward_simpl.
    + (* vist (dfs_field cvis) (pg.(dst) e) == 0 *)
      apply btrue_valeq_iseq in H10.
      simpl in H10.
      (* abs step *)
      rewrite (repeat_break_unfold _ _ ) in H5.
      unfold body_DFS in H5 at 1.
      prog_nf in H5;safe_choice_l H5.
      prog_nf in H5;apply Exec_any_bind with (a:= (pg.(dst) e)) in H5.
      prog_nf in H5;eapply Exec_testst_bind in H5.
      2: { intros st [ ? ?].
        rewrite H11.
        apply H2. auto. }
      prog_nf in H5;eapply Exec_test_bind in H5.
      2: {  exists e. 
        assert (In e el). { rewrite <- H1. apply in_cons_app. }
        constructor;auto.
        apply H4. auto.
        apply H4. auto. }
      prog_nf in H5;eapply highstepbind_derive in H5.
      2: apply push_stack_eval.
      (* % _arg1 := _v; *)
      forward_simpl.
      (* Call (_dfs_rec) *)
      forward_simpl.
      eapply hoare_Call_frm' with (fspec:= dfs_rec_spec_aux) (w:= (X, pg, vl, E_Order, Gsh, nil, pg.(dst) e, v_ptr, e, vis)).
      { cbn;auto. }
      { (* ==> pre*)
        unfold FS_Pre. cbn.
        Exists cvis.
        instantiate (1:= (
        (LV _v @ vptr ↦ₗ pg.(dst) e &&
         (LV _e @ vptr ↦ₗ e &&
          (LV _x @ vptr ↦ₗ v_ptr && emp))))).
        entailer!.
        rewrite <- fold_graph_field with (v:= pg.(dst) e).
        unfold field_storage.
        simpl.
        entailer!.
        { prog_nf in H5. auto. }
        { unfold out_edges. 
          assert (In e el). { rewrite <- H1. apply in_cons_app. }
          constructor;auto.
          apply H4. auto.
          apply H4. auto.  }
        apply H2.
        simpl in H10. auto.
      }
      { refl. }
      solve_closedgvars idtac.
      (* after call *)
      simpl (FS_Post dfs_rec_spec_aux
      (X, pg, vl, E_Order, Gsh, nil, 
      pg.(dst) e, v_ptr, e, vis)).
      rename vis into vis_old. rename cvis into cvis_old.
      clear H5 H10. 
      hoare_simpl_pre.
      rename v into vis. rename v0 into cvis.
      assert (forall e : Z, In e el1 -> vis (pg.(dst) e) ).
      { intros. apply H11. apply Hel1. auto. }
      clear Hel1.
      rename H13 into Hel1. rename H12 into Habs.
      (* _e := [_e + 1] *)
      eapply hoare_conseq_pre.
      erewrite unfold_graph;[refl | eauto ].
      eapply hoare_conseq_pre.
      cbn [vertex_storage]. refl.
      hoare_simpl_pre.
      assert (l = el1 ++ e :: el2).
      { rewrite H1. eapply edge_deterministic;eauto. }
      subst l. clear H12 H13.
      unfold AVertex, field_storage.
      eapply hoare_conseq_pre.
      { rewrite <- edge_seg_list.
        simpl (edge_storage Gsh pg (e :: el2)).
        refl.
      }
      hoare_simpl_pre.
      clear H12 H13.
      forward_simpl.
      Intros v'.
      hoareasrt_simpl.
      Intros.
      clear v' H12.
      Exists (el1 ++ e ::nil) el2 cvis vis.
      quick_entailer!.
      2: { intros.
           apply in_app_or in H12.
           destruct H12.
           apply Hel1. auto.
           simpl in H12. destruct H12;subst;auto. contradiction. }
      2: { rewrite <- H1. rewrite <- app_assoc. simpl. auto.  }
      sep_apply (fold_edge_node Gsh e (pg.(dst) e) (hd 0 el2)).
      asrt_simpl.
      sep_apply singleton_eseg;auto.
      asrt_simpl.
      replace ((hd 0 (e :: el2))) with (hd 0 (e::nil)) by (cbn;auto).
      strongseplift (edge_seg Gsh pg (e :: nil) (hd 0 el2)).
      strongseplift (edge_seg Gsh pg el1 (hd 0 (e :: nil))).
      rewrite sepcon_assoc_logic_equiv.
      unfoldimpmodel.
      erewrite (eseg_eseg Gsh pg el1 (e::nil) (hd 0 el2)).
      rewrite H1. 
      quick_entailer!. 
    + (* vist (dfs_field cvis) (pg.(dst) e) <> 0 *) 
      apply bfalse_valeq_neq in H10.
      simpl in H10.
      (* _e := [_e + 1] *)
      eapply hoare_conseq_pre.
      { sep_apply fold_field_storage.
        asrt_simpl.
        instantiate (1:= LV _vis @ vint ↦ₗ vist (dfs_field cvis) (pg.(dst) e) &&
        (LV _v @ vptr ↦ₗ pg.(dst) e &&
         (LV _e @ vptr ↦ₗ e &&
          (LV _x @ vptr ↦ₗ v_ptr && @graphrep E_Order Gsh ➀ pg (dfs_field cvis))))).
        rewrite <- fold_graph_field.
        quick_entailer!. }
      eapply hoare_conseq_pre.
      erewrite unfold_graph;[refl | eauto ].
      eapply hoare_conseq_pre.
      cbn [vertex_storage]. refl.
      hoare_simpl_pre.
      assert (l = el1 ++ e :: el2).
      { rewrite H1. eapply edge_deterministic;eauto. }
      subst l. clear H11 H12.
      unfold AVertex, field_storage.
      eapply hoare_conseq_pre.
      { rewrite <- edge_seg_list.
        simpl (edge_storage Gsh pg (e :: el2)).
        refl.
      }
      hoare_simpl_pre.
      clear H11 H12.
      forward_simpl.
      Intros v'. 
      hoareasrt_simpl.
      Intros.
      clear v' H11.
      Exists (el1 ++ e ::nil) el2 cvis vis.
      quick_entailer!.
      2: { intros.
           apply in_app_or in H11.
           destruct H11.
           apply Hel1. auto.
           simpl in H11. destruct H11;[ | contradiction].
           subst e0.
           apply H2. auto. }
      2: { rewrite <- H1. rewrite <- app_assoc. simpl. auto.  }
      sep_apply (fold_edge_node Gsh e (pg.(dst) e) (hd 0 el2)).
      asrt_simpl.
      sep_apply singleton_eseg;auto.
      asrt_simpl.
      replace ((hd 0 (e :: el2))) with (hd 0 (e::nil)) by (cbn;auto).
      strongseplift (edge_seg Gsh pg (e :: nil) (hd 0 el2)).
      strongseplift (edge_seg Gsh pg el1 (hd 0 (e :: nil))).
      rewrite sepcon_assoc_logic_equiv.
      unfoldimpmodel.
      erewrite (eseg_eseg Gsh pg el1 (e::nil) (hd 0 el2)).
      rewrite H1. 
      quick_entailer!.
  - clear vis cvis H1 H2 H3.
    Intros el1 el2 cvis vis.
    andp_lift (Abfalse <{ _e != ENull }>).
    eapply derivable1_trans.
    { eapply Abfalse_derive_bfalse. symbolic_execution. }
    unfoldimpmodel.
    Intros.
    apply bfalse_valneq_eq in H8.
    destruct el2.
    + (* el2 = nil *)
      Exists vis cvis.
      rewrite app_nil_r in H1.
      subst el1. 
      quick_entailer!.
      simpl (edge_storage Gsh pg nil).
      simpl ((hd 0 nil)).
      sep_apply edgeseg_zero.
      asrt_simpl.
      sep_apply fold_field_storage.
      asrt_simpl.
      rewrite <- fold_graph_field';eauto.
      quick_entailer!.
      (* abs step *)
      rewrite (repeat_break_unfold _ _ ) in H6.
      unfold body_DFS in H6 at 1.
      prog_nf in H6.
      safe_choice_r H6.
      prog_nf in H6. apply Exec_testst_bind in H6.
      2: { intros st [? ?] v ?.
           rewrite H1.
           destruct H10.
           inversion H10. subst v. 
           apply H7.
           apply H4.
           unfold out_edges.
           auto. }
      prog_nf in H6. safe_choice_r H6.
      prog_nf in H6. apply Exec_testst_bind in H6.
      2: { intros ? [? ?]. auto. }
      auto.
    + cbn [edge_storage].
      Intros.
      cbn in H8.
      subst z. unfold isvalidptr in H10. lia.
Qed. 

Lemma dfs_rec_triplesat_aux: triple_body_nrm ρ Δ _dfs_rec dfs_rec_spec_aux.
Proof.
  funcproof_init.
  rename v into vis_pre.
  rename z1 into v_ptr.  rename v0 into Gsh. 
  rename l into recstk. rename l0 into uvl. rename v2 into pg. rename z0 into u_ptr.  rename z into ue.
  rename v1 into E_Order. 
  rename v3 into cvis_pre. 
  rename H3 into Hue.  rename H4 into Hedst. rename H5 into H3. 
  (* _x := % _arg1; *)
  forward_simpl.
  (* [_x + 1]:= 1; *)
  (* 取出结点x的信息*)
  pose proof vertex_in_vprop pg H H0 as [vl ?] . clear H. rename H4 into H.
  eapply hoare_conseq_pre.
  erewrite unfold_graph;[refl | eauto ].
  eapply hoare_conseq_pre.
  cbn [vertex_storage]. refl.
  hoare_simpl_pre.
  rename l into el.
  unfold AVertex, field_storage.
  hoare_simpl_pre.
  forward_simpl.
  entailer!.
  (* abs step *)
  unfold DFS in H3.
  eapply highstepbind_derive in H3.
  2: { apply visit_eval. }
  (* _e := [_x]; *)
  forward_simpl.
  eapply hoare_conseq_pre. 
  instantiate (1:= 
  EX el1 el2 cvis_loop vis_loop,
  !! (el1 ++ el2 = el) && 
  !! (vis_func vis_loop cvis_loop) && 
  !! (isvalidptr v_ptr) &&  !! (vis_loop v_ptr) &&
  !! (Exec
       (fun s : state Z =>
        visited s = vis_loop /\ stack s =  u_ptr :: recstk)
       (repeat_break (body_DFS pg) v_ptr) X) && 
  !! (forall e, List.In e el1 -> vis_loop (pg.(dst) e) ) &&
  !! (forall w, vis_pre w -> vis_loop w ) &&
  LV _e @ vptr ↦ₗ hd 0 el2 &&
  (LV _x @ vptr ↦ₗ  v_ptr &&
    PV v_ptr + 1 @ vint ↦ₗ (vist (dfs_field cvis_loop) v_ptr) $ ➀ **
    (PV v_ptr @ vptr ↦ₗ hd 0 el $ Gsh **
    (edge_seg Gsh pg el1 (hd 0 el2) **
    (edge_storage Gsh pg el2 **
      vertex_storage Gsh ➀ pg (dfs_field cvis_loop) vl))))
  ).
  { Exists nil el (cvisupdate v_ptr 1 cvis_pre) (vis_pre ∪ [v_ptr]).
    quick_entailer!.
    cbn [edge_seg].
    simpl (vist (dfs_field (cvisupdate v_ptr 1 cvis_pre))).
    unfold cvisupdate at 1.
    rewrite Z.eqb_refl.
    quick_entailer!.
    erewrite vertex_storage_app_r with (vs1:= (v_ptr :: nil)) (vf_new := (dfs_field (cvisupdate v_ptr 1 cvis_pre))).
    entailer!.
    simpl. auto. 
    { intros. simpl in H6. 
    simpl. unfold cvisupdate. 
    destruct (v' =? v_ptr) eqn:?;auto.
    lia. }
    { intros. sets_unfold. tauto. }
    { sets_unfold. auto. } 
    apply vis_func_update;auto.
  }
  eapply hoare_conseq_post'.
  - eapply hoare_While'.
    { Intros el1 el2 cvis_loop vis_loop.
      symbolic_execution. }
    clear cvis_pre H1 H2 H3 H5. 
    hoare_simpl_pre.
    rename l into el1. rename l0 into el2. 
    rename v0 into vis. rename v into cvis.
    rename H5 into Hvis_v. rename H6 into H5.
    rename H7 into Hel1. rename H8 into Hvis_pre. 
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue.
      symbolic_execution. }
    hoare_simpl_pre.
    destruct el2. 
    { cbn in H6. unfold btrue in H6. contradiction. }
    rename z into e.
    cbn in H6.
    apply btrue_valneq_neq in H6.
    cbn [hd].
    (* _v := [_e]; *)
    cbn [edge_storage]. unfold data_at_t_edge_node.
    hoare_simpl_pre.
    forward_simpl.
    (* _vis := [_v + 1]; *)
    eapply hoare_conseq_pre.
    { instantiate (1:= 
       LV _v @ vptr ↦ₗ pg.(dst) e &&
      (LV _e @ vptr ↦ₗ e &&
      (LV _x @ vptr ↦ₗ v_ptr && @graphrep E_Order Gsh ➀ pg (dfs_field cvis)))).
      sep_apply fold_field_storage.
      asrt_simpl.
      sep_apply (fold_edge_node Gsh e (pg.(dst) e) (hd 0 el2)).
      asrt_simpl.
      sep_apply singleton_eseg.
      asrt_simpl.
      strongseplift (edge_storage Gsh pg el2).
      strongseplift (edge_seg Gsh pg (e :: nil) (hd 0 el2)).
      rewrite sepcon_assoc_logic_equiv.
      unfoldimpmodel.
      rewrite (edge_seg_list Gsh pg (e::nil) el2).
      asrt_simpl.
      simpl (((e :: nil) ++ el2)).
      strongseplift (edge_storage Gsh pg (e :: el2)).
      strongseplift (edge_seg Gsh pg el1 e).
      replace e with (hd 0 (e::el2)) at 1 by (cbn;auto).
      rewrite sepcon_assoc_logic_equiv.
      rewrite (edge_seg_list). unfoldimpmodel.
      rewrite <- H1.
      rewrite <- (fold_graph_field' Gsh ➀ pg (dfs_field cvis) v_ptr vl  (el1 ++ e :: el2)).
      quick_entailer!.
      all : auto.
      rewrite H1. auto.
    }
    eapply hoare_conseq_pre.
    { rewrite unfold_graph;[ | eauto].
      assert (In (pg.(dst) e) (v_ptr :: vl)).
      { apply H. auto. }
      pose proof vertex_storage_valid_pointer  Gsh ➀ pg (dfs_field cvis) (v_ptr :: vl) (pg.(dst) e) H9.
      erewrite (prop_add_left _ _ H10). 
      rewrite fold_graph.
      rewrite unfold_field_storage with (v:= (pg.(dst) e));[ | eauto].
      unfold field_storage.
      refl. 
      auto. }
    hoare_simpl_pre.
    forward_simpl.
    (* If _vis == 0 Then *)
    forward_simpl.
    + (* vist (dfs_field cvis) (pg.(dst) e) == 0 *)
      apply btrue_valeq_iseq in H10.
      simpl in H10.
      (* abs step *)
      rewrite (repeat_break_unfold _ _ ) in H5.
      unfold body_DFS in H5 at 1.
      prog_nf in H5. safe_choice_l H5.
      prog_nf in H5. apply Exec_any_bind with (a:= (pg.(dst) e)) in H5.
      prog_nf in H5. eapply Exec_testst_bind in H5.
      2: { intros st [ ? ?].
        rewrite H11.
        apply H2. auto. }
      prog_nf in H5. eapply Exec_test_bind in H5.
      2: { exists e. 
        assert (In e el). { rewrite <- H1. apply in_cons_app. }
        constructor;auto.
        apply H4. auto.
        apply H4. auto. }
      prog_nf in H5. eapply highstepbind_derive in H5.
      2: apply push_stack_eval.
      prog_nf in H5.
      (* % _arg1 := _v; *)
      forward_simpl.
      (* Call (_dfs_rec) *)
      forward_simpl.
      eapply hoare_Call_frm' with (fspec:= dfs_rec_spec_aux) (w:= (X, pg, vl, E_Order, Gsh, u_ptr :: recstk, pg.(dst) e, v_ptr, e, vis)).
      { cbn;auto. }
      { (* ==> pre*)
        unfold FS_Pre. cbn.
        Exists cvis.
        instantiate (1:= (
        (LV _v @ vptr ↦ₗ pg.(dst) e &&
         (LV _e @ vptr ↦ₗ e &&
          (LV _x @ vptr ↦ₗ v_ptr && emp))))).
        entailer!.
        rewrite <- fold_graph_field with (v:= pg.(dst) e).
        unfold field_storage.
        simpl.
        entailer!.
        { unfold out_edges. 
          assert (In e el). { rewrite <- H1. apply in_cons_app. }
          constructor;auto.
          apply H4. auto.
          apply H4. auto.  }
        apply H2.
        simpl in H10. auto.
      }
      { refl. }
      solve_closedgvars idtac.
      (* after call *)
      simpl (FS_Post dfs_rec_spec_aux
      (X, pg, vl, E_Order, Gsh, u_ptr :: recstk,
      pg.(dst) e, v_ptr, e, vis)).
      rename vis into vis_old. rename cvis into cvis_old.
      clear H5 H10. 
      hoare_simpl_pre.
      rename v into vis. rename v0 into cvis.
      assert (forall e : Z, In e el1 -> vis (pg.(dst) e) ).
      { intros. apply H11. apply Hel1. auto. }
      clear Hel1.
      rename H13 into Hel1. rename H12 into Habs.
      (* _e := [_e + 1] *)
      eapply hoare_conseq_pre.
      erewrite unfold_graph;[refl | eauto ].
      eapply hoare_conseq_pre.
      cbn [vertex_storage]. refl.
      hoare_simpl_pre.
      assert (l = el1 ++ e :: el2).
      { rewrite H1. eapply edge_deterministic;eauto. }
      subst l. clear H12 H13.
      unfold AVertex, field_storage.
      eapply hoare_conseq_pre.
      { rewrite <- edge_seg_list.
        simpl (edge_storage Gsh pg (e :: el2)).
        refl.
      }
      hoare_simpl_pre.
      clear H12 H13.
      forward_simpl.
      Intros v'.
      hoareasrt_simpl.
      Intros.
      clear v' H12.
      Exists (el1 ++ e ::nil) el2 cvis vis.
      quick_entailer!.
      2: { intros.
           apply in_app_or in H12.
           destruct H12.
           apply Hel1. auto.
           simpl in H12. destruct H12;subst;auto. contradiction. }
      2: { rewrite <- H1. rewrite <- app_assoc. simpl. auto.  }
      sep_apply (fold_edge_node Gsh e (pg.(dst) e) (hd 0 el2)).
      asrt_simpl.
      sep_apply singleton_eseg;auto.
      asrt_simpl.
      replace ((hd 0 (e :: el2))) with (hd 0 (e::nil)) by (cbn;auto).
      strongseplift (edge_seg Gsh pg (e :: nil) (hd 0 el2)).
      strongseplift (edge_seg Gsh pg el1 (hd 0 (e :: nil))).
      rewrite sepcon_assoc_logic_equiv.
      unfoldimpmodel.
      erewrite (eseg_eseg Gsh pg el1 (e::nil) (hd 0 el2)).
      rewrite H1. 
      quick_entailer!. 
    + (* vist (dfs_field cvis) (pg.(dst) e) <> 0 *) 
      apply bfalse_valeq_neq in H10.
      simpl in H10.
      (* _e := [_e + 1] *)
      eapply hoare_conseq_pre.
      { sep_apply fold_field_storage.
        asrt_simpl.
        instantiate (1:= LV _vis @ vint ↦ₗ vist (dfs_field cvis) (pg.(dst) e) &&
        (LV _v @ vptr ↦ₗ pg.(dst) e &&
         (LV _e @ vptr ↦ₗ e &&
          (LV _x @ vptr ↦ₗ v_ptr && @graphrep E_Order Gsh ➀ pg (dfs_field cvis))))).
        rewrite <- fold_graph_field.
        quick_entailer!. }
      eapply hoare_conseq_pre.
      erewrite unfold_graph;[refl | eauto ].
      eapply hoare_conseq_pre.
      cbn [vertex_storage]. refl.
      hoare_simpl_pre.
      assert (l = el1 ++ e :: el2).
      { rewrite H1. eapply edge_deterministic;eauto. }
      subst l. clear H11 H12.
      unfold AVertex, field_storage.
      eapply hoare_conseq_pre.
      { rewrite <- edge_seg_list.
        simpl (edge_storage Gsh pg (e :: el2)).
        refl.
      }
      hoare_simpl_pre.
      clear H11 H12.
      forward_simpl.
      Intros v'. 
      hoareasrt_simpl.
      Intros.
      clear v' H11.
      Exists (el1 ++ e ::nil) el2 cvis vis.
      quick_entailer!.
      2: { intros.
           apply in_app_or in H11.
           destruct H11.
           apply Hel1. auto.
           simpl in H11. destruct H11;[ | contradiction].
           subst e0.
           apply H2. auto. }
      2: { rewrite <- H1. rewrite <- app_assoc. simpl. auto.  }
      sep_apply (fold_edge_node Gsh e (pg.(dst) e) (hd 0 el2)).
      asrt_simpl.
      sep_apply singleton_eseg;auto.
      asrt_simpl.
      replace ((hd 0 (e :: el2))) with (hd 0 (e::nil)) by (cbn;auto).
      strongseplift (edge_seg Gsh pg (e :: nil) (hd 0 el2)).
      strongseplift (edge_seg Gsh pg el1 (hd 0 (e :: nil))).
      rewrite sepcon_assoc_logic_equiv.
      unfoldimpmodel.
      erewrite (eseg_eseg Gsh pg el1 (e::nil) (hd 0 el2)).
      rewrite H1. 
      quick_entailer!.
  - clear  cvis_pre H1 H2 H3. 
    Intros el1 el2 cvis vis.
    andp_lift (Abfalse <{ _e != ENull }>).
    eapply derivable1_trans.
    { eapply Abfalse_derive_bfalse. symbolic_execution. }
    unfoldimpmodel.
    rename H9 into Hvis_pre. rename H8 into Hel1.
    Intros.
    apply bfalse_valneq_eq in H8.
    destruct el2.
    + (* el2 = nil *)
      Exists vis cvis.
      rewrite app_nil_r in H1.
      subst el1. 
      quick_entailer!.
      simpl (edge_storage Gsh pg nil).
      simpl ((hd 0 nil)).
      sep_apply edgeseg_zero.
      asrt_simpl.
      sep_apply fold_field_storage.
      asrt_simpl.
      rewrite <- fold_graph_field';eauto.
      quick_entailer!.
      (* abs step *)
      rewrite (repeat_break_unfold _ _ ) in H7.
      unfold body_DFS in H7 at 1.
      prog_nf in H7. safe_choice_r H7.
      prog_nf in H7. apply Exec_testst_bind in H7.
      2: { intros st [? ?] v ?.
           rewrite H1.
           destruct H10.
           inversion H10. subst v. 
           apply Hel1.
           apply H4.
           unfold out_edges.
           auto. }
      prog_nf in H7. safe_choice_l H7.
      prog_nf in H7. eapply highstepbind_derive in H7.
      2: apply pop_stack_eval.
      auto.
    + cbn [edge_storage].
      Intros.
      cbn in H8.
      subst z. unfold isvalidptr in H10. lia.
Qed.

Theorem dfs_rec_triplesat_functional_correctness: triple_body_nrm ρ Δ _dfs_rec dfs_rec_spec_fc.
Proof.
  pose proof dfs_rec_triplesat. 
  unfold triple_body_nrm in *;simpl in *.
  let w := fresh "w" in intros w; destruct_prodtype w;hoare_simpl_pre.
  rename z into x.  rename v into Gsh. rename l into vertexl. 
  rename v0 into E_Order.  rename v1 into pg. 
  pose proof @rh_hoare_vc_safeexec _ _ _ unit ((Z * (Z -> Prop ))%type * (Z -> Z))%type ((Z * (Z -> Prop ))%type * (Z -> Z))%type Δ f_dfs_rec
  (fun '(xv, vis, cvis) => DFS pg xv)
  (fun '(xv, vis, cvis) => GV _arg1 @ vptr ↦ₗ xv && graphrep Gsh ➀ pg (dfs_field cvis))
  (fun '(xv, vis, cvis) s => s.(visited) = vis /\ s.(stack) = nil) 
  (fun '(xv, vis, cvis) _ => graphrep Gsh ➀ pg (dfs_field cvis))
  (fun '(xv, vis, cvis) _ s => s.(visited) = vis /\ s.(stack) = nil) 
  (fun '(xv, vis, cvis)  => pg.(vvalid) xv /\ vis = ∅ /\ vis_func vis cvis) (fun '(xv, vis, cvis) _  => vis_func vis cvis) 
  (fun s => s.(stack) = nil /\ s.(visited) = ∅)
  (fun _ s => (forall u, u ∈ s.(visited) <-> reachable pg x u)) 
  (x, ∅, (fun v => 0)) as Hvc.
  eapply hoare_conseq.
  3: { eapply Hvc.
    { simpl. eapply StateRelHoare.Hoare_forall.
      intros u. eapply DFSProof.ContradictionProof.DFS_visited_reachable. } 
    clear Hvc. 
    intros X. clear x  H1. 
    hoare_simpl_pre. destruct v as ((xv, vis), cvis).
    specialize (H (X, pg, vertexl, E_Order, Gsh, xv)). simpl in H.
    eapply hoare_conseq; [ | | apply H].
    { Exists vis cvis. entailer!. destruct H2 as [? [? ?]]. subst. sets_unfold. auto.  }
    { Intros vis0 cvis0. Exists tt (xv, vis0, cvis0). entailer!. } }
  { clear H Hvc.
    entailer!.
    { unfold vis_func. 
      intros.
      sets_unfold. tauto. } 
    exists (Build_state Z nil ∅).
    simpl.
    splits;auto. }
  { clear H Hvc.
    Intros r v. 
    destruct v as ((xv, vis0), cvis0).
    destruct H as [? [? ?]].
    Exists cvis0.
    entailer!.
    intros u.
    rewrite <- H3.
    destruct H. rewrite H.
    unfold vis_func in H2.
    specialize (H2 u) as [? _].
    rewrite <- H2.
    sets_unfold. tauto.
  }
Qed.

End CGraphDFSProof.