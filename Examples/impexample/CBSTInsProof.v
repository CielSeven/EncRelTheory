Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.

From AUXLib Require Import Feq Idents  List_lemma VMap int_auto ListLib.
From compcert.lib Require Import Integers.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics ImpHoareTactics slllib bst_lib. 
From EncRelSeq Require Import callsem basicasrt contexthoare_imp. 
From EncRelSeq.MonadsAsHigh.AbsMonad Require Import  encimpmonad.
Require Import MonadLib.StateRelMonad.StateRelMonad.
From Examples Require Import  CBSTInsert bst.
From SetsClass Require Import SetsClass.
Local Open Scope sets.

Module CBSTInsertProof.
Import EnvProgramSem.
Import NormalContextualImp.
Import NormalImpHoareRules.
Import NormalImpHoareTac.
Import CTree_Insert.
Import RelImpAbsMonad.


Import ImpRules.
Local Open Scope asrt_scope.
Local Open Scope com_scope.
Import MonadNotation.
Local Open Scope monad.


Definition tree_ins_spec := {|
  FS_With := ((tree) -> unit -> Prop) * Z * Z * addr ;
  FS_Pre := fun '(X, kv, vv, pv) =>
            (EX t pvv, !! (safeExec ATrue (insert kv vv t) X) &&
            !! ( Int64.min_signed <= kv <= Int64.max_signed ) &&
            GV _arg1 @ vint ↦ₗ kv && GV _arg2 @ vint ↦ₗ vv && 
            GV _arg3 @ vptr ↦ₗ pv && 
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** store_tree ➀ pvv t);
  FS_Post := fun '(X, kv, vv, pv) =>
            (EX t pvv, !! (safeExec ATrue (return t) X) &&
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** store_tree ➀ pvv t);
|}.

Definition tree_ins_spec_fc := {|
  FS_With := (tree * (Z -> option Value.t) * Z * Z * addr) ;
  FS_Pre := fun '(t, m, kv, vv, pv) =>
            (EX pvv, !! (SearchTree t) && !! (Abs t m) && 
            !! ( Int64.min_signed <= kv <= Int64.max_signed ) &&
            GV _arg1 @ vint ↦ₗ kv && GV _arg2 @ vint ↦ₗ vv && 
            GV _arg3 @ vptr ↦ₗ pv && 
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** store_tree ➀ pvv t);
  FS_Post := fun '(t, m, kv, vv, pv) =>
            (EX rt pvv, !! (SearchTree rt) && !! (Abs rt (Map.insert kv vv m)) && 
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** store_tree ➀ pvv rt);
|}.


Definition ρ : program := 
  (_tree_ins, f_tree_ins):: nil.

Definition Δ : funcspecs := 
  (_tree_ins, tree_ins_spec):: 
  (_tree_ins, tree_ins_spec_fc):: nil. 

Ltac hoareasrt_simpl ::= asrt_simpl_aux bst_asrt_simpl.


Definition tree_rooteq (t : tree) (k : Z) (v : Z ):=
  match t with 
  | empty  => False 
  | make_tree l x v0 r => Z.compare k x = Eq /\ Z.compare v v0 = Eq 
  end.

Lemma insert_triplesat: triple_body_nrm ρ Δ _tree_ins tree_ins_spec.
Proof.
  funcproof_init.
  rename z into p0. rename v0 into p0_ptr. rename v into t0.
  rename z0 into v. rename z1 into k.
  (* _k := % _arg1; *)
  forward_simpl.
  (* _v := % _arg2; *)
  forward_simpl.
  (* _p := % _arg3; *)
  forward_simpl.
  (* _break := 0; *)
  forward_simpl.
  (* While _break != 0 *)
  eapply hoare_conseq_pre with (P':= 
  EX bv p p_ptr t Pt,
  !! (safeExec ATrue (x <- (insert k v t) ;; return (combine_tree Pt x)) X) &&
  !! (bv = 1 ->  tree_rooteq t k v) && 
  !! (isvalidptr p) &&
  LV _break @ vint ↦ₗ bv && 
  (LV _p @ vptr ↦ₗ p &&
  (LV _v @ vint ↦ₗ v &&
    (LV _k @ vint ↦ₗ k &&
        PV p @ vptr ↦ₗ p_ptr $ ➀ **
        store_tree ➀ p_ptr t ** store_ptb ➀ p p0 Pt )))
  ).
  { Exists 0 p0 p0_ptr t0 nil.
    quick_entailer!.
    simpl (store_ptb ➀ p0 p0 nil).
    entailer!.
    simpl (combine_tree nil).
    rewrite  bind_ret_right.
    auto.  }
  clear H t0 p0_ptr. rename H1 into Hvalidptr.
  eapply hoare_conseq_post'.
  - eapply hoare_While'.
    { Intros bv p p_ptr t Pt.
      symbolic_execution. }
    simpl_pre.
    rename v0 into brk. rename v1 into p. rename v2 into p_ptr. rename v3 into t. rename v4 into Pt.
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue.
      symbolic_execution. }
    simpl_pre.
    apply btrue_valneq_neq in H3.
    clear H1.
    (* _q := [_p]; *)
    forward_simpl.
    (* If _q == 0 *)
    forward.
    + apply btrue_valeq_iseq in H1. subst p_ptr.
      destruct t.
      2:{ simpl (store_tree _ _ _ ). 
          simpl_pre. unfold isvalidptr in H4. lia. }
      simpl (store_tree _ _ _ ).
      simpl_pre.  clear H1.
      (* Alloc (_q, tree_type, 4); *)
      forward_simpl.
      replace (Z.to_nat 4) with (4)%nat by lia.
      unfold tree_type.
      simpl (IterSepcon (consec_mem v0 4 (vint :: vint :: vptr :: vptr :: nil))).
      unfoldimpmodel.
      simpl_pre.
      replace (v0 + 1 + 1 + 1)%Z with (v0 + 3)%Z in * by lia.
      replace (v0 + 1 + 1)%Z with (v0 + 2)%Z in * by lia.
      rename v0 into p_ptr.
      (* [_q]:= _k; *)
      forward_simpl. entailer!.
      (* [_q + 1]:= _v; *)
      forward_simpl. entailer!.
      (* [_q + 2]:= ENull; *)
      forward_simpl. entailer!.
      (* [_q + 3]:= ENull; *)
      forward_simpl. entailer!.
      (* [_p]:= _q; *)
      forward_simpl. entailer!.
      (* _break := 1 *)
      forward.
      Intros v'. hoareasrt_simpl. Intros. clear v' H8.
      Exists 1 p p_ptr (make_tree empty k v empty) Pt.
      quick_entailer!.
      simpl (store_tree ➀ p_ptr (make_tree empty k v empty)).
      Exists 0 0.
      quick_entailer!.
      entailer!.
      intros. unfold tree_rooteq.  rewrite !Z.compare_refl. auto.
      erewrite (program_para_equiv (insert_unfold k v)) in *.
      unfold F_insert in *.  rewrite Z.compare_refl in *.
      auto.
    + (* _qkey := [_q]; *)
      apply bfalse_valeq_neq in H1.
      destruct t.
      { simpl (store_tree _ _ _ ). 
        simpl_pre.  lia. }
      simpl (store_tree ➀ p_ptr (make_tree t1 k0 v0 t2)).
      simpl_pre.
      forward_simpl.
      (* If _k < _qkey *)
      forward_simpl.
      (* _p := _q + 2 *)
      ++ forward_simpl.
        Intros v'. hoareasrt_simpl. Intros. clear v' H10.
        Exists brk (p_ptr + 2)%Z v1 t1 (LH k0 v0 t2 :: Pt).
        quick_entailer!.
        simpl (store_ptb ➀ (p_ptr + 2)%Z p0 (LH k0 v0 t2 :: Pt)).
        Exists p_ptr p v2.
        entailer!.
        (* abs step *)
        erewrite (program_para_equiv (insert_unfold k v)) in  H.
        unfold F_insert in H.
        apply btrue_vallt_lt in H9.
        assert (Key.compare k k0  = Lt).
        { apply Key.compare_lt_iff. lia.  }
        rewrite H10 in H.
        prog_nf in H.
        simpl (combine_tree _ _).
        auto.
      ++  forward_simpl.
        +++  (* _p := _q + 3*)
        forward_simpl.
        Intros v'. hoareasrt_simpl. Intros. clear v' H11.
        Exists brk (p_ptr + 3)%Z v2 t2 (RH k0 v0 t1 :: Pt).
        quick_entailer!.
        simpl (store_ptb ➀ (p_ptr + 3)%Z p0 (RH k0 v0 t1 :: Pt)).
        Exists p_ptr p v1.
        quick_entailer!.
        (* abs step *)
        erewrite (program_para_equiv (insert_unfold k v)) in  H.
        unfold F_insert in H.
        apply bfalse_vallt_lt in H9.
        apply btrue_vallt_lt in H10.
        assert (Key.compare k k0  = Gt).
        { apply Key.compare_gt_iff. lia.  }
        rewrite H11 in H.
        prog_nf in H.
        simpl (combine_tree _ _).
        auto.
        +++ (* [_q + 1]:= _v; *)
          forward_simpl. entailer!.
          (* _break := 1 *)
          forward_simpl.
          Intros v'. hoareasrt_simpl. Intros. clear v' H11.
          apply bfalse_vallt_lt in H9.
          apply bfalse_vallt_lt in H10.
          assert (k0 = k) by lia. subst k0.
          Exists 1 p p_ptr (make_tree t1 k v t2) Pt.
          quick_entailer!.
          simpl (store_tree ➀ p_ptr (make_tree t1 k v t2)).
          Exists v1 v2.
          entailer!.
          intros. unfold tree_rooteq. rewrite !Key.compare_refl. auto.
          (* abs step *)
          erewrite (program_para_equiv (insert_unfold k v)) in *.
          unfold F_insert in *.
          rewrite Key.compare_refl in *.
          auto.
  - Intros brk p p_ptr t Pt.
    andp_lift (Abfalse <{ _break != 1 }>).
    eapply derivable1_trans.
    eapply Abfalse_derive_bfalse.
    symbolic_execution.
    unfoldimpmodel.
    Intros.
    apply bfalse_valneq_eq in H3. subst brk. 
    Exists (combine_tree Pt t) .
    do 4 rewrite derivable1_andp_elim2.
    sep_apply (store_ptb_store_tree).
    Intros p_root.
    Exists p_root.
    entailer!.
    destruct t.
    simpl in H1. contradiction.
    simpl in H1. 
    specialize (H1 (ltac:(auto))).
    (* abs step *)
    erewrite (program_para_equiv (insert_unfold k v)) in *.
    unfold F_insert in *.
    destruct H1. 
    apply Z.compare_eq in H1. apply Z.compare_eq in H3.
    subst k0 v0.
    rewrite Key.compare_refl in H.
    rewrite bind_ret_left in H.
    auto.
Qed.


Theorem insert_triplesat_functional_correctness: triple_body_nrm ρ Δ _tree_ins tree_ins_spec_fc.
Proof.
  pose proof insert_triplesat.
  unfold triple_body_nrm in *;simpl in *.
  let w := fresh "w" in intros w; destruct_prodtype w;hoare_simpl_pre.
  rename z1 into kv. rename z0 into vv. rename z into pv.
  rename v0 into tr. rename v into m. rename v1 into pvv.
  pose proof rh_hoare_vc_safeexec Δ f_tree_ins
  (fun '(t, pvv) => insert kv vv t)
  (fun '(t, pvv) => GV _arg1 @ vint ↦ₗ kv && GV _arg2 @ vint ↦ₗ vv &&  GV _arg3 @ vptr ↦ₗ pv &&  vPV pv @ vptr ↦ₗ pvv $ ➀ ** store_tree ➀ pvv t)
  (fun _ => ATrue) 
  (fun pvv t => vPV pv @ vptr ↦ₗ pvv $ ➀ ** store_tree ➀ pvv t)
  (fun _ _  => ATrue) (fun '(t, pvv) => (Int64.min_signed <= kv <= Int64.max_signed )) (fun _ _ => True) 
  (fun _ => SearchTree tr /\ Abs tr m)
  (fun rtr _ => SearchTree rtr /\ Abs rtr (Map.insert kv vv m)) (tr, pvv)
  (ltac:(apply bst_insert_fc)) as Hvc.
  eapply hoare_conseq.
  3: { eapply Hvc.
    clear Hvc. 
    intros X. clear H0 H1 H2 H3 tr pvv. 
    specialize (H (((X, kv), vv),pv)).
    hoare_simpl_pre. destruct v as (tr, pvv).
    eapply hoare_conseq; [ | | apply H].
    { Exists tr pvv. quick_entailer!. }
    { Intros tr0 pvv0. Exists tr0 pvv0. entailer!. } }
  { clear H Hvc.
    quick_entailer!.
    exists tt.
    unfold ATrue.
    splits;auto. }
  { clear H Hvc.
    Intros r v.
    destruct H as [? [? ?]].
    Exists r v.
    entailer!.
  }
Qed.


End CBSTInsertProof.
           



