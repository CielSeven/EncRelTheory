Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.
Require Import Coq.Logic.Classical_Prop.

From AUXLib Require Import Feq Idents  List_lemma VMap int_auto ListLib.
From compcert.lib Require Import Integers.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics ImpHoareTactics slllib ArrayLib. 
From EncRelSeq Require Import callsem basicasrt contexthoare_imp. 
From EncRelSeq.AbsMonad Require Import  encimpmonad.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From Examples Require Import MergeSort CmergesortArray.


Module CMergeSortProof.
Import EnvProgramSem.
Import NormalContextualImp.
Import NormalImpHoareRules.
Import NormalImpHoareTac.
Import CMergeSort.
Import RelImpAbsMonad.
Import RelImpAbsMonadRules.
Import NormalImpHoareArrayRules.

Import ImpRules.
Local Open Scope asrt_scope.
Local Open Scope com_scope.
Import MonadNotation.
Local Open Scope monad.

Definition merge_spec := {|
  FS_With := ((list Z) -> unit -> Prop) * (int64) * Z * Z * Z;
  FS_Pre := fun '(X, xv, p, q, r) =>
            (EX lx ly, !! (safeExec ATrue (merge_rel lx ly) X) &&
            !! (0 <= p <= q /\ q < r <= Int64.max_signed)%Z &&
            GV _arg1 ↦ₗ xv && GV _arg2 ↦ₗ (Int64.repr p) && 
            GV _arg3 ↦ₗ (Int64.repr q) && GV _arg4 ↦ₗ (Int64.repr r) &&
            store_int_array ➀ (Int64.add xv (Int64.repr p)) (q - p + 1) lx ** 
            store_int_array ➀ (Int64.add xv (Int64.repr (q + 1))) (r - q) ly);
  FS_Post := fun '(X, xv, p, q, r) =>
            (EX lr, !! (safeExec ATrue (return lr) X) &&
            store_int_array ➀ (Int64.add xv (Int64.repr p)) (r - p + 1) lr );
|}. 




Definition ρ : program := 
  (_merge, f_merge):: nil.

Definition Δ : funcspecs := 
  (_merge, merge_spec):: nil. 


Ltac hoareasrt_simpl ::= asrt_simpl_aux array_asrt_simpl.
Ltac hoaresolve_closedgvars := solve_closedgvars idtac. 

Ltac unfoldfspec := 
  repeat progress (match goal with 
  | |- context [FS_Pre ?f] => unfold f; cbn [FS_Post FS_Pre FS_With] in * 
  | |- context [FS_Post ?f] => unfold f; cbn [FS_Post FS_Pre FS_With] in * 
  | H: context [FS_Pre ?f] |- _ =>  unfold f; cbn [FS_Post FS_Pre FS_With] in * 
  | H: context [FS_Post ?f] |- _ =>  unfold f; cbn [FS_Post FS_Pre FS_With] in * 
  end). 

Ltac destruct_arrow_aux w B ::=
  match B with 
  | Prop => let X := fresh "X" in destruct w as [w B]
  | @StateRelBasic.program _ _ => let m := fresh "m" in destruct w as [w m]
  | _ -> ?C =>  destruct_arrow_aux w C 
  end.

Ltac renmae_arrow_type w A ::=
  match A with 
  | Prop => let X := fresh "X" in rename w into X
  | @StateRelBasic.program _ _ => let m := fresh "m" in rename w into m
  | _ -> ?C =>  renmae_arrow_type w C
  end.

Ltac allocisvalidptr_one n pv :=
  replace ((Z.to_nat (Int64.signed (Int64.repr 1)))) with (S O) by int_auto;
  simpl (IterSepcon _); unfoldimpmodel; simpl_pre;
  match goal with 
  | H: (n > 0 )%nat /\ _ |- _ => assert (isvalidptr (Int64.repr (Z.of_nat n)));
                                [clear - H; destruct H; int auto; unfold isvalidptr; int auto | ];
                                clear H; let h := fresh "H" in  remember (Int64.repr (Z.of_nat n)) as pv eqn: h; clear n h
  end.


Lemma itersepcon_intarray : forall n p0,
  IterSepcon (consec_mem p0 n) --||-- store_int_array ➀ (Int64.repr (Z.of_nat p0)) (Z.of_nat n) (repeat 0%Z n).
Proof.
  induction n;intros.
  - cbn.
    eapply logic_equiv_derivable1;split;
    entailer!.
  - unfold IterSepcon.
    cbn [consec_mem fold_right].
    unfold IterSepcon in IHn.
    rewrite IHn. 
    erewrite (store_int_array_divide _ (Int64.repr (Z.of_nat p0))) with (m:=1).
    rewrite Int64.add_unsigned.
Admitted.

Lemma merge_triplesat: triple_body_nrm ρ Δ _merge merge_spec.
Proof.
  funcproof_init.
  rename l into lx. rename l0 into ly.
  rename z1 into p. rename z0 into q. rename z into r.

  (* _x := % _arg1;
  _p := % _arg2;
  _q := % _arg3;
  _r := % _arg4; *)
  forward_simpl.
  forward_simpl.
  forward_simpl.
  forward_simpl.
  (* _n1 := _q - _p + 1;
  _n2 := _r - _q; *)
  forward_simpl.
  forward_simpl.

  (* Alloc (_L, _n1); *)
  replace (Int64.add (Int64.sub (Int64.repr q) (Int64.repr p)) (Int64.repr 1)) with (Int64.repr (q - p + 1)).
  2: { admit. }
  forward_simpl.
  eapply hoare_conseq_pre.
  erewrite Int64.signed_repr.
  2: { clear - H0. destruct H0. int auto. }
  rewrite itersepcon_intarray.
  erewrite Z2Nat.id by lia.
  refl.
  (* Alloc (_M, _n2); *)
  replace (Int64.sub (Int64.repr r) (Int64.repr q) ) with (Int64.repr (r - q)).
  2: { admit. }
  forward_simpl.
  eapply hoare_conseq_pre.
  erewrite Int64.signed_repr.
  2: { clear - H0. int auto. } 
  rewrite itersepcon_intarray.
  erewrite Z2Nat.id by lia.
  refl.
  (* _i := 0;
  _j := 0; *)
  forward_simpl.
  forward_simpl.

  (* While _i < _n1 Do *)
  eapply hoare_conseq_pre.
  { instantiate (1:= EX i l0 l1 l2, 
  !! ( 0 <= i <= q - p + 1) &&
  !! (lx = l0 ++ l2) && !! (Zlength l0 = i) && 
  LV _j ↦ₗ Int64.repr 0 &&
  (LV _i ↦ₗ Int64.repr i &&
   (LV _M ↦ₗ Int64.repr (Z.of_nat v1) &&
    (LV _L ↦ₗ Int64.repr (Z.of_nat v0) &&
     (LV _n2 ↦ₗ Int64.repr (r - q) &&
      (LV _n1 ↦ₗ Int64.repr (q - p + 1) &&
       (LV _r ↦ₗ Int64.repr r &&
        (LV _q ↦ₗ Int64.repr q &&
         (LV _p ↦ₗ Int64.repr p &&
          (LV _x ↦ₗ v &&
           (GV _arg1 ↦ₗ v &&
            (GV _arg2 ↦ₗ Int64.repr p &&
             (GV _arg3 ↦ₗ Int64.repr q &&
              (GV _arg4 ↦ₗ Int64.repr r &&
               store_int_array ➀ (Int64.repr (Z.of_nat v1)) (r - q) (repeat 0 (Z.to_nat (r - q))) **
               (store_int_array ➀ (Int64.repr (Z.of_nat v0)) (q - p + 1) (l0 ++ l1) **
                (store_int_array ➀ (Int64.add v (Int64.repr p)) (q - p + 1) lx ** store_int_array ➀ (Int64.add v (Int64.repr (q + 1))) (r - q) ly)))))))))))))))).
    Exists 0 (@nil Z) (repeat 0 (Z.to_nat (q - p + 1))) lx.
    do 2 rewrite app_nil_l.
    entailer!. }
  forward_simpl.
  - eapply hoare_While';[symbolic_execution | ].
    simpl_pre.
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue. symbolic_execution. }   
    simpl_pre.
    eapply btrue_vallt_lt in H6.
    rename v2 into i.
    assert (0 <= i < q - p + 1 ). { clear - H0 H3 H6.  int auto. }
    (* _t := [_x + (_p + _i)] *)
    forward_simpl.
    eapply hoare_LoadCharArrayElem with (n:= q - p + 1) (pm := ➀) (l:=  (strl ++ 0 :: nil));[ | symbolic_execution | symbolic_execution | ].
    
    forward_simpl.
    rewrite (Int64.add_unsigned (Int64.repr p)).
    do 2 rewrite Int64.unsigned_repr by (clear - H0 H3 H6; int auto).



    (*If _x == 0 Then [_t]:= _y; _break := 1 *)
    forward_simpl.
    + (* _x == 0*)
      apply btrue_valeq_iseq in H3.
      subst v0.
      (* [_t]:= _y; *)
      forward_simpl.
      (* _break := 1 *)
      forward_simpl.
      Intros v'.
      hoareasrt_simpl.
      Intros.
      subst v'.
      Exists (Int64.repr 1) (@nil Z) l0 l1.
      Exists (Int64.repr 0) v1 v2 v1.
      rewrite listrep_nil. unfold Int64.zero.
      entailer!.
      (* abs step *)
      subst l.
      auto.
    + (* _x != 0*)
      apply bfalse_valeq_neq in H3.
      (* If _y == 0 Then .. Else .. *)
      forward_simpl.
      * (* _y == 0 *)
        apply btrue_valeq_iseq in H4.
        subst v1.
        (* [_t] = _x; *)
        forward_simpl.
        (* _break := 1 *)
        forward_simpl.
        Intros v'.
        hoareasrt_simpl.
        Intros.
        subst v'.
        Exists (Int64.repr 1) l (@nil Z) l1.
        Exists v0 (Int64.repr 0) v2 v0.
        rewrite listrep_nil. unfold Int64.zero.
        entailer!.
        (* abs step *)
        subst l0.
        auto.
      * (* _y != 0*)
        apply bfalse_valeq_neq in H4.
        (* _a := [_x]; *)
        eapply hoare_conseq_pre.
        { rewrite listrep_neqnil;[ | auto].
          reflexivity. } 
        simpl_pre.
        eapply hoare_conseq_pre.
        { rewrite (listrep_neqnil ➀ v1) ;[ | auto].
          reflexivity. } 
        simpl_pre.
        destruct l;[contradiction | ].
        destruct l0;[contradiction | ].
        simpl (listrep _ _ (_ :: _)).
        simpl_pre.
        (* _a := [_x]; *)
        forward_simpl.
        (* _b := [_y]; *)
        forward_simpl.
        (* If _a < _b Then .. Else ..  *)
        forward_simpl.
        ++ (* _a < _b *)
          apply btrue_vallt_lt in H13.
          (* [_t]:= _x; *)
          forward_simpl.
          (* _t := _x + 1; *)
          forward_simpl.
          (* _x := [_x + 1] *)
          forward_simpl.
          Intros v'.
          hoareasrt_simpl.
          Intros. subst v'.
          Exists (Int64.repr 0) l (z0 :: l0) (l1 ++ z :: nil).
          Exists v v1 (Int64.add v0 (Int64.repr 1)) v.
          simpl (listrep _ _ (_ :: _ )).
          Exists v4.
          entailer!.
          { erewrite <- sllbseg_sllbseg with (y:= v2).
            simpl (sllbseg _ _ _ (_ :: _)).
            Exists v0.
            entailer!. }
          intros. contradiction.
          (* abs step *)
          unfold merge_from_mid_rel in *.
          rewrite (repeat_break_unfold _ _) in H.
          prove_by_one_abs_step (inl (l, z0::l0, l1 ++ z:: nil)).
          unfold merge_body.
          abs_choice_left.
          abs_test_step;[ int auto |
          abs_return_step].
        ++ (* _a >= _b *)
           apply bfalse_vallt_lt in H13.
          (* [_t]:= _x; *)
          forward_simpl.
          (* _t := _x + 1; *)
          forward_simpl.
          (* _x := [_x + 1] *)
          forward_simpl.
          Intros v'.
          hoareasrt_simpl.
          Intros. subst v'.
          Exists (Int64.repr 0) (z:: l) l0 (l1 ++ z0 :: nil).
          Exists v0 v4 (Int64.add v1 (Int64.repr 1)) v4.
          simpl (listrep _ _ (_ :: _ )).
          Exists v.
          entailer!.
          { erewrite <- sllbseg_sllbseg with (y:= v2).
            simpl (sllbseg _ _ _ (_ :: _)).
            Exists v1.
            entailer!. }
          intros. contradiction.
          (* abs step *)
          unfold merge_from_mid_rel in *.
          rewrite (repeat_break_unfold _ _) in H.
          prove_by_one_abs_step (inl (z::l, l0, l1 ++ z0:: nil)).
          unfold merge_body.
          abs_choice_right.
          abs_test_step;[ int auto |
          abs_return_step].
  - simpl_pre.
    eapply hoare_conseq_pre.
    { eapply Abfalse_derive_bfalse. symbolic_execution. }
    simpl_pre.
    apply bfalse_valeq_neq in H4.
    (* _t := [_r]; *)
    eapply hoare_conseq_pre.
    { sep_apply sllbseg_2_listrep';auto.
      refl. }
    simpl_pre.
    forward_simpl.
    (* Free (_r); *)
    forward_simpl.
    specialize (H3 H4) as [[? ?] | [? ?]].
    + subst.
      simpl (listrep _ _ nil).
      simpl_pre.
      subst.
      (* % _ret1 := _t  *)
      forward_simpl.
      Intros v'. 
      asrt_simpl. clear v'.
      Exists (l1 ++ l0) v4.
      rewrite listrep_app.
      Exists v1.
      entailer!.
      (* abs step *)
      unfold merge_from_mid_rel in H0.
      rewrite (repeat_break_unfold _ _) in H0.
      prove_by_one_abs_step (inr (l1 ++ l0)).
      unfold merge_body.
      abs_return_step.
    + subst. 
      simpl (listrep _ _ nil).
      simpl_pre.
      subst.
      forward_simpl.
      Intros v'. 
      asrt_simpl. clear v'.
      Exists (l1 ++ l) v4.
      rewrite listrep_app.
      Exists v0.
      entailer!.
      (* abs step *)
      unfold merge_from_mid_rel in H0.
      rewrite (repeat_break_unfold _ _) in H0.
      prove_by_one_abs_step (inr (l1 ++ l)).
      unfold merge_body.
      destruct l;abs_return_step.
Qed.


Lemma merge_sort_triplesat: triple_body_nrm ρ Δ _merge_sort mergesort_spec.
Proof.
  funcproof_init.
  rename l into lx. rename v into xv.
  (* _x := % _arg1; *)
  forward_simpl.
  (* Alloc (_p, 1); *)
  forward_simpl.
  allocisvalidptr_one v pv.
  (* [_p]:= 0; *)
  forward_simpl.
  (* Alloc (_q, 1); *)
  forward_simpl.
  allocisvalidptr_one v qv.
  (* [_q]:= 0; *)
  forward_simpl.
  (* % _arg1 := _x;
  % _arg2 := _p;
  % _arg3 := _q; *)
  forward_simpl. 
  forward_simpl.
  forward_simpl.
  (* Call (_split_while); *)
  eapply hoare_Seq.
  { rewrite (mergesortrec_unfold lx) in H.
    clear_LV_pre.
    unfold mergesortrec_f in H.
    eapply hoare_Call_specderive_frm with (fspec := split_while_spec) (fspec0 := split_while_spec_aux)
          (w0 := (mergesortrec_loc0, X, xv, pv, qv )).
    cbn;auto.
    apply split_while_spec_derive_spec_aux.
    unfold split_while_spec_aux. cbn [FS_Post FS_With FS_Pre].
    Exists lx.
    entailer!.
    unfold split_while_spec_aux. cbn [FS_Post FS_With FS_Pre]. asrt_simpl. refl.
    hoaresolve_closedgvars. }
  hoare_simpl_pre.
  rename l into lp. rename l0 into lq. rename v into ppv. rename v0 into qqv. clear H.
  (* _p := % _arg2;
  _q := % _arg3; *)
  forward_simpl.
  forward_simpl.
  clear_var_pre _arg2. clear_var_pre _arg3.
  (* _qv := [_q];
  _pv := [_p]; *)
  forward_simpl.
  forward_simpl.
  (* Free (_p);
  Free (_q); *)
  forward_simpl.
  forward_simpl.
  clear_var_pre _p. clear_var_pre _q.
  (* If _qv == 0 Then % _ret1 := _pv *)
  forward_simpl.
  - (* _qv = 0 *)
    apply btrue_valeq_iseq in H. subst qqv.
    eapply hoare_conseq_pre. rewrite listrep_nil. refl.
    hoare_simpl_pre. subst lq.
    (* % _ret1 := _pv *)
    forward_simpl.
    Intros v'.
    asrt_simpl. clear v'.
    Exists lp ppv.
    simpl (listrep _ _ nil). 
    entailer!.
  - (* _qv != 0 *)
    apply bfalse_valeq_neq in H.
    eapply hoare_conseq_pre. sep_apply (listrep_neqnil ➀ qqv);auto. refl.
    (* % _arg1 := _pv; *)
    forward_simpl.
    (* Call (_merge_sort); *)
    forward_simpl.
    { eapply hoare_Call_specderive_frm with (fspec := mergesort_spec) (fspec0 := mergesort_spec_aux)
      (w0 := (mergesortrec_loc1 lq, X)).
      cbn;eauto.
      apply mergesort_spec_derive_spec_aux.
      { unfold mergesort_spec_aux. cbn.
        Exists lp ppv.
        entailer!.
        (* abs step *)
        unfold mergesortrec_loc0 in H0.
        unfold mergesortrec_loc1.
        destruct lq; congruence.  }
      { unfold mergesort_spec_aux. cbn.
        asrt_simpl. refl. } 
      hoaresolve_closedgvars.
      }
    simpl_pre.
    (* _pv := % _ret1; *)
    forward_simpl. 
    clear ppv lp H0. rename v into ppv. rename l into lp_sorted.
    (* % _arg1 := _qv; *)
    forward_simpl.
    clear_var_pre _ret1.
    (* Call (_merge_sort); *)
    forward_simpl.
    { eapply hoare_Call_specderive_frm with (fspec := mergesort_spec) (fspec0 := mergesort_spec_aux)
      (w0 := (mergesortrec_loc2 lp_sorted, X)).
      cbn;eauto.
      apply mergesort_spec_derive_spec_aux.
      { unfold mergesort_spec_aux. cbn.
        Exists lq qqv.
        entailer!. }
      { unfold mergesort_spec_aux. cbn.
        asrt_simpl. refl. } 
      hoaresolve_closedgvars.
      }
    simpl_pre.
    (* _qv := % _ret1; *)
    forward_simpl.
    clear lq qqv H H5 H6. rename v into qqv. rename l into lq_sorted.
    (* % _arg1 := _pv; % _arg2 := _qv; *)
    forward_simpl. forward_simpl.
    clear_LV_pre. clear_var_pre _ret1.
    (* <{ Call (_merge) }> *)
    eapply hoare_Call_frm' with (fspec:= merge_spec) (w:= X).
    cbn;auto.
    { unfoldfspec.
      Exists lp_sorted lq_sorted ppv qqv. 
      entailer!. }
    { unfoldfspec.
      entailer!.
    }
    hoaresolve_closedgvars.
Qed.


Lemma gmerge_sort_triplesat: triple_body_nrm ρ Δ _gmerge_sort gmergesort_spec.
Proof.
  funcproof_init.
  intros.
  unfold f_gmerge_sort.
  simpl_pre.
  rename l into lx. rename v into xv.
  (* _x := % _arg1; *)
  forward_simpl.
  (* % _arg4 := 8; *)
  forward_simpl.
  (* Call (_lengthle); *)
  forward_simpl.
  { eapply hoare_Call_frm' with (fspec := lengthle_spec) (w:= (lx,xv, Int64.repr 8)).
  { cbn ;auto. }
  { unfoldfspec. entailer!. }
  unfoldfspec. asrt_simpl. refl.
  hoaresolve_closedgvars. }
  (* _n := % _ret1; *)
  forward_simpl.  clear_var_pre _ret1.
  (* If _n == 0 Then Call (_ins_sort) *)
  forward_simpl.
  - (* _n == 1 *)
    apply btrue_valeq_iseq in H0.
    assert (Zlength lx <= 8).
    {  pose proof Zlength_nonneg lx. remember (Zlength lx ).   
       clear - H H0 H1.  int auto. destruct (z <=? 8) eqn:?;[ lia | discriminate].  } 
    (* Call (_ins_sort) *)
    eapply hoare_Call_frm' with (fspec := inssort_spec) (w:= (lx)).
    cbn;tauto.
    { unfoldfspec. Exists xv.
    entailer!.
    instantiate (1:= LV _n ↦ₗ (if Zlength lx <=? Int64.signed (Int64.repr 8)
    then Int64.repr 1 else Int64.repr 0) && (LV _x ↦ₗ xv && emp)).
    entailer!. }
    { unfoldfspec. Intros lr rv. Exists lr rv. entailer!. 
      (* abs step *)
      rewrite (gmergesortrec_unfold lx) in H.
      unfold gmergesortrec_f in H. 
      apply safeExec_choice_left in H.
      revert H; apply (highstependret_derive _ _ _ (fun _ => ATrue)).
      hnf.
      intros ? _; exists tt.
      split; [ | exact I].
      hnf.
      tauto.
    } 
    hoaresolve_closedgvars.
  -  (* ! _n <= 8 *)
  apply bfalse_valeq_neq in H0.
  assert (Zlength lx > 8).
  {  pose proof Zlength_nonneg lx. remember (Zlength lx ).  
     clear - H H0 H1. int auto. destruct (z <=? 8) eqn:?;[ contradiction | lia].  } 
  (* Alloc (_p, 1); *)
  forward_simpl. 
  allocisvalidptr_one v pv.
  (* [_p]:= 0; *)
  forward_simpl.
  (* Alloc (_q, 1); *)
  forward_simpl.
  allocisvalidptr_one v qv.
  (* [_q]:= 0; *)
  forward_simpl.
  (* % _arg1 := _x;
  % _arg2 := _p;
  % _arg3 := _q; *)
  forward_simpl. 
  forward_simpl.
  forward_simpl.
  (* Call (_split_while); *)
  forward_simpl.
  { clear_LV_pre.
    eapply hoare_Call_specderive_frm with (fspec := split_while_spec) (fspec0 := split_while_spec_aux)
          (w0 := (gmergesortrec_loc0, X, xv, pv, qv )).
    cbn;auto.
    apply split_while_spec_derive_spec_aux. 
    { unfold split_while_spec_aux. cbn [FS_Post FS_With FS_Pre].
    Exists lx.
    entailer!. 
    (* abs step *)
    rewrite (gmergesortrec_unfold lx) in H.
    unfold gmergesortrec_f in H.
    unfold gmergesortrec_loc0.
    apply safeExec_choice_right in H.
    unfold seq in H.
    prove_by_one_abs_step tt.
    abs_test_step.
    lia. }
    unfold split_while_spec_aux. cbn [FS_Post FS_With FS_Pre]. asrt_simpl. refl.
    hoaresolve_closedgvars. }
  hoare_simpl_pre.
  rename l into lp. rename l0 into lq. rename v into ppv. rename v0 into qqv. clear H.
  (* _p := % _arg2;
  _q := % _arg3; *)
  forward_simpl.
  forward_simpl.
  clear_var_pre _arg2. clear_var_pre _arg3.
  (* _qv := [_q];
  _pv := [_p]; *)
  forward_simpl.
  forward_simpl.
  (* Free (_p);
  Free (_q); *)
  forward_simpl.
  forward_simpl.
  clear_var_pre _p. clear_var_pre _q. 
  (* % _arg1 := _pv; *)
  forward_simpl.
  (* Call (_gmerge_sort); *)
  forward_simpl.
  { eapply hoare_Call_specderive_frm with (fspec := gmergesort_spec) (fspec0 := gmergesort_spec_aux)
    (w0 := (gmergesortrec_loc1 lq, X)).
    cbn;tauto.
    apply gmergesort_spec_derive_spec_aux.
    { unfold gmergesort_spec_aux. cbn [FS_Pre].
      Exists lp ppv.
      entailer!. }
    { unfold gmergesort_spec_aux. cbn.
      asrt_simpl. refl. } 
    hoaresolve_closedgvars.
    }
  simpl_pre.
  (* _pv := % _ret1; *)
  forward_simpl. 
  clear ppv lp H2. rename v into ppv. rename l into lp_sorted.
  (* % _arg1 := _qv; *)
  forward_simpl.
  clear_var_pre _ret1.
  (* Call (_merge_sort); *)
  eapply hoare_Seq.
  { eapply hoare_Call_specderive_frm with (fspec := gmergesort_spec) (fspec0 := gmergesort_spec_aux)
    (w0 := (fun q2 => merge_rel lp_sorted q2, X)).
    cbn;tauto.
    apply gmergesort_spec_derive_spec_aux.
    { unfold gmergesort_spec_aux. cbn.
      Exists lq qqv.
      entailer!. }
    { unfold gmergesort_spec_aux. cbn.
      asrt_simpl. refl. } 
    hoaresolve_closedgvars.
    }
  simpl_pre.
  (* _qv := % _ret1; *)
  forward_simpl.
  clear lq qqv H. rename v into qqv. rename l into lq_sorted.
  (* % _arg1 := _pv; % _arg2 := _qv; *)
  forward_simpl. forward_simpl. 
  clear_LV_pre. clear_var_pre _ret1.
  (* <{ Call (_merge) }> *)
  eapply hoare_Call_frm' with (fspec:= merge_spec) (w:= X).
  cbn;auto.
  { unfoldfspec.
    Exists lp_sorted lq_sorted ppv qqv. 
    entailer!. }
  { unfoldfspec.
    entailer!.
  }
  hoaresolve_closedgvars.
Qed.

End CMergeSortProof.