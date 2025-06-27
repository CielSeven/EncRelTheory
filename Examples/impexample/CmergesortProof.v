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
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics ImpHoareTactics slllib. 
From EncRelSeq Require Import callsem basicasrt contexthoare_imp. 
From EncRelSeq.MonadsAsHigh.AbsMonad Require Import  encimpmonad.
Require Import MonadLib.MonadLib.
Import StateRelMonad.
From MonadLib.Examples Require Import mergesort.
From Examples Require Import  Cmergesort.
From SetsClass Require Import SetsClass.
Local Open Scope sets.


Module CMergeSortProof.
Import EnvProgramSem.
Import NormalContextualImp.
Import NormalImpHoareRules.
Import NormalImpHoareTac.
Import CMergeSort.
Import RelImpAbsMonad.



Import ImpRules.
Local Open Scope asrt_scope.
Local Open Scope com_scope.
Import MonadNotation.
Local Open Scope monad.


Definition split_while_spec := {|
  FS_With := ((list Z * list Z) -> unit -> Prop) * addr * addr * addr ;
  FS_Pre := fun '(X, xv, pv, qv) =>
            (EX lx pvv qvv, !! (Exec ATrue (split_rel lx) X) &&
            GV _arg1 @ vptr ↦ₗ xv && GV _arg2 @ vptr ↦ₗ pv && GV _arg3 @ vptr ↦ₗ qv && 
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** vPV qv @ vptr ↦ₗ qvv $ ➀ **
            listrep ➀ xv lx ** listrep ➀ pvv nil ** listrep ➀ qvv nil );
  FS_Post := fun '(X, xv, pv, qv) =>
            (EX lp lq pvv qvv, !! (Exec ATrue (return (lp, lq)) X) &&
            GV _arg1 @ vptr ↦ₗ 0 && GV _arg2 @ vptr ↦ₗ pv && GV _arg3 @ vptr ↦ₗ qv && 
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** vPV qv @ vptr ↦ₗ qvv $ ➀ **
            listrep ➀ pvv lp ** listrep ➀ qvv lq );
|}. 


Definition merge_spec := {|
  FS_With := ((list Z) -> unit -> Prop) ;
  FS_Pre := fun X =>
            (EX lx ly xv yv, !! (Exec ATrue (merge_rel lx ly) X) &&
            GV _arg1 @ vptr ↦ₗ xv && GV _arg2 @ vptr ↦ₗ yv && 
            listrep ➀ xv lx ** listrep ➀ yv ly);
  FS_Post := fun X =>
            (EX lr rv, !! (Exec ATrue (return lr) X) &&
            GV _ret1 @ vptr ↦ₗ rv &&
            listrep ➀ rv lr );
|}. 


Definition mergesort_spec := {|
  FS_With := ((list Z) -> unit -> Prop) ;
  FS_Pre := fun X =>
            (EX lx xv, !! (Exec ATrue (mergesortrec lx) X) &&
            GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
  FS_Post := fun X =>
            (EX lr rv, !! (Exec ATrue (return lr) X) &&
            GV _ret1 @ vptr ↦ₗ rv &&
            listrep ➀ rv lr );
|}.

Definition lengthle_spec := {|
  FS_With := (list Z)  * (addr) * (Z) ;
  FS_Pre := fun '(lx, xv, n) => 
            (GV _arg1 @ vptr ↦ₗ xv && GV _arg4 @ vint ↦ₗ n && listrep ➀ xv lx);
  FS_Post := fun '(lx, xv, n) =>
            (GV _ret1 @ vint ↦ₗ  (if ((Zlength lx) <=? n) then (1) else (0) ) && 
             GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
|}.


Definition inssort_spec := {|
  FS_With := (list Z) ;
  FS_Pre := fun lx => 
            (EX xv, GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
  FS_Post := fun lx =>  (EX lr rv, !! (Permutation lx lr /\ incr lr) &&
             GV _ret1 @ vptr ↦ₗ rv && listrep ➀ rv lr );
|}.

Definition gmergesort_spec := {|
  FS_With := ((list Z) -> unit -> Prop) ;
  FS_Pre := fun X =>
            (EX lx xv,
            !! (Exec ATrue (gmergesortrec lx) X) &&
            GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
  FS_Post := fun X =>
            (EX lr rv, !! (Exec ATrue (return lr) X) &&
            GV _ret1 @ vptr ↦ₗ rv && listrep ➀ rv lr );
|}.


Definition sort_spec_fs := {|
  FS_With := (list Z) ;
  FS_Pre := fun lx =>
            (EX xv,
            GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
  FS_Post := fun lx =>
            (EX lr rv,  !! (Permutation lx lr /\ incr lr) &&
            GV _ret1 @ vptr ↦ₗ rv && listrep ➀ rv lr );
|}.



Definition ρ : program := 
  (_split_while, f_split_while)::
  (_merge, f_merge):: 
  (_merge_sort, f_merge_sort) ::
  (_gmerge_sort, f_gmerge_sort) :: nil.

Definition Δ : funcspecs := 
  (_split_while, split_while_spec):: 
  (_merge, merge_spec):: 
  (_merge_sort, mergesort_spec) :: 
  (_merge_sort, sort_spec_fs) :: 
  (_lengthle, lengthle_spec) :: 
  (_ins_sort, inssort_spec) :: 
  (_gmerge_sort, gmergesort_spec) ::
  (_gmerge_sort, sort_spec_fs) :: nil. 


Ltac hoareasrt_simpl ::= asrt_simpl_aux sll_asrt_simpl.
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

Ltac allocisvalidptr_one v pv :=
  simpl (IterSepcon _); unfoldimpmodel; simpl_pre;
  match goal with 
  | H: v > 0, H0: isvalidptr v |- _ => rename v into pv; clear H;rename H0 into H 
  end.

Definition split_while_spec_aux {B: Type} := {|
  FS_With := ((list Z * list Z) -> MONAD B) * (B -> unit -> Prop)  * addr * addr * addr ;
  FS_Pre := fun '(f, X, xv, pv, qv) =>
            (EX lx, !! (Exec ATrue (bind (split_rel lx) f) X) &&
            GV _arg1 @ vptr ↦ₗ xv && GV _arg2 @ vptr ↦ₗ pv && GV _arg3 @ vptr ↦ₗ qv && 
            vPV pv @ vptr ↦ₗ 0 $ ➀ ** vPV qv @ vptr ↦ₗ 0 $ ➀ **
            listrep ➀ xv lx);
  FS_Post := fun '(f, X, xv, pv, qv) =>
            (EX lp lq pvv qvv, !! (Exec ATrue (f (lp, lq)) X) &&
            GV _arg1 @ vptr ↦ₗ 0 && GV _arg2 @ vptr ↦ₗ pv && GV _arg3 @ vptr ↦ₗ qv && 
            vPV pv @ vptr ↦ₗ pvv $ ➀ ** vPV qv @ vptr ↦ₗ qvv $ ➀ **
            listrep ➀ pvv lp ** listrep ➀ qvv lq );
|}. 

Definition mergesort_spec_aux {B: Type} := {|
  FS_With := ((list Z) -> MONAD B) * (B -> unit -> Prop) ;
  FS_Pre := fun '(f, X) =>
            (EX lx xv, !! (Exec ATrue (bind (mergesortrec lx) f) X) &&
            GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
  FS_Post := fun '(f, X) =>
            (EX lr rv, !! (Exec ATrue (f lr) X) &&
            GV _ret1 @ vptr ↦ₗ rv &&
            listrep ➀ rv lr );
|}. 

Definition gmergesort_spec_aux {B: Type} := {|
  FS_With := ((list Z) -> MONAD B) * (B -> unit -> Prop) ;
  FS_Pre := fun '(f, X) =>
            (EX lx xv, 
            !! (Exec ATrue (bind (gmergesortrec lx) f) X) &&
            GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv lx);
  FS_Post := fun '(f, X) =>
            (EX lr rv, !! (Exec ATrue (f lr) X) &&
            GV _ret1 @ vptr ↦ₗ rv && listrep ➀ rv lr );
|}.



Lemma  split_while_spec_derive_spec_aux {B: Type}:  forall w0 : FS_With (@split_while_spec_aux B),
    FS_Pre split_while_spec_aux w0 |-- EX w, FS_Pre split_while_spec w ** (FS_Post split_while_spec w ₑ-* FS_Post split_while_spec_aux w0).
Proof.
  unfold split_while_spec_aux.
  unfoldfspec.
  intros ((((f & X) & xv) & pv) & qv).
  Intros lx.
  apply Exec_bind in H as [X' [Hpre Hpost]].
  Exists (X', xv, pv, qv).
  Exists lx 0 0.
  simpl (listrep _ _ nil).
  entailer!. 
  unfold wand_env.
  Intros_r l g.
  apply derivable1_wand_sepcon_adjoint;unfoldimpmodel.
  entailer!.
  revert l g.
  apply env_derivable1.
  Intros lp lq pvv qvv.
  Exists lp lq pvv qvv.
  entailer!.
Qed.


Lemma  mergesort_spec_derive_spec_aux {B: Type}:  forall w0 : FS_With (@mergesort_spec_aux B),
    FS_Pre mergesort_spec_aux w0 |-- EX w, FS_Pre mergesort_spec w ** (FS_Post mergesort_spec w ₑ-* FS_Post mergesort_spec_aux w0).
Proof.
  unfold mergesort_spec_aux.
  unfoldfspec.
  intros (f & X) .
  Intros lx xv.
  apply Exec_bind in H as [X' [Hpre Hpost]].
  Exists (X').
  Exists lx xv.
  entailer!.
  unfold wand_env.
  Intros_r l g.
  apply derivable1_wand_sepcon_adjoint;unfoldimpmodel.
  entailer!.
  revert l g.
  apply env_derivable1.
  Intros lr rv.
  Exists lr rv.
  entailer!.
Qed.

Lemma  gmergesort_spec_derive_spec_aux {B: Type}:  forall w0 : FS_With (@gmergesort_spec_aux B),
    FS_Pre gmergesort_spec_aux w0 |-- EX w, FS_Pre gmergesort_spec w ** (FS_Post gmergesort_spec w ₑ-* FS_Post gmergesort_spec_aux w0).
Proof.
  unfold gmergesort_spec_aux.
  unfoldfspec.
  intros (f & X) .
  Intros lx xv.
  apply Exec_bind in H as [X' [Hpre Hpost]].
  Exists (X').
  Exists lx xv.
  entailer!.
  unfold wand_env.
  Intros_r l g.
  apply derivable1_wand_sepcon_adjoint;unfoldimpmodel.
  entailer!.
  revert l g.
  apply env_derivable1.
  Intros lr rv.
  Exists lr rv.
  entailer!.
Qed.

Lemma split_triplesat: triple_body_nrm ρ Δ _split_while split_while_spec.
Proof.
  funcproof_init.
  rename z1 into xv. rename z0 into pv. rename z into qv. rename v into pvv. rename v0 into qvv. rename l into lx.
  (* _x := % _arg1; *)
  forward_simpl.
  (* _p := % _arg2; *)
  forward_simpl.
  (* _p := % _arg2; *)
  forward_simpl.
  (* While _x != 0 *)
  eapply hoare_conseq_pre.
  { instantiate (1:= EX l l0 l1 xv  pvv qvv, 
                  !! (Exec ATrue (split_rec_rel l l0 l1) X) &&
                  LV _x @ vptr ↦ₗ xv && LV _p @ vptr ↦ₗ pv && LV _q @ vptr ↦ₗ qv && 
                  vPV pv @ vptr ↦ₗ pvv $ ➀ ** vPV qv @ vptr ↦ₗ qvv $ ➀ **
                  listrep ➀ xv l ** listrep ➀ pvv l0 ** listrep ➀ qvv l1 ).
  Exists lx (@nil Z) (@nil Z) xv.
  Exists pvv qvv.
  simpl (listrep _ _ nil).  
  quick_entailer!. }
  clear H H2 H3 xv lx pvv qvv. 
  eapply hoare_Seq.
  eapply hoare_While';[symbolic_execution | ].
  + simpl_pre.
    rename v into xv. rename v0 into pvv. rename v1 into qvv.
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue.
      symbolic_execution. }
    simpl_pre.
    apply btrue_valneq_neq in H4.
    destruct l.
    { simpl.
      simpl_pre.
      subst.
      contradiction. }
    (* _t := [_x + 1]; *)
    simpl (listrep ➀ xv (z :: l)).
    simpl_pre.
    forward_simpl.
    (* _pv := [_p]; *)
    forward_simpl.
    (* [_x + 1]:= _pv; *)
    forward_simpl.
    entailer!.
    (* [_p]:= _x; *)
    forward_simpl.
    entailer!.
    (* _x := _t; *)
    forward_simpl.
    apply split_rel_eval_xnotnil in H.
    (* If _x != 0 Then _t := [_x + 1]; _qv := [_q]; [_x + 1]:= _qv; [_q]:= _x; _x := _t Else Skip End *)
    forward_simpl.
    - (* x != 0 *)
      apply btrue_valneq_neq in H8.
      destruct l.
      { simpl.
        simpl_pre.
        subst.
        contradiction. }
      simpl  (listrep ➀ v (z0 :: l)).
      simpl_pre.
      (* _t := [_x + 1]; *)
      forward_simpl.
      (* _qv := [_q]; *)
      forward_simpl.
      (* [_x + 1]:= _qv; *)
      forward_simpl.
      entailer!.
      (* [_q]:= _x; *)
      forward_simpl.
      entailer!.
      (* _x := _t *)
      forward_simpl.
      Intros v'.
      normalize.
      pureIntros.
      subst v'.
      Exists l (z::l0) (z0::l1) v0.
      Exists xv v.
      simpl (listrep ➀ _ (_ :: _)).
      Exists pvv qvv.
      quick_entailer!. 
      (* abs step *)
      erewrite (program_para_equiv (split_rec_rel_unfold)) in H.
      unfold split_rec_rel_f in H.
      prog_nf in H.
      rewrite bind_2_reversepair_equiv_Id in H.
      rewrite bind_ret_right in H.
      exact H.
    - (* x = 0 *)
      apply bfalse_valneq_eq in H8.
      subst v.
      forward_simpl.
      rewrite listrep_nil.
      Exists (@nil Z) (z::l0) l1 0. 
      Exists xv qvv.
      pureIntros.
      subst l.
      simpl (listrep ➀ _ (_ :: _)).
      Exists pvv.
      quick_entailer!.
      (* abs step *)
      unfold split_rec_rel.
      rewrite (split_rec_rel_unfold (nil, z::l0, l1)).
      rewrite (split_rec_rel_unfold (nil, l1, z::l0)) in H.
      simpl in H. simpl.
      prog_nf in H.
      unfold reversepair in H.
      auto.
  + hoare_simpl_pre.
    eapply hoare_conseq_pre.
    { eapply Abfalse_derive_bfalse. symbolic_execution. }
    hoare_simpl_pre.
    apply bfalse_valneq_eq in H4.
    subst v.
    (* % _arg1 := _x; *)
    forward_simpl.
    (* % _arg2 := _p; *)
    forward_simpl.
    (* % _arg3 := _q *)
    forward_simpl.
    Intros v'. normalize.
    clear v'.
    Exists l0 l1 v0 v1.
    rewrite listrep_nil.
    cbn [listrep].
    quick_entailer!.
    (* abs step *)
    subst l.
    eapply highstependret_derive with (P':= fun _ =>  ATrue);eauto.
    eapply split_rec_rel_eval_xnil.
Qed.



Lemma merge_triplesat: triple_body_nrm ρ Δ _merge merge_spec.
Proof.
  funcproof_init.
  rename l into lx. rename l0 into ly.
  rename v into xv. rename v0 into yv.
  (* _x := % _arg1; *)
  forward_simpl.
  (* _y := % _arg2; *)
  forward_simpl.
  (* Alloc (_r, 1); *)
  forward_simpl.
  allocisvalidptr_one v rv.
  (* _t:= _r; *)
  forward_simpl.
  (* _break := 0; *)
  forward_simpl.
  (* While _break == 0 *)
  eapply hoare_conseq_pre.
  { instantiate (1:= EX (bf:Z) (l1 l2 l3: list Z) (xv yv tv ttv: addr), 
                  !! Exec ATrue (merge_from_mid_rel l1 l2 l3) X && 
                  !! isvalidptr tv && 
                  LV _break @ vint ↦ₗ bf && !! (bf <> 0 -> l1 = nil /\ ttv = yv \/ l2 = nil /\ ttv = xv) &&
                  LV _x @ vptr ↦ₗ xv && LV _y @ vptr ↦ₗ yv && 
                  LV _t @ vptr ↦ₗ tv &&  LV _r @ vptr ↦ₗ rv &&
                  listrep ➀ xv l1 ** listrep ➀ yv l2 **
                  sllbseg ➀ rv tv l3 ** PV tv @ vptr ↦ₗ ttv $ ➀).
    Exists (0 ) lx ly (@nil Z) xv.
    Exists yv rv 0.
    cbn [sllbseg].
    quick_entailer!. }
  forward_simpl.
  - clear lx ly xv yv H. 
    eapply hoare_While';[symbolic_execution | ].
    simpl_pre.
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue. symbolic_execution. }   
    simpl_pre.
    eapply btrue_valeq_iseq in H3.
    subst v.
    (*If _x == 0 Then [_t]:= _y; _break := 1 *)
    forward_simpl.
    + (* _x == 0*)
      apply btrue_valeq_iseq in H3.
      subst v0.
      (* [_t]:= _y; *)
      forward_simpl.
      entailer!.
      (* _break := 1 *)
      forward_simpl.
      Intros v'.
      hoareasrt_simpl.
      Intros.
      subst v'.
      Exists (1) (@nil Z) l0 l1.
      Exists 0 v1 v2 v1.
      rewrite listrep_nil.
      quick_entailer!.
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
        entailer!.
        (* _break := 1 *)
        forward_simpl.
        Intros v'.
        hoareasrt_simpl.
        Intros.
        subst v'.
        Exists (1) l (@nil Z) l1.
        Exists v0 0 v2 v0.
        rewrite listrep_nil.
        quick_entailer!.
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
          entailer!.
          (* _t := _x + 1; *)
          forward_simpl.
          (* _x := [_x + 1] *)
          forward_simpl.
          Intros v'.
          hoareasrt_simpl.
          Intros. subst v'.
          Exists 0 l (z0 :: l0) (l1 ++ z :: nil).
          Exists v v1 (v0 + 1) v.
          simpl (listrep _ _ (_ :: _ )).
          Exists v4.
          quick_entailer!.
          { erewrite <- sllbseg_sllbseg with (y:= v2).
            simpl (sllbseg _ _ _ (_ :: _)).
            Exists v0.
            quick_entailer!. }
          (* abs step *)
          unfold merge_from_mid_rel in *.
          rewrite (repeat_break_unfold _ _) in H.
          prove_by_one_abs_step (by_continue (l, z0::l0, l1 ++ z:: nil)).
          unfold merge_body.
          abs_choice_left.
          abs_test_step;[ int auto |
          abs_ret_step].
        ++ (* _a >= _b *)
           apply bfalse_vallt_lt in H13.
          (* [_t]:= _x; *)
          forward_simpl.
          entailer!.
          (* _t := _x + 1; *)
          forward_simpl.
          (* _x := [_x + 1] *)
          forward_simpl.
          Intros v'.
          hoareasrt_simpl.
          Intros. subst v'.
          Exists 0 (z:: l) l0 (l1 ++ z0 :: nil).
          Exists v0 v4 (v1 + 1) v4.
          simpl (listrep _ _ (_ :: _ )).
          Exists v.
          quick_entailer!.
          { erewrite <- sllbseg_sllbseg with (y:= v2).
            simpl (sllbseg _ _ _ (_ :: _)).
            Exists v1.
            quick_entailer!. }
          (* abs step *)
          unfold merge_from_mid_rel in *.
          rewrite (repeat_break_unfold _ _) in H.
          prove_by_one_abs_step (by_continue (z::l, l0, l1 ++ z0:: nil)).
          unfold merge_body.
          abs_choice_right.
          abs_test_step;[ int auto |
          abs_ret_step].
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
      normalize. clear v'.
      Exists (l1 ++ l0) v4.
      rewrite listrep_app.
      Exists v1.
      quick_entailer!.
      (* abs step *)
      unfold merge_from_mid_rel in H1.
      rewrite (repeat_break_unfold _ _) in H1.
      prove_by_one_abs_step (by_break (l1 ++ l0)).
      unfold merge_body.
      abs_ret_step.
    + subst. 
      simpl (listrep _ _ nil).
      simpl_pre.
      subst.
      forward_simpl.
      Intros v'. 
      normalize. clear v'.
      Exists (l1 ++ l) v4.
      rewrite listrep_app.
      Exists v0.
      entailer!.
      (* abs step *)
      unfold merge_from_mid_rel in H1.
      rewrite (repeat_break_unfold _ _) in H1.
      prove_by_one_abs_step (by_break (l1 ++ l)).
      unfold merge_body.
      destruct l;abs_ret_step.
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
  entailer!.
  (* Alloc (_q, 1); *)
  forward_simpl.
  allocisvalidptr_one v qv.
  (* [_q]:= 0; *)
  forward_simpl.
  entailer!.
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
    normalize. clear v'.
    Exists lp ppv.
    simpl (listrep _ _ nil). 
    quick_entailer!.
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
        unfold mergesortrec_loc0 in H2.
        unfold mergesortrec_loc1.
        destruct lq; congruence.  }
      { unfold mergesort_spec_aux. cbn.
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
  { eapply hoare_Call_frm' with (fspec := lengthle_spec) (w:= (lx,xv, 8)).
  { cbn ;tauto. }
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
    instantiate (1:= LV _n @ vint ↦ₗ (if Zlength lx <=? 8
    then 1 else 0) && (LV _x @ vptr ↦ₗ xv && emp)).
    entailer!. }
    { unfoldfspec. Intros lr rv. Exists lr rv. entailer!. 
      (* abs step *)
      rewrite (gmergesortrec_unfold lx) in H.
      unfold gmergesortrec_f in H. 
      apply Exec_choice_left in H.
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
  entailer!.
  (* Alloc (_q, 1); *)
  forward_simpl.
  allocisvalidptr_one v qv.
  (* [_q]:= 0; *)
  forward_simpl.
  entailer!.
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
    apply Exec_choice_right in H.
    unfold seq in H.
    rewrite (split_rel_refine_ext_split lx).
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
  clear ppv lp H4. rename v into ppv. rename l into lp_sorted.
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

Theorem merge_sort_triplesat_fc: triple_body_nrm ρ Δ _merge_sort sort_spec_fs.
Proof.
  pose proof merge_sort_triplesat. 
  unfold triple_body_nrm in *;simpl in *.
  let w := fresh "w" in intros w; destruct_prodtype w;hoare_simpl_pre.
  rename v into xv.
  pose proof rh_hoare_vc_safeexec Δ f_merge_sort
  (fun '(l, xv) => mergesortrec l)
  (fun '(l, xv) => GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv l)
  (fun _ => ATrue) 
  (fun xv lr => GV _ret1 @ vptr ↦ₗ xv && listrep ➀ xv lr)
  (fun _ _  => ATrue) (fun '(l, xv) => True) (fun _ _ => True) 
  (fun _ => True)
  (fun l0 _ => Permutation l l0 /\ incr l0) (l, xv)
  (ltac:(apply functional_correctness_mergesort)) as Hvc.
  eapply hoare_conseq.
  3: { eapply Hvc.
    clear Hvc. 
    intros X. clear l xv.   
    specialize (H X).
    hoare_simpl_pre. destruct v as (l, xv).
    eapply hoare_conseq; [ | | apply H].
    { Exists l xv. quick_entailer!. }
    { Intros l0 xv0. Exists l0 xv0. quick_entailer!. } }
  { clear H Hvc.
    quick_entailer!.
    exists tt.
    unfold ATrue.
    splits;auto. }
  { clear H Hvc.
    Intros lr v.
    destruct H as [? [? ?]].
    Exists lr v.
    quick_entailer!.
  }
Qed.

Theorem gmerge_sort_triplesat_functional_correctness: triple_body_nrm ρ Δ _gmerge_sort sort_spec_fs.
Proof.
  pose proof gmerge_sort_triplesat. 
  unfold triple_body_nrm in *;simpl in *.
  let w := fresh "w" in intros w; destruct_prodtype w;hoare_simpl_pre.
  rename v into xv.
  pose proof rh_hoare_vc_safeexec Δ f_gmerge_sort
  (fun '(l, xv) => gmergesortrec l)
  (fun '(l, xv) => GV _arg1 @ vptr ↦ₗ xv && listrep ➀ xv l)
  (fun _ => ATrue) 
  (fun xv lr => GV _ret1 @ vptr ↦ₗ xv && listrep ➀ xv lr)
  (fun _ _  => ATrue) (fun '(l, xv) => True) (fun _ _ => True) 
  (fun _ => True)
  (fun l0 _ => Permutation l l0 /\ incr l0) (l, xv)
  (ltac:(apply functional_correctness_gmergesort)) as Hvc.
  eapply hoare_conseq.
  3: { eapply Hvc.
    clear Hvc. 
    intros X. clear l xv.   
    specialize (H X).
    hoare_simpl_pre. destruct v as (l, xv).
    eapply hoare_conseq; [ | | apply H].
    { Exists l xv. quick_entailer!. }
    { Intros l0 xv0. Exists l0 xv0. quick_entailer!. } }
  { clear H Hvc.
    quick_entailer!.
    exists tt.
    unfold ATrue.
    splits;auto. }
  { clear H Hvc.
    Intros lr v.
    destruct H as [? [? ?]].
    Exists lr v.
    quick_entailer!.
  }
Qed.

End CMergeSortProof.