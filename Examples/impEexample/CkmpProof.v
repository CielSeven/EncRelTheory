Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Permutation.

From AUXLib Require Import Feq Idents List_lemma VMap int_auto ListLib.
From FP Require Import PartialOrder_Setoid BourbakiWitt. 
From compcert.lib Require Import Integers.
From LangLib.ImpP Require Import PermissionModel Mem mem_lib Imp Assertion ImpTactics ImpEHoareTactics slllib ArrayLib. 
From EncRelSeq Require Import callsem basicasrt contexthoare_imp. 
From EncRelSeq.MonadsAsHigh.AbsMonadE Require Import encimpmonadE.
Require Import MonadLib.MonadErr.StateRelMonadErr.
From MonadLib.Examples Require Import kmp.
From Examples Require Import Ckmp.
From SetsClass Require Import SetsClass.
Local Open Scope sets.
Module CKMPProof.

Import EnvProgramSem.
Import ContextualJoinStateGlobalEnv.
Import PracticalImpHoareRules.
Import PracticalImpHoareTac.
Import PracticalImpHoareArrayRules.
Import CKMP.
Import RelJoinStateGlobalEnvAbsMonad.


Import ImpRules.
Local Open Scope asrt_scope.
Local Open Scope com_scope.
Import MonadNotation.
Local Open Scope monad.


Definition inner_spec := {|
  FS_With := (Z -> unit -> Prop) * Z * Z * list Z * list Z * addr * addr * Z * Z ;
  FS_Pre := fun '(X, n, m, strl, nextl, str, vnext, ch, j) =>
            (!! (safeExec ATrue (inner_loop 0 strl nextl ch j) X) &&
             !! (m <= n) && !! (n < Int64.max_signed) && 
             GV _arg1 @ vptr ↦ₗ str && GV _arg2 @ vptr ↦ₗ vnext && 
             GV _arg3 @ vint ↦ₗ ch && GV _arg4 @ vint ↦ₗ j &&
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext m nextl );
  FS_Post := fun '(X, n, m, strl, nextl, str, vnext, ch, j) =>
            (EX rv, !! (safeExec ATrue (return rv) X) && !! (0 <= rv) && !! (rv < m + 1) &&
             GV _ret1 @ vint ↦ₗ rv && 
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext m nextl );
|}.



Definition constr_spec := {|
  FS_With := (list Z -> unit -> Prop) * Z  * list Z * addr * addr  ;
  FS_Pre := fun '(X, n, strl, str, vnext) =>
            (EX nextl, !! (safeExec ATrue (constr_loop 0 strl) X) &&
            !! (0 < n) && !! (n < Int64.max_signed) && 
             GV _arg1 @ vptr ↦ₗ str && GV _arg2 @ vptr ↦ₗ vnext && GV _arg5 @ vint ↦ₗ n && 
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext n nextl );
  FS_Post := fun '(X, n, strl, str, vnext) =>
            (EX nextl, !! (safeExec ATrue (return nextl) X) && 
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext n nextl );
|}. 


Definition constr_spec_fc := {|
  FS_With :=  Z  * list Z * addr * addr  ;
  FS_Pre := fun '(n, strl, str, vnext) =>
            (EX nextl, 
            !! (0 < n) && !! (n < Int64.max_signed) && 
             GV _arg1 @ vptr ↦ₗ str && GV _arg2 @ vptr ↦ₗ vnext && GV _arg5 @ vint ↦ₗ n && 
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext n nextl );
  FS_Post := fun '(n, strl, str, vnext) =>
            (EX nextl, !! (nextl is_prefix_func_of strl) && 
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext n nextl );
|}. 



Definition ρ : program := 
  (_inner, f_inner)::
  (_constr, f_constr):: nil.

Definition Δ : funcspecs := 
  (_inner, inner_spec)::
  (_constr, constr_spec):: 
  (_constr, constr_spec_fc)::nil. 


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
  | @MonadErrBasic.program _ _ => let m := fresh "m" in destruct w as [w m]
  | _ -> ?C =>  destruct_arrow_aux w C 
  end.

Ltac renmae_arrow_type w A ::=
  match A with 
  | Prop => let X := fresh "X" in rename w into X
  | @MonadErrBasic.program _ _ => let m := fresh "m" in rename w into m
  | _ -> ?C =>  renmae_arrow_type w C
  end.

Ltac allocisvalidptr_one v pv :=
  simpl (IterSepcon _); unfoldimpmodel; simpl_pre;
  match goal with 
  | H: v > 0, H0: isvalidptr v |- _ => rename v into pv; clear H;rename H0 into H 
  end.


Definition inner_spec_aux {B: Type}:= {|
  FS_With := (Z -> MonadErrBasic.program unit B) * (B -> unit -> Prop) * Z * Z * list Z * list Z * addr * addr * Z * Z ;
  FS_Pre := fun '(f, X, n, m, strl, nextl, str, vnext, ch, j) =>
            (!! (safeExec ATrue (bind (inner_loop 0 strl nextl ch j) f) X) &&
             !! (m <= n) && !! (n < Int64.max_signed) && 
             GV _arg1 @ vptr ↦ₗ str && GV _arg2 @ vptr ↦ₗ vnext && GV _arg3 @ vint ↦ₗ ch && GV _arg4 @ vint ↦ₗ j &&
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext m nextl );
  FS_Post := fun '(f, X, n, m, strl, nextl, str, vnext, ch, j) =>
            (EX rv, !! (safeExec ATrue (f rv) X) && !! (0 <= rv) && !! (rv < m + 1) &&
             GV _ret1 @ vint ↦ₗ rv && 
             store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext m nextl );
|}. 



Lemma  inner_spec_derive_inner_spec_aux {B: Type}:  forall w0 : FS_With (@inner_spec_aux B),
    FS_Pre inner_spec_aux w0 |-- EX w, FS_Pre inner_spec w ** (FS_Post inner_spec w ₑ-* FS_Post inner_spec_aux w0).
Proof.
  unfold inner_spec_aux.
  unfoldfspec.
  intros (((((((((f & X) & n) & m) & strl) & nextl) & str) & vnext) & ch) & j).
  Intros.
  apply safeExec_bind in H as [X' [Hpre Hpost]].
  Exists (X', n, m, strl, nextl, str, vnext, ch, j).
  entailer!.
  unfold wand_env.
  Intros_r l g.
  apply derivable1_wand_sepcon_adjoint;unfoldimpmodel.
  entailer!.
  revert l g.
  apply env_derivable1.
  Intros rv.
  Exists rv.
  entailer!.
Qed.

Definition constr_loop_from {A: Type} (default: A) str i vnext j :=
  '(vnext', j') <- range_iter i (Zlength str) (constr_body default str) (vnext, j);;
  return vnext'.

Definition constr_loop_from_after {A: Type} (default: A) str i vnext :=
  fun j => constr_loop_from default str (i+1) (vnext ++ (j::nil)) j.


Lemma replace_Znth_length {A: Type}:
  forall (l:list A) n a, 
    Zlength (replace_Znth n a l) = Zlength l.
Proof.
  intros l n; unfold replace_Znth. 
  remember (Z.to_nat n) as k; clear Heqk.
  revert k; induction l; intros.
  - destruct k; simpl; easy.
  - destruct k; simpl; repeat rewrite Zlength_cons; auto.
    rewrite IHl; auto.
Qed.


Lemma constr_triplesat: triple_body ρ Δ _constr constr_spec.
Proof.
  funcproof_init.
  rename z into vnext. rename z0 into str. rename l into strl. rename l0 into nextl. rename z1 into n.
  eapply hoare_conseq_pre.
  prop_apply store_char_array_Zlength. reflexivity.
  hoare_simpl_pre.
  eapply hoare_conseq_pre.
  prop_apply store_int_array_Zlength. reflexivity.
  hoare_simpl_pre.
  (* _str := % _arg1;
  _vnext := % _arg2;
  _n := % _arg5; *)
  forward_simpl.
  forward_simpl.
  forward_simpl.
  (* [_vnext + 0]:= 0; *)
  forward_simpl.
  eapply hoare_StoreIntArrayElem with (n:= n ); [ | | symbolic_execution | symbolic_execution | symbolic_execution | idtac .. ]. 
  lia. int auto. 
  strongseplift (store_int_array ➀ vnext n nextl). reflexivity.
  hoare_simpl_pre.
  (* _j := 0;
  _i := 1; *)
  forward_simpl.
  forward_simpl.
  (* While _i < _n *)
  eapply hoare_conseq_pre.
  { instantiate (1:= EX i nextl0 nextl1 j , 
    !! (safeExec ATrue (constr_loop_from 0 strl i nextl0 j) X) &&
    !! (1 <= i <= n) &&
    LV _i @ vint ↦ₗ i && LV _j @ vint ↦ₗ j &&  LV _n @ vint ↦ₗ n && LV _vnext @ vptr ↦ₗ vnext && LV _str @ vptr ↦ₗ str &&
    store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
    store_int_array ➀ vnext i nextl0 ** 
    store_int_array ➀ (vnext + i) (n - i) nextl1).
    Exists 1 (0::nil) (sublist 1 n (replace_Znth 0 0 nextl)) 0.
    quick_entailer!.
    rewrite store_int_array_divide with (m:= 1); try lia.
    quick_entailer!.
    destruct nextl.
    rewrite Zlength_nil in H3. lia.
    unfold replace_Znth, sublist. 
    simpl (skipn (Z.to_nat 0)
    (firstn (Z.to_nat 1) (replace_nth (Z.to_nat 0) 0 (z :: nextl)))).
    entailer!.
    rewrite replace_Znth_length. auto. }
  clear H.
  eapply hoare_conseq_post'.
  eapply hoare_While';[symbolic_execution | ].
  - simpl_pre. rename v into i. rename v0 into j. rename l into nextl0. rename l0 into nextl1.
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue.
      symbolic_execution. }
    simpl_pre.
    apply btrue_vallt_lt in H5. 
    assert (i < n) by (lia).
    clear H5. 
    (* _ch := [_str + _i]; *)
    forward_simpl.
    eapply hoare_LoadCharArrayElem with (n:= n + 1) (pm := ➀) (l:=  (strl ++ 0 :: nil));[ | symbolic_execution | symbolic_execution | ].
    lia.
    entailer!.
    pure_intro;hoare_simpl_pre_clearv.
    (* % _arg1 := _str; % _arg2 := _vnext; % _arg3 := _ch; % _arg4 := _j; *)
    do 4 forward_simpl.
    set (ch := Znth i (strl ++ 0 :: nil) 0 ) in *.
    (* Call (_inner); *)
    forward_simpl.
    eapply hoare_Call_specderive_frm with (fspec := inner_spec) (fspec0 := inner_spec_aux)
    (w0 := (constr_loop_from_after 0 strl i nextl0, X, n, i, strl, nextl0, str, vnext, ch, j )).
    cbn;eauto.
    apply inner_spec_derive_inner_spec_aux.
    { unfold inner_spec_aux. cbn [FS_With FS_Pre FS_Post].
      entailer!.
      (* abs step *)
      unfold constr_loop_from_after.
      unfold constr_loop_from in *.
      unfold_loop H.
      prog_nf in H.
      rewrite Zlength_app, Zlength_cons, Zlength_nil in H2. simpl in H2.
      safe_choice_l H; try lia.
      unfold constr_body at 1 in H.
      prog_nf in H.
      safe_step H.
      subst ch.
      rewrite app_Znth1 by lia.
      prog_nf in H.
      auto. }
    { unfold inner_spec_aux. cbn [FS_With FS_Pre FS_Post].
      asrt_simpl. refl. } 
    hoaresolve_closedgvars. apply closedgvars_store_int_array.
    simpl_pre.
    (* _j := % _ret1; *)
    forward_simpl.
    clear j H.
    rename v into j.
    (* [_vnext + _i]:= _j;  *)
    eapply hoare_conseq_pre.
    prop_apply store_int_array_Zlength. reflexivity.
    hoare_simpl_pre.
    eapply hoare_conseq_pre.
    prop_apply (store_int_array_Zlength ➀ vnext). reflexivity.
    hoare_simpl_pre.
    destruct nextl1 as [ | ? ? ].
    rewrite Zlength_nil in H. lia.
    eapply hoare_conseq_pre.
    { rewrite (store_int_array_divide _  _ (n - i) _ 1);try lia.
    rewrite (sublist_cons1 1) by lia.
    rewrite (sublist_nil nextl1 0) by lia.
    rewrite sublist_cons2 by lia.
    replace (1-1) with 0 by lia.
    rewrite Zlength_cons in H.
    rewrite sublist_self by lia.
    replace (n- i -1) with (n-(i +1)) by lia.
    instantiate (1:= LV _j @ vint ↦ₗ j &&
    (LV _ch @ vint ↦ₗ ch &&
     (LV _i @ vint ↦ₗ i &&
      (LV _n @ vint ↦ₗ n &&
       (LV _vnext @ vptr ↦ₗ vnext &&
        (LV _str @ vptr ↦ₗ str &&
          store_int_array ➀ vnext (i + 1) (nextl0 ++ z::nil) **
          (store_int_array ➀ (vnext + i + 1) (n - (i + 1)) nextl1 **
          (store_char_array ➀ str (n + 1) (strl ++ 0 :: nil) )))))))).
    quick_entailer!.
    rewrite (store_int_array_divide _  _ (i + 1) _ i);try lia.
    2:{ 
    rewrite Zlength_app.
    rewrite H10. 
    rewrite Zlength_cons, Zlength_nil. simpl. auto. }
    rewrite (sublist_split_app_l 0 i); try lia.
    2:{ rewrite <- Zlength_correct; lia. }
    rewrite sublist_self by eauto. entailer!.
    replace (i + 1 - i) with 1 by lia.
    rewrite sublist_split_app_r with (len:=i); [ | auto | lia].
    replace (i-i) with 0 by lia; replace (i+1-i) with 1 by lia.
    rewrite sublist_self by eauto.
    entailer!. }
    forward_simpl.
    eapply hoare_StoreIntArrayElem with (n:= (i + 1));[ | | symbolic_execution | symbolic_execution | symbolic_execution | idtac .. ].
    lia. int auto.
    strongseplift (store_int_array ➀ vnext (i + 1) (nextl0 ++ z :: nil)). reflexivity.
    hoare_simpl_pre.
    replace ((vnext + i + 1)) with (vnext + (i + 1)) by lia.
    (* _i := _i + 1 *)
    forward_simpl.
    Intros v'.
    hoareasrt_simpl.
    Exists (i + 1) (replace_Znth i j (nextl0 ++ z :: nil))
    nextl1 (j).
    rewrite (replace_Znth_app_r i j nextl0) at 2 by lia.
    replace ((i - Zlength nextl0)) with 0 by lia.
    rewrite (replace_Znth_nothing i nextl0 j) by lia.
    replace (replace_Znth 0 j (z :: nil)) with (j :: nil).
    rewrite Int64.signed_repr.
    2: int_auto.
    quick_entailer!.
    unfold replace_Znth. cbn. reflexivity.
  - hoareasrt_simpl.
    Intros i.
    rewrite logic_equiv_andp_comm. unfoldimpmodel.
    erewrite Abfalse_derive_bfalse. 2: symbolic_execution.
    Intros.
    Intros nextl0 nextl1 j.
    apply bfalse_vallt_lt in H.
    assert (i >= n) by (lia).
    replace i with n  in * by lia.
    replace (n-n) with 0 by lia.
    prop_apply (store_int_array_length ➀ (vnext + n) 0).
    Intros.
    destruct nextl1. 2: simpl in H7;lia.
    unfold store_int_array at 1. unfold store_array.
    cbn [store_array_rec].
    Exists nextl0.
    quick_entailer!.
    unfold constr_loop_from in H4.
    unfold_loop H4.
    safe_choice_r H4.
    auto. 
    rewrite Zlength_app, Zlength_cons, Zlength_nil in H2. simpl in H2.
    lia.
Qed.
    
Lemma inner_triplesat: triple_body ρ Δ _inner inner_spec.
Proof.
  funcproof_init.
  rename z into j. rename z0 into ch. rename z1 into vnext.
  rename z2 into str. rename l into nextl. rename l0 into strl.
  rename z3 into m. rename z4 into n. 
  (* _str := % _arg1; *)
  forward_simpl.
  (*_vnext := % _arg2; *)
  forward_simpl.
  (* _ch := % _arg3; *)
  forward_simpl.
  (* _j := % _arg4; *)
  forward_simpl.
  (* _str_j := [_str + _j]; *)
  eapply hoare_conseq_pre.
  prop_apply store_char_array_Zlength. reflexivity.
  hoare_simpl_pre.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in H2. simpl in H2. 
  eapply hoare_conseq_pre.
  prop_apply store_int_array_Zlength. reflexivity.
  hoare_simpl_pre. rename H3 into Hnextl.
  (* abs assert *)
  pose proof H as Habs.
  unfold inner_loop in Habs.
  unfold_loop Habs.
  unfold inner_body at 1 in Habs.
  safe_step Habs. 
  clear Habs.
  forward_simpl.
  eapply hoare_LoadCharArrayElem with (n:= n + 1) (pm := ➀) (l:=  (strl ++ 0 :: nil));[ | symbolic_execution | symbolic_execution | ].
  lia.
  entailer!.
  pure_intro;hoare_simpl_pre_clearv.
  (* While 0 < _j && _str_j != _ch  *)
  eapply hoare_conseq_pre.
  { instantiate (1:= EX j, 
    !! (safeExec ATrue (inner_loop 0 strl nextl ch j) X) &&
    !! ( Znth j (strl ++ 0 :: nil) 0 <= Byte.max_signed /\ Znth j (strl ++ 0 :: nil) 0 >= Byte.min_signed) &&
      LV _str_j  @ vint ↦ₗ  (Znth j (strl ++ 0 :: nil) 0) &&
      LV _j @ vint ↦ₗ j &&  LV _ch @ vint ↦ₗ ch && LV _vnext @ vptr ↦ₗ vnext && LV _str @ vptr ↦ₗ str &&
      store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
      store_int_array ➀ vnext m nextl ).
  Exists j.
  quick_entailer!. }
  clear j H  H3 H4 H5.
  eapply hoare_Seq.
  eapply hoare_While';[symbolic_execution | ].
  + simpl_pre. rename v into j.
    eapply hoare_conseq_pre.
    { eapply Abtrue_derive_btrue.
      symbolic_execution. }
    simpl_pre.
    apply btrue_valand_and in H4 as [? ?].
    apply btrue_vallt_lt in H4. apply btrue_valneq_neq in H5.
    (* _j := [_vnext + (_j - 1)]; *)
    (* abs assert *)
    pose proof H as Habs.
    unfold inner_loop in Habs.
    unfold_loop Habs.
    unfold inner_body at 1 in Habs.
    safe_step Habs.
    clear Habs.
    forward_simpl.
    eapply hoare_LoadIntArrayElem with (n:= m) (pm := ➀) (l:=  nextl);[ | symbolic_execution | symbolic_execution | ].
    { rewrite ! Int64.signed_repr. lia. 
      clear - H4 H7 H2 H1 H0 Hnextl. int auto.  }
    entailer!.
    pure_intro;hoare_simpl_pre_clearv.
    (* _str_j := [_str + _j] *)
    (* abs step *)
    rewrite ! Int64.signed_repr. 
    2: clear - H4 H6 H1 H2;  int auto.
    unfold inner_loop in *.
    unfold_loop H.
    unfold inner_body at 1 in H.
    safe_step H.
    rewrite app_Znth1 in H5 by auto.
    safe_choice_r H.
    safe_choice_r H.
    unfold continue in H.
    prog_nf in H. 
    2: lia.
    (* abs assert *)
    pose proof H as Habs.
    unfold continue in Habs.
    prog_nf in Habs. 
    unfold_loop Habs.
    unfold inner_body at 1 in Habs.
    safe_step Habs. clear Habs.
    eapply hoare_conseq_post'.
    eapply hoare_LoadCharArrayElem with (n:= n + 1) (pm := ➀) (l:=  (strl ++ 0 :: nil));[ | symbolic_execution | symbolic_execution | ].
    lia.
    entailer!.
    Intros v'.
    hoareasrt_simpl.
    Exists ( (Znth (j - 1) nextl 0)).
    quick_entailer!.
  + hoare_simpl_pre. rename v into j.
    eapply hoare_conseq_pre.
    { eapply Abfalse_derive_bfalse. symbolic_execution. }
    hoare_simpl_pre.
    apply bfalse_valand_or in H4.
    (* If _str_j == _ch Then  % _ret1 := _j + 1  Else % _ret1 := 0 End *)
    forward_simpl.
    * apply btrue_valeq_iseq in H5.
      forward_simpl.
      Intros v'.
      hoareasrt_simpl.
      Exists (j + 1).
      unfold inner_loop in H.
      unfold_loop H.
      unfold inner_body at 1 in H.
      safe_step H.
      rewrite app_Znth1 in H5 by lia.
      prog_nf in H.
      safe_choice_l H.
      unfold break in H. prog_nf in H.
      rewrite Int64.signed_repr.
      quick_entailer!.
      clear - H4 H6 H1 H2;  int auto.
    * apply bfalse_valeq_neq in H5.
      destruct H4.
      ** 
        apply bfalse_vallt_lt in H4.
        forward_simpl.
        Intros v'.
        hoareasrt_simpl.
        Exists 0.
        unfold inner_loop in H.
        unfold_loop H.
        unfold inner_body at 1 in H.
        safe_step H.
        assert (j = 0) by lia. 
        rewrite app_Znth1 in H5 by lia.
        safe_choice_r H.
        safe_choice_l H.
        unfold break in H. prog_nf in H.
        subst j.
        quick_entailer!.
      ** 
        apply bfalse_valneq_eq in H4.
        congruence.
Qed. 

Theorem constr_triplesat_functional_correctness: triple_body ρ Δ _constr constr_spec_fc.
Proof.
  pose proof constr_triplesat.
  unfold triple_body in *;simpl in *.
  let w := fresh "w" in intros w; destruct_prodtype w;hoare_simpl_pre.
  rename z into vnext. rename z0 into str. rename l into strl. rename l0 into nextl. rename z1 into n.
  assert (strl = nil \/ strl <> nil) as [ | ] by tauto.
  { eapply hoare_conseq_pre.
    prop_apply store_char_array_Zlength. reflexivity.
    hoare_simpl_pre.
    subst. simpl in H3. rewrite Zlength_cons, Zlength_nil in H3. lia. }
  assert (MonadErrHoare.Hoare (fun _ : unit => True) ((fun _ : list Z => constr_loop 0 strl) nextl)
       (fun (vnext : list Z) (_ : unit) => vnext is_prefix_func_of strl /\ Zlength vnext = Zlength strl)) as Habs.
  {  apply constr_loop_sound. auto. }
  pose proof rh_hoare_vc_safeexec Δ f_constr
  (fun nextl  => (constr_loop 0 strl))
  (fun nextl => GV _arg1 @ vptr ↦ₗ str && GV _arg2 @ vptr ↦ₗ vnext && GV _arg5 @ vint ↦ₗ n && store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
  store_int_array ➀ vnext n nextl)
  (fun _ => ATrue) 
  (fun (x: unit) nextl' => store_char_array ➀ str (n + 1) (strl ++ (0:: nil)) **
             store_int_array ➀ vnext n nextl')
  (fun _ _  => ATrue) (fun _ => (0 < n < Int64.max_signed )) (fun _ _ => True) 
  (fun _ => True)
  (fun vnext _ => vnext is_prefix_func_of strl /\ Zlength vnext = Zlength strl) nextl Habs as Hvc.
  eapply hoare_conseq.
  3: { eapply Hvc.
    clear Hvc. 
    intros X. clear H0 H1 H2 Habs nextl. 
    specialize (H ((((X, n), strl),str), vnext)).
    hoare_simpl_pre.
    eapply hoare_conseq; [ | | apply H].
    { Exists l. quick_entailer!. }
    { Intros l0. Exists l0 tt. entailer!. } }
  { clear H Hvc.
    entailer!.
    exists tt.
    unfold ATrue.
    splits;auto. }
  { clear H Hvc.
    Intros r v.
    destruct H as [? [? ?]].
    Exists r.
    entailer!.
  }
Qed.


End CKMPProof.