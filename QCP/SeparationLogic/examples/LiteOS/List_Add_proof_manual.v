Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From LOS_Verify.VC.code.link Require Import List_Add_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Require Import LOS_Verify.lib.sortlink.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_LOS_ListAdd_return_wit_1 : LOS_ListAdd_return_wit_1.
Proof.
    pre_process.
    intros.
    unfold dllseg_shift.
    Exists node_pre.
    entailer!.
Qed. 

Lemma proof_of_LOS_ListTailInsert_return_wit_1 : LOS_ListTailInsert_return_wit_1.
Proof. 
    pre_process.
    intros.
    unfold store_dll.
    sep_apply(dllseg_shift_concat storeA list_pre list_pstPrev node_pre).
    sep_apply(dllseg_shift_to_dllseg storeA).
    Intros x.
    Exists x node_pre.
    entailer!.
Qed. 


Lemma proof_of_LOS_ListTailInsert_which_implies_wit_1 : LOS_ListTailInsert_which_implies_wit_1.
Proof. 
    pre_process.
    intros.
    unfold store_dll.
    Intros h pt.
    pose proof dllseg_to_dllseg_shift storeA h list list pt.
    sep_apply H.
    Exists pt.
    entailer!.
Qed. 

Lemma proof_of_LOS_ListAdd_derive_high_level_spec_by_low_level_spec : LOS_ListAdd_derive_high_level_spec_by_low_level_spec.
Proof. 
    pre_process.
    Intros un pu.
    Exists A storeA1 a.
    unfold store_dll at 1.
    Intros h pt.
    Exists h un pu.
    sep_apply(dllseg_to_dllseg_shift_rev storeA1).
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    unfold store_dll.
    sep_apply(dllseg_shift_to_dllseg_shift_rev storeA1).
    Intros x.
    sep_apply (dllseg_shift_rev_concat storeA1).
    assert(H:(({| data := a; ptr := node_pre |} :: nil) ++ l)=({| data := a; ptr := node_pre |} :: l)) by (auto).
    rewrite H.
    sep_apply (dllseg_shift_rev_to_dllseg storeA1 x list_pre list_pre ).
    Intros py.
    Exists x py.
    entailer!.
Qed. 

