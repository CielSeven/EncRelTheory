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
From LOS_Verify.VC.code.link Require Import LOS_ListDelete_goal.
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

Lemma proof_of_LOS_ListDelete_return_wit_1 : LOS_ListDelete_return_wit_1.
Proof.
    pre_process.
    unfold dllseg_shift.
    entailer!.
    repeat sep_apply store_ptr_undef_store_ptr.
    cancel.
Qed.

Lemma proof_of_LOS_ListDelete_derive_mid_level_spec_by_low_level_spec : LOS_ListDelete_derive_mid_level_spec_by_low_level_spec.
Proof.
    pre_process.
    unfold store_dll. Intros h pt.
    sep_apply (@dllseg_split A). simpl.
    Intros y py z. subst.
    sep_apply (@dllseg_to_dllseg_shift_rev A).
    sep_apply (@dllseg_to_dllseg_shift A).
    Exists A storeA1 a py z. entailer!. Exists node_pre. entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    sep_apply (@dllseg_shift_to_dllseg A). Intros x.
    sep_apply (@dllseg_shift_rev_to_dllseg A). Intros py0.
    sep_apply (dllseg_concat storeA1 x).
    Exists x py0. entailer!.
Qed.

