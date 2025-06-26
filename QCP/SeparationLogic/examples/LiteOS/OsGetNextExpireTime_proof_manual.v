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
From LOS_Verify.VC.code.link Require Import OsGetNextExpireTime_goal.
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


Lemma proof_of_OsGetNextExpireTime_return_wit_1 : OsGetNextExpireTime_return_wit_1.
Proof. 
    unfold OsGetNextExpireTime_return_wit_1.
    pre_process.
    intros.
    entailer!.
    rewrite H1 in H.
    rewrite H0 in H.
    subst retval retval_2.
    unfold getminExpireTime.
    intros.
    remember (getFirstNodeExpireTime l1 startTime_pre tickPrecision_pre) as x.
    remember (getFirstNodeExpireTime l2 startTime_pre tickPrecision_pre) as y.
    assert (H_ltb : (x <? y)%Z = true) by (apply Z.ltb_lt; exact H).
    rewrite H_ltb.
    lia.
Qed. 

Lemma proof_of_OsGetNextExpireTime_return_wit_2 : OsGetNextExpireTime_return_wit_2.
Proof. 
    unfold OsGetNextExpireTime_return_wit_1.
    pre_process.
    intros.
    entailer!.
    rewrite H1 in H.
    rewrite H0 in H.
    subst retval retval_2.
    unfold getminExpireTime.
    intros.
    remember (getFirstNodeExpireTime l1 startTime_pre tickPrecision_pre) as x.
    remember (getFirstNodeExpireTime l2 startTime_pre tickPrecision_pre) as y.
    assert (H_le : y <= x) by (apply Z.ge_le; exact H).
    assert (H_ltb : (x <? y)%Z = false) by (apply Z.ltb_ge; exact H_le).
    rewrite H_ltb.
    lia.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec : GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec.
Proof. 
    unfold GetSortLinkNextExpireTime_derive_swmtrSpec_by_highSpec.
    pre_process.
    intros.
    entailer!.
    eapply derivable1s_exp_r.
    Exists (fun (p : addr) (swmtrID : glob_vars_and_defs.SwtmrID) =>
   [|p = &( ((glob_vars_and_defs.g_swtmrCBArray sg) # "SWTMR_CTRL_S" + swmtrID) ->ₛ "stSortList")|] &&
   emp) l.
   unfold store_swtmr_sorted_dll.
   rewrite H.
   csimpl.
   unfold glob_vars_and_defs.SwtmrID.
   entailer!.
   Intros y.
   rewrite H0.
   csimpl.
   entailer!.
   (* rewrite <- derivable1_wand_sepcon_adjoint. 
   Intros retval_2.
   Exists retval_2.
   rewrite H1.
   csimpl.
   entailer!.
   Exists y.
   entailer!.
   rewrite H0.
   csimpl.
   entailer!. *)
Admitted. 

Lemma proof_of_GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec : GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec.
Proof. 
    unfold GetSortLinkNextExpireTime_derive_taskSpec_by_highSpec.
    pre_process.
    intros.
    entailer!.
    eapply derivable1s_exp_r.
    Exists (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
   [|p = &( ((glob_vars_and_defs.g_taskCBArray sg) # "LosTaskCB" + taskID) ->ₛ "sortList")|] &&
   emp) l.
   unfold store_task_sorted_dll.
   rewrite H.
   csimpl.
   unfold glob_vars_and_defs.TaskID.
   entailer!.
   Intros y.
   rewrite H0.
   csimpl.
   entailer!.
   rewrite <- derivable1_wand_sepcon_adjoint. 
   Intros retval_2.
   Exists retval_2.
   rewrite H1.
   csimpl.
   entailer!.
   Exists y.
   entailer!.
   rewrite H0.
   csimpl.
   entailer!.
Qed. 

