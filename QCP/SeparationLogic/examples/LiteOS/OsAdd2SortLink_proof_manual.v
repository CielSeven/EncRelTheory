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
From LOS_Verify.VC.code.link Require Import OsAdd2SortLink_goal.
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

Lemma proof_of_OsAdd2SortLink_partial_solve_wit_2_pure : OsAdd2SortLink_partial_solve_wit_2_pure.
Proof. 
    unfold OsAdd2SortLink_partial_solve_wit_2_pure.
    pre_process.
    intros.
    entailer!.
    assert (unsigned_last_nbits (waitTicks_pre * g) 64 = waitTicks_pre * g).
    pose proof (unsigned_last_nbits_eq (waitTicks_pre * g) 64).
    rewrite H3.
    lia.
    lia.
    rewrite H3.
    assert (unsigned_last_nbits (startTime_pre + waitTicks_pre * g ÷ 100) 64 = startTime_pre + waitTicks_pre * g ÷ 100).
    pose proof (unsigned_last_nbits_eq (startTime_pre + waitTicks_pre * g ÷ 100) 64).
    rewrite H4.
    lia.
    lia.
    rewrite H4.
    lia.
Qed. 

Lemma proof_of_OsAdd2SortLink_which_implies_wit_1 : OsAdd2SortLink_which_implies_wit_1.
Proof.
    unfold OsAdd2SortLink_which_implies_wit_1.
    pre_process.
    intros.
    unfold storesortedLinkTaskNode.
    Intros y.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    entailer!.
Qed. 

Lemma proof_of_OsAdd2SortLink_which_implies_wit_2 : OsAdd2SortLink_which_implies_wit_2.
Proof. 
    unfold OsAdd2SortLink_which_implies_wit_2.
    pre_process.
    intros.
    rewrite H.
    unfold storesortedLinkTaskNode.
    Exists node.
    entailer!.
Qed. 


Lemma proof_of_OsAddNode2SortLink_derive_taskSpec_by_highSpec : OsAddNode2SortLink_derive_taskSpec_by_highSpec.
Proof. 
    unfold OsAddNode2SortLink_derive_taskSpec_by_highSpec.
    pre_process.
    intros.
    Intros un pu.
    csimpl.
    simpl.
    unfold store_task_sorted_dll.
    eapply derivable1s_exp_r.
    Exists a t (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
    [|p = &( ((glob_vars_and_defs.g_taskCBArray sg) # "LosTaskCB" + taskID) ->ₛ "sortList")|] &&
    emp) l.
    Intros x.
    csimpl.
    simpl.
    Exists un pu.
    rewrite H.
    unfold store_task_sorted_dll.
    rewrite H0.
    unfold glob_vars_and_defs.TaskID.
    csimpl.
    entailer!.
    unfold storesortedLinkTaskNode.
    Intros y.
    unfold task_store.
    apply addr_of_arrow_field_inv in H1.
    rewrite H1.
    unfold storesortedLinkNode.
    Exists y.
    csimpl.
    simpl.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint. 
    Intros l1_2 l2_2.
    Exists l1_2 l2_2.
    entailer!.
    csimpl.
    simpl.
    Exists x.
    rewrite H0.
    csimpl.
    entailer!.
Qed. 


