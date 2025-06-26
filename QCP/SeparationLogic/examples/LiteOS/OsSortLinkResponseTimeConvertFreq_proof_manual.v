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
From LOS_Verify.VC.code.link Require Import OsSortLinkResponseTimeConvertFreq_goal.
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

Lemma proof_of_SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_swmtrSpec_by_highSpec.
Proof. 
  pre_process.
  unfold store_swtmr_sorted_dll.
  Intros x.
  Exists Z.
  Exists n (fun (p : addr) (swmtrID : glob_vars_and_defs.SwtmrID) =>
   [|p = &( ((glob_vars_and_defs.g_swtmrCBArray sg) # "SWTMR_CTRL_S" + swmtrID) ->ₛ "stSortList")|] &&
   emp) l.
  entailer!.
  rewrite H0, H1.
  unfold glob_vars_and_defs.SwtmrID.
  csimpl.
  entailer!.
  (* rewrite <- derivable1_wand_sepcon_adjoint. 
  Exists x. 
  rewrite H1.
   csimpl.
   entailer!. *)
Admitted. 

Lemma proof_of_SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec : SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec.
Proof. 
    unfold SortLinkNodeTimeUpdate_derive_taskSpec_by_highSpec.
    pre_process.
    intros.
    entailer!.
    unfold store_task_sorted_dll.
    eapply derivable1s_exp_r.
    Exists n (fun (p : addr) (taskID : glob_vars_and_defs.TaskID) =>
    [|p = &( ((glob_vars_and_defs.g_taskCBArray sg) # "LosTaskCB" + taskID) ->ₛ "sortList")|] &&
    emp) l.
   entailer!.
   rewrite H0.
   csimpl.
   unfold glob_vars_and_defs.TaskID.
   entailer!.
   Intros x.
   rewrite H1.
   csimpl.
   entailer!.
   rewrite <- derivable1_wand_sepcon_adjoint. 
   Exists x.
   rewrite H1.
   csimpl.
   entailer!.
Qed.
