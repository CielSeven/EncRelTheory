From LOS_Verify.VC.code.link Require Import OsDeleteNodeSortLink_goal OsDeleteNodeSortLink_proof_auto OsDeleteNodeSortLink_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include OsDeleteNodeSortLink_proof_auto.
  Include OsDeleteNodeSortLink_proof_manual.
End VC_Correctness.
