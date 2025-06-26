From LOS_Verify.VC.code.link Require Import OsSortLinkGetTargetExpireTime_goal OsSortLinkGetTargetExpireTime_proof_auto OsSortLinkGetTargetExpireTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include OsSortLinkGetTargetExpireTime_proof_auto.
  Include OsSortLinkGetTargetExpireTime_proof_manual.
End VC_Correctness.
