From LOS_Verify.VC.code.link Require Import OsSortLinkGetNextExpireTime_goal OsSortLinkGetNextExpireTime_proof_auto OsSortLinkGetNextExpireTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include OsSortLinkGetNextExpireTime_proof_auto.
  Include OsSortLinkGetNextExpireTime_proof_manual.
End VC_Correctness.
