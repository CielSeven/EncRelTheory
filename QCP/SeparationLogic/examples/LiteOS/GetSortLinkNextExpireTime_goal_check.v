From LOS_Verify.VC.code.link Require Import GetSortLinkNextExpireTime_goal GetSortLinkNextExpireTime_proof_auto GetSortLinkNextExpireTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include GetSortLinkNextExpireTime_proof_auto.
  Include GetSortLinkNextExpireTime_proof_manual.
End VC_Correctness.
