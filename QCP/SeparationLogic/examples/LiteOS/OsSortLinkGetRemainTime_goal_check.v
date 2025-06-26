From LOS_Verify.VC.code.link Require Import OsSortLinkGetRemainTime_goal OsSortLinkGetRemainTime_proof_auto OsSortLinkGetRemainTime_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include OsSortLinkGetRemainTime_proof_auto.
  Include OsSortLinkGetRemainTime_proof_manual.
End VC_Correctness.
