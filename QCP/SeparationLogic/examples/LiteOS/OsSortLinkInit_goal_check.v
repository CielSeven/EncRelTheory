From LOS_Verify.VC.code.link Require Import OsSortLinkInit_goal OsSortLinkInit_proof_auto OsSortLinkInit_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include OsSortLinkInit_proof_auto.
  Include OsSortLinkInit_proof_manual.
End VC_Correctness.
