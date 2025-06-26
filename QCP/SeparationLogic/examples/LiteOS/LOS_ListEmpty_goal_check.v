From LOS_Verify.VC.code.link Require Import LOS_ListEmpty_goal LOS_ListEmpty_proof_auto LOS_ListEmpty_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include LOS_ListEmpty_proof_auto.
  Include LOS_ListEmpty_proof_manual.
End VC_Correctness.
