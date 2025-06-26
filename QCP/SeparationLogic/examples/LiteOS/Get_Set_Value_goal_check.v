From LOS_Verify.VC.code.link Require Import Get_Set_Value_goal Get_Set_Value_proof_auto Get_Set_Value_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include Get_Set_Value_proof_auto.
  Include Get_Set_Value_proof_manual.
End VC_Correctness.
