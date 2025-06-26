From LOS_Verify.VC.code.link Require Import List_Add_goal List_Add_proof_auto List_Add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include List_Add_proof_auto.
  Include List_Add_proof_manual.
End VC_Correctness.
