From LOS_Verify.VC.code.link Require Import OsAdd2SortLink_goal OsAdd2SortLink_proof_auto OsAdd2SortLink_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include los_sortlink_strategy_proof.
  Include OsAdd2SortLink_proof_auto.
  Include OsAdd2SortLink_proof_manual.
End VC_Correctness.
