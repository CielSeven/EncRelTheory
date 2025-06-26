Require Import typeinfer_goal typeinfer_proof_auto typeinfer_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include typeinfer_strategy_proof.
  Include typeinfer_proof_auto.
  Include typeinfer_proof_manual.
End VC_Correctness.
