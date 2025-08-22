From SimpleC.EE Require Import eval_goal eval_proof_auto eval_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include eval_strategy_proof.
  Include eval_proof_auto.
  Include eval_proof_manual.
End VC_Correctness.
