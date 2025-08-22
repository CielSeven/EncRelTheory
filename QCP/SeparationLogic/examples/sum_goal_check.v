From SimpleC.EE Require Import sum_goal sum_proof_auto sum_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include int_array_strategy_proof.
  Include sum_proof_auto.
  Include sum_proof_manual.
End VC_Correctness.
