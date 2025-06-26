From SimpleC.EE Require Import swap_goal swap_proof_auto swap_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include swap_proof_auto.
  Include swap_proof_manual.
End VC_Correctness.
