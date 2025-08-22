From SimpleC.EE Require Import poly_sll_goal poly_sll_proof_auto poly_sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include poly_sll_strategy_proof.
  Include poly_sll_proof_auto.
  Include poly_sll_proof_manual.
End VC_Correctness.
