From SimpleC.EE Require Import sll_goal sll_proof_auto sll_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include sll_proof_auto.
  Include sll_proof_manual.
End VC_Correctness.
