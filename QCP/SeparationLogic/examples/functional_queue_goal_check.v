From SimpleC.EE Require Import functional_queue_goal functional_queue_proof_auto functional_queue_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include functional_queue_strategy_proof.
  Include functional_queue_proof_auto.
  Include functional_queue_proof_manual.
End VC_Correctness.
