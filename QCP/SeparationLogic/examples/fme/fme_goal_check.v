Require Import fme_goal fme_proof_auto fme_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include fme_strategy_proof.
  Include fme_proof_auto.
  Include fme_proof_manual.
End VC_Correctness.
