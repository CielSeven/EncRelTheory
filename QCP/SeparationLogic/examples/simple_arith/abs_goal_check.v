From SimpleC.EE.simple_arith Require Import abs_goal abs_proof_auto abs_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include abs_proof_auto.
  Include abs_proof_manual.
End VC_Correctness.
