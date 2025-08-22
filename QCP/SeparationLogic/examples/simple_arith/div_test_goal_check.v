From SimpleC.EE.simple_arith Require Import div_test_goal div_test_proof_auto div_test_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include div_test_proof_auto.
  Include div_test_proof_manual.
End VC_Correctness.
