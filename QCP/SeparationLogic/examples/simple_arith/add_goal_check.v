From SimpleC.EE.simple_arith Require Import add_goal add_proof_auto add_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include add_proof_auto.
  Include add_proof_manual.
End VC_Correctness.
