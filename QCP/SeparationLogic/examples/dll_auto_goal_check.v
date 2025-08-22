From SimpleC.EE Require Import dll_auto_goal dll_auto_proof_auto dll_auto_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include dll_shape_strategy_proof.
  Include dll_auto_proof_auto.
  Include dll_auto_proof_manual.
End VC_Correctness.
