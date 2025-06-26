From SimpleC.EE Require Import dll_queue_goal dll_queue_proof_auto dll_queue_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include dll_queue_strategy_proof.
  Include dll_queue_proof_auto.
  Include dll_queue_proof_manual.
End VC_Correctness.
