From Examples.QCPexample Require Import sll_merge_rel_goal sll_merge_rel_proof_auto sll_merge_rel_proof_manual.

Module VC_Correctness : VC_Correct.
  Include common_strategy_proof.
  Include sll_strategy_proof.
  Include safeexec_strategy_proof.
  Include sll_merge_rel_proof_auto.
  Include sll_merge_rel_proof_manual.
End VC_Correctness.
