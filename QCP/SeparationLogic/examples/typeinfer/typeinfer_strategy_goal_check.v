Require Import typeinfer_strategy_goal typeinfer_strategy_proof.

Module typeinfer_Strategy_Correctness : typeinfer_Strategy_Correct.
  Include typeinfer_strategy_proof.
End typeinfer_Strategy_Correctness.
