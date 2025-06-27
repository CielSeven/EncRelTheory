Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Examples.QCP Require Import kmp_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

Lemma proof_of_inner_entail_wit_2 : inner_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_inner_entail_wit_3 : inner_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_inner_return_wit_1 : inner_return_wit_1.
Proof. Admitted. 

Lemma proof_of_inner_return_wit_2 : inner_return_wit_2.
Proof. Admitted. 

Lemma proof_of_constr_entail_wit_1 : constr_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_constr_entail_wit_2 : constr_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_constr_return_wit_1 : constr_return_wit_1.
Proof. Admitted. 

Lemma proof_of_constr_partial_solve_wit_5_pure : constr_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_constr_which_implies_wit_1 : constr_which_implies_wit_1.
Proof. Admitted. 

Lemma proof_of_match_entail_wit_1 : match_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_match_entail_wit_2 : match_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_match_return_wit_1 : match_return_wit_1.
Proof. Admitted. 

Lemma proof_of_match_return_wit_2 : match_return_wit_2.
Proof. Admitted. 

Lemma proof_of_match_partial_solve_wit_4_pure : match_partial_solve_wit_4_pure.
Proof. Admitted. 

Lemma proof_of_match_derive_high_level_spec_by_low_level_spec : match_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_constr_derive_high_level_spec_by_low_level_spec : constr_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_inner_derive_bind_spec_by_low_level_spec : inner_derive_bind_spec_by_low_level_spec.
Proof. Admitted. 

