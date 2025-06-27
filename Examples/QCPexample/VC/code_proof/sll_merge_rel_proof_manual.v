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
From Examples.QCP Require Import sll_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import sll_lib.
Require Import sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap relations.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_merge_return_wit_1_1 : merge_return_wit_1_1.
Proof. Admitted. 

Lemma proof_of_merge_return_wit_1_2 : merge_return_wit_1_2.
Proof. Admitted. 

Lemma proof_of_merge_which_implies_wit_3 : merge_which_implies_wit_3.
Proof. Admitted. 

Lemma proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Proof. Admitted. 

Lemma proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Proof. Admitted. 

Lemma proof_of_split_rec_which_implies_wit_2 : split_rec_which_implies_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_sort_entail_wit_1 : merge_sort_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort_entail_wit_2 : merge_sort_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_merge_sort_return_wit_1 : merge_sort_return_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort_partial_solve_wit_3_pure : merge_sort_partial_solve_wit_3_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_entail_wit_1 : merge_sort3_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort3_entail_wit_2 : merge_sort3_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_merge_sort3_return_wit_1 : merge_sort3_return_wit_1.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_5_pure : merge_sort3_partial_solve_wit_5_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_partial_solve_wit_6_pure : merge_sort3_partial_solve_wit_6_pure.
Proof. Admitted. 

Lemma proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort3_derive_high_level_spec_by_low_level_spec : merge_sort3_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort2_derive_low_level_spec_aux_by_low_level_spec : merge_sort2_derive_low_level_spec_aux_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort2_derive_high_level_spec_by_low_level_spec : merge_sort2_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_derive_low_level_spec_aux_by_low_level_spec : merge_sort_derive_low_level_spec_aux_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_split_rec_derive_low_level_spec_aux_by_low_level_spec : split_rec_derive_low_level_spec_aux_by_low_level_spec.
Proof. Admitted. 

Lemma proof_of_split_rec_derive_high_level_spec_by_low_level_spec : split_rec_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 

