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
From LOS_Verify.VC.code.link Require Import OsDeleteNodeSortLink_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Require Import LOS_Verify.lib.sortlink.
Require Import LOS_Verify.lib.dll.
Require Import LOS_Verify.lib.tick_backup.
Local Open Scope sac.

Lemma proof_of_OsDeleteNodeSortLink_which_implies_wit_1 : OsDeleteNodeSortLink_which_implies_wit_1.
Proof. 
    pre_process.
    unfold store_sorted_dll.
    unfold increasingSortedNode.
    unfold increasing.
    entailer!.
    rewrite map_app.
    rewrite map_cons.
    unfold sortedLinkNodeMapping at 2.
    simpl.
    entailer!.
Qed. 


Lemma proof_of_OsDeleteNodeSortLink_which_implies_wit_2 : OsDeleteNodeSortLink_which_implies_wit_2.
Proof. 
    pre_process.
    unfold storesortedLinkNode.
    Intros y.
    simpl.
    entailer!. 
    apply addr_of_arrow_field_inv in H.
    entailer!.
    rewrite H.
    entailer!.
Qed.

Lemma increasing_split_head: forall (A:Type) (a: DL_Node (sortedLinkNode A)) (l: list (DL_Node (sortedLinkNode A))), increasing (a::l) -> increasing l .
Proof.
    intros.
    unfold increasing in H.
    unfold increasing.
    destruct l.
    - auto.
    - destruct H.
      apply H0.
Qed.

Lemma increasing_split_head2: forall (A:Type) (a a0: DL_Node (sortedLinkNode A)) (l: list (DL_Node (sortedLinkNode A))), increasing (a::(a0::l)) -> increasing (a::l) .
Proof.
    intros.
    unfold increasing in H.
    unfold increasing.
    unfold increasing_aux in H.
    destruct H.
    induction l.
    - unfold increasing_aux.
      auto.
    - destruct H0.
      unfold increasing_aux.
      split.
      + lia .
      + apply H1.
Qed.

Lemma increasing_merge: forall (A:Type) (a0 a1: DL_Node (sortedLinkNode A)) (l: list (DL_Node (sortedLinkNode A))),increasing(a0::a1::nil)->increasing(a1::l)->increasing(a0::a1::l).
Proof.
    intros.
    unfold increasing in H0.
    unfold increasing.
    unfold increasing in H.
    unfold increasing_aux in H.
    unfold increasing_aux in H0.
    destruct H.
    unfold increasing_aux.
    split.
    - apply H.
    - apply H0.
Qed.

Lemma increasing_split: forall (A:Type) (a: DL_Node (sortedLinkNode A)) (l1 l2: list (DL_Node (sortedLinkNode A))),increasing(l1++a::l2)->increasing(l1++l2).
Proof.
    intros.
    induction l1.
    - simpl in H.
      apply increasing_split_head in H.
      auto.
    - assert(H1: increasing (a0::l1++a::l2)). { apply H. }
      unfold increasing in H.
      simpl in H.
      induction l1.
      {assert(nil++a:: l2=a::l2). { auto. }
      assert(a0 :: nil ++ a :: l2 = a0::a::l2). { auto. }
      rewrite H0 in H.
      rewrite H2 in H1.
      pose proof increasing_split_head2 A a0 a l2.
      apply H3 in H1. 
      apply H1.
      }
      assert (increasing (a0 :: (a1 :: l1) ++ a :: l2)) by (apply H1).
      apply increasing_split_head in H1.
      apply IHl1 in H1.
      assert (increasing (a0::a1::nil)).
      { 
        unfold increasing.
        unfold increasing_aux.
        unfold increasing in H0.
        unfold increasing_aux in H0. simpl in H0. destruct H0.
        split.
        apply H0.
        auto.
      }
      pose proof increasing_merge A a0 a1 (l1++l2) H2 H1.
      apply H3.
Qed.

Lemma proof_of_OsDeleteNodeSortLink_return_wit_1 : OsDeleteNodeSortLink_return_wit_1.
Proof. 
    pre_process.
    unfold store_dll.
    Intros h pt.
    entailer!.
    unfold store_sorted_dll.
    unfold store_dll.
    Exists 0 0.
    Exists h pt.
    entailer!.
    rewrite map_app.
    subst.
    entailer!.
    unfold storesortedLinkNode.
    Exists sortList_pre.
    simpl.
    entailer!.
    apply increasing_split in H1.
    apply H1.
Qed.



