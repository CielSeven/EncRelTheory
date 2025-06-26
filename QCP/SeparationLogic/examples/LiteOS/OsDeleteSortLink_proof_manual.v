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
From LOS_Verify.VC.code.link Require Import OsDeleteSortLink_goal.
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

Lemma storesortedLinkNode_split : 
    forall (A : Type) (storeA : Z -> A -> Assertion) (y y0 : Z) (a : A) (t : Z),
    y = &( y0 # "SortLinkList" ->ₛ "sortLinkNode") ->
    storeA y (sl_data {| sl_data := a; responseTime := t |}) **
    &( y0 # "SortLinkList" ->ₛ "responseTime") # UInt64 |-> responseTime {| sl_data := a; responseTime := t |}|--
    storesortedLinkNode storeA y {| sl_data := a; responseTime := t |}.
Proof.
    intros.
    simpl.
    unfold storesortedLinkNode.
    Exists y0.
    entailer!.
Qed.


Lemma dllseg_head_insert:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (py y z x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z |--
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l).
Proof.
    intros.
    simpl.
    Exists z.
    entailer!.
Qed.

Lemma proof_of_OsDeleteSortLink_return_wit_1_1 : OsDeleteSortLink_return_wit_1_1.
Proof. 
  pre_process.
  Right.
  entailer!.
  unfold store_sorted_dll.
  entailer!.
  unfold store_dll.
  pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) v_5 v_pstPrev x (map sortedLinkNodeMapping l2).
  sep_apply(H3).
  Intros py.
  pose proof dllseg_shift_to_dllseg (storesortedLinkNode storeA) x v_6 v_pstNext (map sortedLinkNodeMapping l1).
  sep_apply(H4).
  Intros x0.
  Exists x0 py.
  pose proof storesortedLinkNode_split A storeA &( node_pre #"SortLinkList"->ₛ"sortLinkNode") node_pre a t.
  simpl in H5.
  sep_apply(H5).
  pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) v_6 v_pstPrev v_5 x py (mksortedLinkNode a t) (map sortedLinkNodeMapping l2).
  rewrite H1 in H7.
  rewrite H1.
  -
   revert H7.
   csimpl.
   intros H7.
   sep_apply(H7).
   pose proof dllseg_concat (storesortedLinkNode storeA) x0 x v_pstNext v_6 x py (map sortedLinkNodeMapping l1) ({|
    data := {| sl_data := a; responseTime := t |};
    ptr := &( node_pre # "SortLinkList" ->ₛ "sortLinkNode")
  |} :: map sortedLinkNodeMapping l2).
   rewrite H0 in H8.
   rewrite H0.
   sep_apply(H8).
   rewrite map_app.
   rewrite map_cons.
   entailer!.
  -
   lia.
Qed.


Lemma proof_of_OsDeleteSortLink_which_implies_wit_1 : OsDeleteSortLink_which_implies_wit_1.
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

Lemma proof_of_OsDeleteSortLink_which_implies_wit_2 : OsDeleteSortLink_which_implies_wit_2.
Proof. 
    pre_process.
    unfold store_dll.
    Intros h pt.
    sep_apply(dllseg_split (storesortedLinkNode(storeA)) h x x pt).
    Intros x0 py.
    simpl dllseg.
    Intros z.
    subst.
    pose proof dllseg_to_dllseg_shift_rev (storesortedLinkNode storeA) z &(node#"SortLinkList"->ₛ "sortLinkNode") x pt (map sortedLinkNodeMapping l2).
    sep_apply (H).
    pose proof dllseg_to_dllseg_shift (storesortedLinkNode storeA) h x &( node # "SortLinkList" ->ₛ "sortLinkNode") py (map sortedLinkNodeMapping l1).
    sep_apply (H0).

    Exists &( node # "SortLinkList" ->ₛ "sortLinkNode") z &( node # "SortLinkList" ->ₛ "sortLinkNode") py.

    entailer!.
    csimpl.
    entailer!.
Qed. 

Lemma proof_of_OsDeleteSortLink_which_implies_wit_3 : OsDeleteSortLink_which_implies_wit_3.
Proof. 
    pre_process.
    unfold storesortedLinkNode.
    Intros y.
    simpl.
    entailer!.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    entailer!. 
Qed. 

Lemma proof_of_OsDeleteSortLink_which_implies_wit_4 : OsDeleteSortLink_which_implies_wit_4.
Proof. 
    pre_process.
    unfold store_sorted_dll.
    unfold increasing.
    unfold increasingSortedNode.
    unfold store_dll.
    entailer!.
    (* Search dllseg. *)
    pose proof dllseg_shift_rev_to_dllseg (storesortedLinkNode storeA) v v_pstPrev x (map sortedLinkNodeMapping l2).
    sep_apply(H2).
    Intros py.
    pose proof dllseg_shift_to_dllseg (storesortedLinkNode storeA) x v_2 v_pstNext (map sortedLinkNodeMapping l1).
    sep_apply(H3).
    Intros x0.
    Exists x0 py.
    pose proof storesortedLinkNode_split A storeA &( node #"SortLinkList"->ₛ"sortLinkNode") node a t.
    simpl in H4.
    sep_apply(H4).
    pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) v_2 v_pstPrev v x py (mksortedLinkNode a t) (map sortedLinkNodeMapping l2).
    rewrite H1 in H6.
    rewrite H1.
    - 
     revert H6.
     csimpl.
     intros H6.
     sep_apply(H6).
     pose proof dllseg_concat (storesortedLinkNode storeA) x0 x v_pstNext v_2 x py (map sortedLinkNodeMapping l1) ({|
        data := {| sl_data := a; responseTime := t |};
        ptr := &( node # "SortLinkList" ->ₛ "sortLinkNode")
      |} :: map sortedLinkNodeMapping l2).
     rewrite H0 in H7.
     rewrite H0.
     sep_apply(H7).
     rewrite map_app.
     rewrite map_cons.
     entailer!.
    -
     lia.
Qed.




