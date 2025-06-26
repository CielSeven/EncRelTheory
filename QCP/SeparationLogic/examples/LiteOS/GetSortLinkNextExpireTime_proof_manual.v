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
From LOS_Verify.VC.code.link Require Import GetSortLinkNextExpireTime_goal.
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


Lemma dllseg_head_split:
  forall (A: Type) (storeA: Z -> A -> Assertion) 
         (y py x pt: Z) (a: A) (l: list (DL_Node A)),
    dllseg storeA y py x pt ((Build_DL_Node a y) :: l) |--
    EX z,
    dllseg storeA z y x pt l **
    storeA y a **
    &(y # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> py **
    &(y # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z.
Proof.
    intros.
    simpl.
    Intros z.
    Exists z.
    entailer!.
Qed.

Lemma head_trans:
forall (A: Type) (storeA: Z -> A -> Assertion) 
    (y py x pt az: Z) (a: A) (l: list (DL_Node A)),
  dllseg storeA y py x pt ((Build_DL_Node a az) :: l) |--
[| az = y|].
Proof.
    intros.
    simpl.
    unfold store_dll.
    Intros z.
    rewrite H.
    entailer!.
Qed.

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

Lemma store_dll_shift_rev_unfold:
forall {A: Type} (storeA: addr -> A -> Assertion)(x: addr) (l: list (DL_Node A)),
  store_dll storeA x l |--
  EX xn: addr ,
  &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> xn **
  &(xn # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> x **
  dllseg_shift_rev storeA xn x l.
Proof.
  intros.
  unfold store_dll.
  Intros h pt.
  sep_apply (dllseg_to_dllseg_shift_rev storeA h x x pt l).
  Exists h.
  entailer!.
Qed.

Lemma map_sortedLinkNodeMapping_not_nil : forall [A B : Type]  (f : A -> B) (l : list A),
  map f l <> nil -> l <> nil.
Proof.
    pre_process.
    intros.
    csimpl.
    destruct l.
    +
    contradiction.
    +
    congruence.
Qed.

Lemma map_sortedLinkNodeMapping : forall [A: Type](d a: DL_Node (sortedLinkNode A)) (l1 l: list (DL_Node (sortedLinkNode A))),
  map sortedLinkNodeMapping (d::l) = a::l1 ->  d.(dll_data) = a.(dll_data).
Proof.
    pre_process.
    intros.
    csimpl.
    simpl in H.
    destruct d.
    destruct a.
    simpl in H.
    unfold sortedLinkNodeMapping in H.
    simpl in H.
    inversion H.
    simpl.
    reflexivity.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_entail_wit_1 : GetSortLinkNextExpireTime_entail_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_entail_wit_1.
    pre_process.
    intros.
    csimpl.
    Intros.
    destruct l.
    +
    unfold obtian_first_pointer.
    simpl.
    csimpl.
    entailer!.
    assert (h = &( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")).
    apply H5.
    rewrite H6.
    entailer!.
    +
    unfold obtian_first_pointer.
    simpl.
    csimpl.
    Intros z.
    Exists z.
    entailer!.
    rewrite H5.
    entailer!.
Qed. 


Lemma proof_of_GetSortLinkNextExpireTime_return_wit_1 : GetSortLinkNextExpireTime_return_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_return_wit_1.
    pre_process.
    intros.
    csimpl.
    unfold store_sorted_dll.
    entailer!.
    unfold getFirstNodeExpireTime.
    destruct l.
    +
    unfold MaxTime.
    pose proof (unsigned_last_nbits_eq (ULLONG_MAX - tickPrecision_pre) 64).
    assert (0 <= ULLONG_MAX - tickPrecision_pre).
    lia. 
    assert ( ULLONG_MAX - tickPrecision_pre < 2 ^ 64).
    lia.
    lia.
    +
    simpl in H0.
    discriminate H0.
Qed. 

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_2 : GetSortLinkNextExpireTime_return_wit_2.
Proof. 
    unfold GetSortLinkNextExpireTime_return_wit_2.
    pre_process.
    intros.
    csimpl.
    unfold store_sorted_dll.
    entailer!.
    pose proof storesortedLinkNode_split A storeA (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) retval_2 (sl_data a.(dll_data)) (responseTime a.(dll_data)). 
    sep_apply H11.
    unfold store_dll.
    Exists &( retval_2 # "SortLinkList" ->ₛ "sortLinkNode") pt.
    csimpl.
    simpl.
    pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) pl (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) pt (mksortedLinkNode (sl_data a.(dll_data)) (responseTime a.(dll_data)))  l1. 
    csimpl.
    simpl.
    entailer!.
    revert H13.
    csimpl.
    intros.
    sep_apply H13.
    rewrite H4.
    revert H0.
    unfold obtian_first_pointer.
    csimpl.
    simpl in H2.
    rewrite H4.
    intros.
    destruct a.
    rewrite H0.
    entailer!.
    lia.
    unfold getFirstNodeExpireTime.
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
    assert (l <> nil).
    apply H11.
    apply H2.
    destruct l.
    +
    contradiction.
    +
    unfold getNodeExpireTime.
    pose proof map_sortedLinkNodeMapping d a l1 l.
    rewrite H13.
    assert (unsigned_last_nbits (startTime_pre + tickPrecision_pre) 64 = startTime_pre + tickPrecision_pre).
    pose proof (unsigned_last_nbits_eq (startTime_pre + tickPrecision_pre) 64).
    assert (0 <= startTime_pre + tickPrecision_pre).
    lia. 
    assert ( startTime_pre + tickPrecision_pre < 2 ^ 64).
    lia.
    rewrite H14.
    lia.
    lia.
    rewrite H14 in H.
    destruct (responseTime a.(dll_data) <=? startTime_pre + tickPrecision_pre)%Z eqn: En.
    lia.
    lia.
    apply H4.
Qed. 

Lemma proof_of_GetSortLinkNextExpireTime_return_wit_3 : GetSortLinkNextExpireTime_return_wit_3.
Proof.  
    unfold GetSortLinkNextExpireTime_return_wit_2.
    pre_process.
    intros.
    csimpl.
    unfold store_sorted_dll.
    entailer!.
    pose proof storesortedLinkNode_split A storeA (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) retval_2 (sl_data a.(dll_data)) (responseTime a.(dll_data)). 
    sep_apply H11.
    unfold store_dll.
    Exists &( retval_2 # "SortLinkList" ->ₛ "sortLinkNode") pt.
    csimpl.
    simpl.
    pose proof dllseg_head_insert (sortedLinkNode A) (storesortedLinkNode storeA) (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) (&( retval_2 # "SortLinkList" ->ₛ "sortLinkNode")) pl (&( sortHead_pre # "SortLinkAttribute" ->ₛ "sortLink")) pt (mksortedLinkNode (sl_data a.(dll_data)) (responseTime a.(dll_data)))  l1. 
    csimpl.
    simpl.
    entailer!.
    revert H13.
    csimpl.
    intros.
    sep_apply H13.
    rewrite H4.
    revert H0.
    unfold obtian_first_pointer.
    csimpl.
    simpl in H2.
    rewrite H4.
    intros.
    destruct a.
    rewrite H0.
    entailer!.
    lia.
    unfold getFirstNodeExpireTime.
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
    assert (l <> nil).
    apply H11.
    apply H2.
    destruct l.
    +
    contradiction.
    +
    unfold getNodeExpireTime.
    pose proof map_sortedLinkNodeMapping d a l1 l.
    rewrite H13.
    assert (unsigned_last_nbits (startTime_pre + tickPrecision_pre) 64 = startTime_pre + tickPrecision_pre).
    pose proof (unsigned_last_nbits_eq (startTime_pre + tickPrecision_pre) 64).
    assert (0 <= startTime_pre + tickPrecision_pre).
    lia. 
    assert ( startTime_pre + tickPrecision_pre < 2 ^ 64).
    lia.
    rewrite H14.
    lia.
    lia.
    rewrite H14 in H.
    destruct (responseTime a.(dll_data) <=? startTime_pre + tickPrecision_pre)%Z eqn: En.
    lia.
    lia.
    apply H4.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_1 : GetSortLinkNextExpireTime_which_implies_wit_1.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_1.
    pre_process.
    intros.
    csimpl.
    unfold store_sorted_dll.
    unfold store_dll.
    Intros h pt.
    Exists pt h.
    csimpl.
    entailer!.
Qed. 


Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_2 : GetSortLinkNextExpireTime_which_implies_wit_2.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_2.
    pre_process.
    intros.
    csimpl.
    unfold store_dll.
    Exists h pt.
    csimpl.
    entailer!.
Qed. 

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_3 : GetSortLinkNextExpireTime_which_implies_wit_3.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_3.
    pre_process.
    intros.
    csimpl.
    unfold store_dll.
    csimpl.
    Intros h pt.
    prop_apply (head_trans (sortedLinkNode A) (storesortedLinkNode storeA) h (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) pt (&( listSorted # "SortLinkList" ->ₛ "sortLinkNode")) (mksortedLinkNode al t) l1).
    entailer!.
    rewrite H.
    pose proof dllseg_head_split (sortedLinkNode A) (storesortedLinkNode storeA) h (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) (&( sortHead # "SortLinkAttribute" ->ₛ "sortLink")) pt (mksortedLinkNode al t) l1.
    sep_apply H0.
    Intros z.
    Exists pt z.
    csimpl.
    entailer!.
    rewrite <- H.
    csimpl.
    entailer!.
Qed.

Lemma proof_of_GetSortLinkNextExpireTime_which_implies_wit_4 : GetSortLinkNextExpireTime_which_implies_wit_4.
Proof. 
    unfold GetSortLinkNextExpireTime_which_implies_wit_4.
    pre_process.
    intros.
    unfold storesortedLinkNode.
    csimpl.
    Intros y.
    apply addr_of_arrow_field_inv in H.
    rewrite H.
    entailer!.
Qed. 

Lemma proof_of_LOS_ListEmpty_derive_getfirstSpec_by_highSpec : LOS_ListEmpty_derive_getfirstSpec_by_highSpec.
Proof. 
    pre_process.
    Exists A storeA l.
    entailer!.
    rewrite <- derivable1_wand_sepcon_adjoint.
    entailer!.
    apply derivable1_orp_elim.
    - Intros retval_2.
    Right.
    Exists retval_2.
    entailer!.
    - Intros retval_2.
    Left.
    unfold store_dll.
    Intros h pt.
    unfold dllseg.
    destruct l.
    + entailer!.
    + Intros z.
    Exists d l retval_2.
    Exists h pt.
    Exists z.
    entailer!.
Qed.


Lemma proof_of_GetSortLinkNextExpireTime_partial_solve_wit_5_pure: GetSortLinkNextExpireTime_partial_solve_wit_5_pure.
Proof.
    pre_process.
    entailer!.
    rewrite H.
    unfold obtian_first_pointer.
    pose proof map_sortedLinkNodeMapping_not_nil sortedLinkNodeMapping l.
    assert (l <> nil).
    apply H10.
    apply H1.
    destruct (map sortedLinkNodeMapping l).
    +
    congruence.
    +
    congruence.
Qed.
