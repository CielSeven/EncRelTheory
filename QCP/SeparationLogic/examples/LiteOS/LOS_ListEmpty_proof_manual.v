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
From LOS_Verify.VC.code.link Require Import LOS_ListEmpty_goal.
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

Lemma proof_of_LOS_ListEmpty_return_wit_1_1 : LOS_ListEmpty_return_wit_1_1.
Proof. 
    unfold LOS_ListEmpty_return_wit_1_1.
    pre_process.
    intros.
    Right.  
    unfold store_dll.
    Exists h pt.

    induction l.
    -
    entailer!.
    -
    subst h; simpl.
    Intros z.
    prop_apply (dup_store_ptr (&(node_pre # "LOS_DL_LIST" ->ₛ "pstPrev")) node_pre pt).
    entailer!.
Qed. 

Lemma dllseg_neq:
  forall {A : Type} (storeA : addr -> A -> Assertion)
  (x px y py: addr) (l: list (DL_Node A)),
  x <> y ->
  dllseg storeA x px y py l |--
  EX z a l0,
    [| l = a :: l0 |] &&
    [| x = a.(ptr) |] &&
    storeA x a.(dll_data) **
    &(x # "LOS_DL_LIST" ->ₛ "pstPrev") # Ptr |-> px ** 
    &(x # "LOS_DL_LIST" ->ₛ "pstNext") # Ptr |-> z **
    dllseg storeA z x y py l0.
Proof.
  intros.
  destruct l; simpl.
  + entailer!.
  + Intros z0.
    Exists z0 d l.
    entailer!.
Qed.


Lemma proof_of_LOS_ListEmpty_return_wit_1_2 : LOS_ListEmpty_return_wit_1_2.
Proof. 
    unfold LOS_ListEmpty_return_wit_1_2.
    pre_process.
    intros.
    Left.
    unfold store_dll.
    Exists h pt.
    induction l.
    -
    unfold dllseg.
    simpl.
    entailer!.
    -
    entailer!.
    congruence.
Qed. 

Lemma proof_of_LOS_ListEmpty_which_implies_wit_1 : LOS_ListEmpty_which_implies_wit_1.
Proof. 
    unfold LOS_ListEmpty_which_implies_wit_1.
    pre_process.
Qed.

