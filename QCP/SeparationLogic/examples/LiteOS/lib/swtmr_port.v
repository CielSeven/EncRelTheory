Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass. 
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Coq.Logic.FunctionalExtensionality.
Local Open Scope Z_scope.
Local Open Scope sets.
Require Import String.
Local Open Scope string.
Require Import SL.ConAssertion SL.CriticalSTS.
From LOS_Verify.lib Require Import dll sortlink queue tick glob_vars_and_defs.
Import DLL.
Import SDLL.

From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample.
Export MonadNotation.
Local Open Scope stmonad.


Require Import LOS_Verify.lib.Los_Rules_lib.
Import Los_C_Rules.
Import SwtmrStateDef.
Local Open Scope sac.
Require Import LOS_Verify.lib.Los_Verify_State_def.

(* From LOS_Verify.lib Require Import glob_vars_and_defs.
From LOS_Verify.lib Require Import critical_tick_lib task. *)

(********************* critical_tick_lib.v definition Start *****************************)

(********************* critical_tick_lib.v definition End *****************************)

(********************* definition of Swtmr_C_Rules *****************************)

Definition SWTMR_LIMIT : Z := 5. 
Definition OS_SWTMR_MAX_TIMERID : Z := 0xFFFFFFFF. 


(* Definition SWTMRHandlerQID := Z.  (* Handler队列ID，指出Handler函数所在的消息队列 *)
Definition g_swtmrSortLinkList := addr. *)

(* Record Los_Verify_State := mkOSAbstractState {
    SwtmrState: Glob_SWTMRAbstractState;
    g_tick_state: tickGlobalState;
    (* ... *)
}. *)

(********************* sortlink.v predicates Start *****************************)


Lemma list_nonempty_split :
    forall {A : Type} (l : list A),
        l <> nil -> exists l1 x l2, l = app l1 (cons x l2).
Proof.
    intros A l H.
    destruct l.
    - exfalso. apply H. reflexivity. (* 列表为空与假设矛盾 *)
    - exists nil, a, l. simpl. reflexivity. (* 非空列表拆分为 [] ++ x :: l2 *)
Qed.

Lemma store_swtmr_sorted_dll_split (sg: StableGlobVars)(l: list (DL_Node(sortedLinkNode SwtmrID))):
    l <> nil -> exists l1 x l2, 
        store_swtmr_sorted_dll sg l = store_swtmr_sorted_dll sg (l1 ++ x :: l2).
Proof.
    intros.
    destruct l as [ |x l0].
    - exfalso. apply H. reflexivity.
    - exists nil, x, l0. simpl. reflexivity.
Qed.

Definition store_swtmr_sorted_dll_missing_i (sg: StableGlobVars)(l: list (DL_Node(sortedLinkNode SwtmrID))) (i: SwtmrID): Assertion :=
    (* TODO *)
    [| True |]. 
(********************* sortlink.v predicates End *****************************)

(* Module absswtmr from swtmr.v *)
(* Module absswtmr. *)

    Definition notIn {A} (item: A) (l: list A): Prop :=
        ~ In item l.

    Definition used_swtmr_in_range (st: Glob_SWTMRAbstractState): Prop :=
        forall CbID, (CbID >= 0 /\ CbID < SWTMR_LIMIT)%Z ->
            match st.(inUseStates) CbID with
            | None => True
            | Some s => (s.(ID) mod SWTMR_LIMIT = CbID)
            end.
  
  
  Definition unused_swtmr_in_range (st: Glob_SWTMRAbstractState): Prop :=
    Forall (fun CbID => 0 <= CbID mod SWTMR_LIMIT < SWTMR_LIMIT) st.(unUsedStates).


  (* Definition unused_swtmr_in_range (st : Glob_SWTMRAbstractState): Prop := 
    Forall (fun SwtmrID => 0 <= SwtmrID < SWTMR_LIMIT) st.(unUsedStates).

  Definition used_swtmr_in_range (st : Glob_SWTMRAbstractState): Prop :=
    forall SwtmrID : SwtmrID, 
    match st.(inUseStates) SwtmrID with
      | Some _ => 0 <= SwtmrID < SWTMR_LIMIT
      | None => True
    end. *)
  Definition CbIDInFreelist (CbID: SWTMRCbID) (st : Glob_SWTMRAbstractState): Prop :=
    exists ID : SwtmrID, In ID st.(unUsedStates) /\ ID mod SWTMR_LIMIT = CbID.
  
  Definition check_swtmr_list (st : Glob_SWTMRAbstractState): Prop :=
    forall CbID : SWTMRCbID,
    0 <= CbID < SWTMR_LIMIT ->
    ( CbIDInFreelist CbID st /\ st.(inUseStates) CbID = None) \/
    ( ~ CbIDInFreelist CbID st /\ exists b : SWTMRAbstractState, st.(inUseStates) CbID = Some b).

  Definition valid_GlobSWTMRAbstractState (st:Glob_SWTMRAbstractState): Prop := 
    used_swtmr_in_range st /\ unused_swtmr_in_range st /\ check_swtmr_list st.

  
  Definition Status2Z (s: SWTMRStatus): Z := 
    match s with
    | created   => 0
    | ticking   => 1
    end.
  Parameter occupy_sdll_node :  addr -> Assertion.
  Parameter occupy :  addr -> Assertion.
  Definition used_complete_swtmr
              (ctrl_start: addr)
              (s: SWTMRAbstractState): Assertion :=
    (* TODO: 类似于pendList，usedSWTMR的权限在sortlink里*)
    (* y的存储 *)
    (* &(ctrl_start # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |->_ **  *)
    (* (EX __, &(( ctrl_start # "tagSwTmrCtrl") ->ₛ "pstNext") # Ptr |-> __) ** *)
    &(( ctrl_start # "tagSwTmrCtrl") ->ₛ "pstNext") # Ptr |-> 0 **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "usTimerID") # UInt |-> s.(ID) **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "uwInterval") # UInt |-> s.(interval) **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "startTime") # UInt64 |-> s.(startTime) **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "ucMode") # UChar |-> s.(mode) **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "ucState") # UChar |-> s.(status) **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "ucOverrun") # UChar |->_ **
    occupy_sdll_node &(ctrl_start # "tagSwTmrCtrl" ->ₛ "stSortList").

  Definition unused_complete_swtmr
        (ctrl_start: addr)
        (swtmrID: SwtmrID) (next: addr): Assertion :=
    (* TODO: 类似于pendList，unUsedSWTMR的权限在自己这 *)
    (* &(ctrl_start # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |->_ ** *)
    (* (EX __, &(( ctrl_start # "tagSwTmrCtrl") ->ₛ "pstNext") # Ptr |-> __) ** *)
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |-> next **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "usTimerID") # UInt |-> swtmrID **

    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "uwInterval") # UInt |->_ **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "startTime") # UInt64 |->_ **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "ucMode") # UChar |->_ **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "ucState") # UChar |-> 0 **
    &(ctrl_start # "tagSwTmrCtrl" ->ₛ "ucOverrun") # UChar |->_ **

    (* (EX __, &((ctrl_start # "tagSwTmrCtrl") ->ₛ "uwInterval") # UInt |-> __) **
    (EX __, &((ctrl_start # "tagSwTmrCtrl") ->ₛ "startTime") # UInt64 |-> __) **
    (EX __, &((ctrl_start # "tagSwTmrCtrl") ->ₛ "ucMode") # UChar |-> __) **
    (EX __, &((ctrl_start # "tagSwTmrCtrl") ->ₛ "ucState") # UChar |-> __) ** *)

    occupy_sdll_node &(ctrl_start # "tagSwTmrCtrl" ->ₛ "stSortList").
  
  (* Lemma unused_complete_swtmr_repr : forall (x: addr) (ID: Z),
  &( x # "tagSwTmrCtrl" ->ₛ "usTimerID") # Int |-> ID **
    (EX __, (&( x # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |-> __) **
    (&( x # "tagSwTmrCtrl" ->ₛ "uwInterval") # UInt |-> 0 **
      (&( x # "tagSwTmrCtrl" ->ₛ "startTime") # UInt64 |-> 0 **
      (&( x # "tagSwTmrCtrl" ->ₛ "ucMode") # UChar |-> 0 **
        &( x # "tagSwTmrCtrl" ->ₛ "ucState") # UChar |-> 0)))) |--
  unused_complete_swtmr x ID.
  Proof.
    intros.
    unfold unused_complete_swtmr.
    entailer!.
    Intro_any.
    Exists x0.
    entailer!.
  Qed. *)

  (* Lemma unused_complete_swtmr_repr_reverse : forall (x: addr) (ID: Z), unused_complete_swtmr x ID |-- 
  &( x # "tagSwTmrCtrl" ->ₛ "usTimerID") # Int |-> ID **
   (EX __, (&( x # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |-> __) **
    (&( x # "tagSwTmrCtrl" ->ₛ "uwInterval") # UInt |-> 0 **
     (&( x # "tagSwTmrCtrl" ->ₛ "startTime") # UInt64 |-> 0 **
      (&( x # "tagSwTmrCtrl" ->ₛ "ucMode") # UChar |-> 0 **
       &( x # "tagSwTmrCtrl" ->ₛ "ucState") # UChar |-> 0)))).
  Proof.
    intros.
    unfold unused_complete_swtmr.
    entailer!.
    Intro_any.
    Exists x0.
    entailer!.
  Qed. *)

  Definition store_used_swtmr_map
              (x: addr)
              (m: SWTMRCbID -> option SWTMRAbstractState): Assertion :=
  store_map
    (fun CbID s =>
    (* CbID == (s.(ID) mod SWTMR_LIMIT) *)
      used_complete_swtmr ( x + sizeof("tagSwTmrCtrl") *  CbID) s
    ) 
    m.

  Definition store_used_swtmr_map_missing_i
                (x: addr)
                (m: SWTMRCbID -> option SWTMRAbstractState)
                (missingID : SWTMRCbID): Assertion :=
  store_map_missing_i
  (fun CbID s =>
  used_complete_swtmr (x + sizeof("tagSwTmrCtrl") * CbID) s)
    m missingID.

  (* sll *)
  (* store_free_swtmr_list sg.(g_swtmrCBArray) list_Z(5) *)
  (* store_free_swtmr_list_seg x 0 l *)
  Fixpoint store_free_swtmr_list
                (x: addr)
                (l: list SwtmrID): Assertion :=
    match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                  (* (let y :=  x + sizeof("tagSwTmrCtrl") in *)
                  EX y: addr,
                    unused_complete_swtmr x a y **
                    (* &(x # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |-> y ** *)
                    store_free_swtmr_list y l0
                  (* )  *)
    end.


  (* sllseg *)
  (* store_free_swtmr_list_seg sg.(g_swtmrCBArray) right list_Z(index) *)
  Fixpoint store_free_swtmr_list_seg
      (left: addr)
      (right: addr)
      (l: list SwtmrID): Assertion :=   
    match l with
      | nil     => [| left = right |] && emp
      | a :: l0 => [| left <> NULL |] && 
                  (* (let z :=  left + sizeof("tagSwTmrCtrl") in *)
                  EX z: addr,
                     unused_complete_swtmr left a z **
                     (* &(left # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |-> z ** *)
                     store_free_swtmr_list_seg z right l0
                  (* ) *)
    end.


  Lemma fold_unused_complete_swtmr: 
      forall x i a y,
        (* x <> NULL -> *)
        &((x # "tagSwTmrCtrl" + i) ->ₛ "usTimerID") # UInt |-> a **
        &((x # "tagSwTmrCtrl" + i) ->ₛ "pstNext") # Ptr |-> y **
        
        &((x # "tagSwTmrCtrl" + i) ->ₛ "uwInterval") # UInt |->_ **
        &((x # "tagSwTmrCtrl" + i) ->ₛ "startTime") # UInt64 |->_ **
        &((x # "tagSwTmrCtrl" + i) ->ₛ "ucMode") # UChar |->_ **
        &((x # "tagSwTmrCtrl" + i) ->ₛ "ucState") # UChar |->_ **

        (* (EX __, &((x # "tagSwTmrCtrl") ->ₛ "uwInterval") # UInt |-> __) **
        (EX __, &((x # "tagSwTmrCtrl") ->ₛ "startTime") # UInt64 |-> __) **
        (EX __, &((x # "tagSwTmrCtrl") ->ₛ "ucMode") # UChar |-> __) **
        (EX __, &((x # "tagSwTmrCtrl") ->ₛ "ucState") # UChar |-> __) ** *)

        occupy_sdll_node &((x # "tagSwTmrCtrl" + i) ->ₛ "stSortList")
      |--
        unused_complete_swtmr (x + sizeof ("tagSwTmrCtrl") * i) a y.
  Proof.
    unfold unused_complete_swtmr.
    intros. csimpl. entailer!.
  Admitted.
  
    (* Lemma store_free_swtmr_list_seg_len1:  *)

  Lemma store_free_swtmr_list_seg_len1: 
    forall x i a y,
      x + sizeof ("tagSwTmrCtrl") * i <> NULL ->
      &((x # "tagSwTmrCtrl" + i) ->ₛ "usTimerID") # UInt |-> a **
      &((x # "tagSwTmrCtrl" + i) ->ₛ "pstNext") # Ptr |-> y **
      
      &((x # "tagSwTmrCtrl" + i) ->ₛ "uwInterval") # UInt |->_ **
      &((x # "tagSwTmrCtrl" + i) ->ₛ "startTime") # UInt64 |->_ **
      &((x # "tagSwTmrCtrl" + i) ->ₛ "ucMode") # UChar |->_ **
      &((x # "tagSwTmrCtrl" + i) ->ₛ "ucState") # UChar |->_ **

      (* (EX __, &((x # "tagSwTmrCtrl") ->ₛ "uwInterval") # UInt |-> __) **
      (EX __, &((x # "tagSwTmrCtrl") ->ₛ "startTime") # UInt64 |-> __) **
      (EX __, &((x # "tagSwTmrCtrl") ->ₛ "ucMode") # UChar |-> __) **
      (EX __, &((x # "tagSwTmrCtrl") ->ₛ "ucState") # UChar |-> __) ** *)

      occupy_sdll_node &((x # "tagSwTmrCtrl" + i) ->ₛ "stSortList")
        (* unused_complete_swtmr x a y *)
    |--
        store_free_swtmr_list_seg (x + sizeof ("tagSwTmrCtrl") * i) y (cons a nil).
    Proof.
      intros.
      sep_apply fold_unused_complete_swtmr.
      simpl store_free_swtmr_list_seg.
      Exists y.
      entailer!.
      (* sep_apply fold_unused_complete_swtmr.
      unfold unused_complete_swtmr.
      entailer!.
      Intro_any. Intro_any. Intro_any. Intro_any.
      Exists y. entailer!.
      Exists x0. entailer!.
      Exists x1. entailer!.
      Exists x2. entailer!.
      Exists x3. entailer!. *)
    Qed.
  
Lemma swtmr_seg_sll: forall x y l1 l2,
  store_free_swtmr_list_seg x y l1 ** store_free_swtmr_list y l2 |--
  store_free_swtmr_list x (l1 ++ l2).
  Proof.
    intros.
    revert x; induction l1; simpl store_free_swtmr_list_seg; simpl store_free_swtmr_list; intros.
    + Intros.
      subst y.
      entailer!.
    + Intros. Intros z0.
      Exists z0.
      sep_apply IHl1.
      entailer!.
Qed.

  Lemma store_map_split_emp:
  forall {A B: Type} (P: A -> B -> Assertion) (a: A) (b: B) (m: A -> option B),
    m a = None ->
    store_map P m |-- store_map_missing_i P m a ** emp.
  Proof.
  Admitted.

  Definition store_glob_swtmr (sg: StableGlobVars) (s: Glob_SWTMRAbstractState): Assertion :=
    store_used_swtmr_map sg.(g_swtmrCBArray) s.(inUseStates) **
    store_free_swtmr_list sg.(g_swtmrFreeList) s.(unUsedStates).
  


  Definition t_update {X: Type} (m: Z -> option X) (k: Z) (v: option X) : Z -> option X :=
      fun (x : Z) => if Z.eq_dec k x then v else m x.

  (* Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
  Proof.
    intros.
    apply iff_reflect.
    rewrite <- beq_id_true_iff.
    reflexivity.
  Qed. *)

  Theorem t_update_same : forall x X (m : Z -> option X),
    t_update m x (m x) = m.
  Proof.
    intros.
    unfold t_update.
    apply functional_extensionality_dep.
    intros.
    destruct (Z.eq_dec x x0)%Z.
    + admit.
    + reflexivity.
  Admitted.

  Definition update_inUseStates (inUseStates: SWTMRCbID -> option SWTMRAbstractState) (ID: SwtmrID) (status: Z) : SWTMRCbID -> option SWTMRAbstractState := 
    match status with
    | 0 => t_update inUseStates (ID % 5) None
    | _ => inUseStates
    end.

  Definition changeStatus (state: SWTMRAbstractState) (status: Z) : SWTMRAbstractState := 
    mkSWTMR (ID state) (interval state) (startTime state) (mode state) status.

    Definition update_used_state (st: Los_Verify_State) (cbid: SWTMRCbID) (state: SWTMRAbstractState) : Los_Verify_State :=
        let gSwtmrSt := (SwtmrState st) in
            replace_swtmrS (mkSWTMRAbstractState (t_update (inUseStates gSwtmrSt) cbid (Some state)) (unUsedStates gSwtmrSt) (sortlink gSwtmrSt) (queue gSwtmrSt) (SWTMRHandlerQID gSwtmrSt)) st.

  Definition getSortLinkList (item: addr): addr := item.
  
  Definition cyclic_plus_5 (ID: SwtmrID) : SwtmrID :=
    if Z.ltb (* TODO: dec definition*) ID (OS_SWTMR_MAX_TIMERID - SWTMR_LIMIT)
             then ID + SWTMR_LIMIT
             else (ID mod SWTMR_LIMIT).

  Definition Init_inUseStates : SWTMRCbID -> option SWTMRAbstractState :=
    fun (CbID: SWTMRCbID) => None.
  
  Definition Init_qMap : QueueMap :=
    fun (QID: QID) => None.


  Fixpoint range (maxnum : nat) : list nat :=
    match maxnum with
    | O => nil 
    | S n => n :: (range n) 
    end.

  Definition list_Z (maxnum : Z) : list Z :=
    rev (map Z.of_nat (range (Z.to_nat maxnum))).

  (* Definition Init_QueueState : Glob_QueueAbstractState :=
    abstqueue.mkQueueGlobAbstractState (list_Z 32) Init_qMap. *)

    (* &(ctrl_start # "g_swtmrCBArray" ->ₛ "ucState") # Int |-> Status2Z s.(status) ** *)
    Definition store_undef_swtmr (x : addr) (i : Z) (a : Z): Assertion :=
      (* &((x # "tagSwTmrCtrl" + i) ->ₛ "usTimerID") # Int |-> _ **
      &((x # "tagSwTmrCtrl" + i) ->ₛ "pstNext") # Ptr |-> _.  *)
      (* (EX __, &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "usTimerID") # Int |-> __) ** *)
      &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "usTimerID") # UInt |->0 **
      (* (EX __, &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "pstNext") # Ptr |-> __) **  *)
      &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "pstNext") # Ptr |->0 ** 
      &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "uwInterval") # UInt |->0 **
      &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "startTime") # UInt64 |->0 **
      &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "ucMode") # UChar |->0 **
      &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "ucState") # UChar |->0 **
      occupy_sdll_node &(( (x + i * sizeof("tagSwTmrCtrl")) # "tagSwTmrCtrl") ->ₛ "stSortList").


      (* (EX __, &(( (x + i) # "tagSwTmrCtrl") ->ₛ "usTimerID") # Int |-> __) ** *)
      (* (EX __, &(( (x + i) # "tagSwTmrCtrl") ->ₛ "pstNext") # Ptr |-> __) ** 
      (EX __, &(( (x + i) # "tagSwTmrCtrl") ->ₛ "uwInterval") # Int |-> __) **
      (EX __, &(( (x + i) # "tagSwTmrCtrl") ->ₛ "startTime") # Int |-> __) **
      (EX __, &(( (x + i) # "tagSwTmrCtrl") ->ₛ "ucMode") # Int |-> __) **
      (EX __, &(( (x + i) # "tagSwTmrCtrl") ->ₛ "ucState") # Int |-> __). *)
    (* Lemma store_undef_swtmr_merge *)
 
    (* TODO *)
    (* Definition store_swtmr_array (x: addr) (lo: Z) (hi: Z) (l: list SWTMRAbstractState): Assertion :=
      (store_array_rec store_swtmr x lo hi (sublist lo hi l)). *)
    
    (* Fixpoint store_array_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (lo hi: Z) (l: list A): CRules.expr := *)
    (* Fixpoint store_array_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (lo hi: Z) (l: list A): CRules.expr :=
      match l with
      | nil     => [| lo = hi |] && [| l = nil |] && emp
      | a :: l0 => storeA x lo a ** store_array_rec storeA x (lo + 1) hi l0
      end.

    Fixpoint store_array_missing_i_rec {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (i lo hi: Z) (l: list A): CRules.expr :=
      match l with
      | nil     => [| False |]
      | a :: l0 => [| i = lo |] && store_array_rec storeA x (lo + 1) hi l0 ||
                  [| i > lo |] && storeA x lo a ** store_array_missing_i_rec storeA x i (lo + 1) hi l0
      end. *)

    (* Definition store_array {A : Type} (storeA : addr -> Z -> A -> CRules.expr) (x: addr) (n: Z) (l: list A): CRules.expr :=
      store_array_rec storeA x 0 n l. *)

    Fixpoint list_0 (n: nat) : list Z :=
      match n with
      | 0%nat => nil
      | S n' => cons 0%Z (list_0 n')
      end.
    Definition store_undef_swtmr_array_rec (x: addr) (lo hi: Z) : Assertion :=
      (store_array_rec store_undef_swtmr x lo hi (list_0 (Z.to_nat (hi - lo)) ) ).

    Definition store_undef_swtmr_array_missing_i_rec (x: addr) (i lo hi: Z): Assertion :=
      (store_array_missing_i_rec store_undef_swtmr x i lo hi (list_0 (Z.to_nat (hi - lo)) ) ).

    Definition storeSwtmrSortLink (sg: StableGlobVars) (p: addr) (ID: SwtmrID) : Assertion :=
      [|p = &((sg.(g_swtmrCBArray) # "SWTMR_CTRL_S" + (ID % 5)) ->ₛ "stSortList")|] &&
       emp.

    (* temp_pred（x，index）然后对index=0/1 *)
    Definition temp_pstNext (x: addr) (index: Z): Assertion :=
      match Z.to_nat(index) with 
      | 0%nat => [|False|]
      | 1%nat => &( x # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |->_
      | _ => &( x # "tagSwTmrCtrl" ->ₛ "pstNext") # Ptr |-> (x + sizeof("tagSwTmrCtrl"))
    end.
    (* Zmult_succ_r_reverse: forall n m : Z, n * m + n = n * Z.succ m *)
    Lemma Zmult_succ_r_custom : forall n m : Z, n * Z.succ m = n + m * n.
    Proof.
        intros.
        rewrite <- Zmult_succ_r_reverse.
        rewrite Z.add_comm.
        rewrite Zmult_comm.
        reflexivity.
    Qed.

    Lemma store_undef_swtmr_succ : forall (x: addr) (i a: Z), store_undef_swtmr (x + sizeof ("tagSwTmrCtrl")) i a = store_undef_swtmr (x) (Z.succ i) a.
    Proof.
        intros.
        unfold store_undef_swtmr.
        rewrite <- Z.add_assoc.
        rewrite <- Zmult_succ_r_custom.
        rewrite <- Zmult_comm. 
        reflexivity.
    Qed.
    
    Lemma sotre_undef_swtmr_array_rec_succ : forall (x: addr) (i n: Z),
        store_undef_swtmr_array_rec (x + sizeof ("tagSwTmrCtrl")) i n = 
            store_undef_swtmr_array_rec x (i+1) (n+1).
    Proof.
        intros.
        unfold store_undef_swtmr_array_rec.
        (* rewrite <- store_undef_swtmr_succ. *)
        unfold store_undef_swtmr.
    Admitted.
    
    Lemma swtmr_array_missing_i_eq_array : forall (x: addr) (i lo hi: Z),
        store_undef_swtmr_array_missing_i_rec x i lo hi =
            store_undef_swtmr_array_rec x (i+1) hi.
    Proof.
        intros.
        unfold store_undef_swtmr_array_missing_i_rec.
        unfold store_undef_swtmr_array_rec.
        (* rewrite sotre_undef_swtmr_array_rec_succ. *)
    Admitted.
  (* 表示谓词和抽象状态都不涉及别的模块；临界区内函数前后条件可能需要swtmr和queue的表示谓词；临界区外的抽象操作，可能涉及swtmr和queue（仅SWTMRHandlerQID涉及的queue）两边的状态 *)

  (* Definition SWTMRHandlerQ := FMapAVL.Make(Nat_as_OT).find SWTMRHandlerQID QueueMap. 暂未使用 *)

  (* Definition SWTMRSortLL := LinkAbstractState.  *)
  (* sortlink提供给我的库，用多态的sortlink *)
  (* 所有软件定时器的高层状态表示为从定时器ID到软件定时器状态的映射 *)

  (* 抽象状态Valid条件 *)

  Definition ValidUsedSWTMRstate (state: Glob_SWTMRAbstractState): Prop :=
  forall CbID, (CbID >= 0 /\ CbID < SWTMR_LIMIT)%Z ->
      match state.(inUseStates) CbID with
      | None => True
      | Some s => ~ (List.In s.(ID) state.(unUsedStates)) /\ 
                  (s.(ID) mod SWTMR_LIMIT = CbID)
      end.

  
    Fixpoint ValidUnUsedSWTMRstate_fix (unused: list SwtmrID) (used: SWTMRCbID -> option SWTMRAbstractState): Prop :=
    match unused with 
        | nil => True
        | ID :: l0 => used (ID mod SWTMR_LIMIT) = None /\ ValidUnUsedSWTMRstate_fix l0 used
    end.

  Definition ValidUnUsedSWTMRstate  (state: Glob_SWTMRAbstractState): Prop :=
    ValidUnUsedSWTMRstate_fix state.(unUsedStates) state.(inUseStates).


Definition vaild_cond1 (state: Glob_SWTMRAbstractState) : Prop :=
  forall swtmrID, swtmrID >= 0  -> (
  (
    (exists b, state.(inUseStates) (swtmrID mod SWTMR_LIMIT) = Some b) /\
    ~ (In swtmrID state.(unUsedStates) )
  ) \/
  (
    ~ (exists b, state.(inUseStates) (swtmrID mod SWTMR_LIMIT) = Some b) /\
    (In swtmrID state.(unUsedStates) ) 
  ) ).

  (* Definition vaild_sortedLink (s : TcbGlobalState) (l : list (sortedLinkNode TaskID)): Prop :=
    forall sln:(sortedLinkNode TaskID) , (In sln l <->
      exists (tsk:TaskAbstractState) (t1: TaskID) (t2: TaskID) (_1 _2 _4: bool) (_3 _5: option Z), 
            ((s.(usedTask) sln.(data)) = Some tsk) 
        /\ ((tsk.(status) = wait (mkWaitStatus _1 _2 (Some t1) _4 _5) ) \/ (tsk.(status) = wait (mkWaitStatus _1 _2 _3 _4 (Some t2 ) ))) (*status equals delayed / pendtime *)
        /\ sln.(responseTime) = t1 + t2). *)
  
  (* 表示调度中 sortedlink 的谓词在调度模块，l 为swtmr.v模块中的排序链表抽象状态，下方为vaild 条件 *)

  (* Definition ValidSortLink (state: Glob_SWTMRAbstractState) : Prop :=
    forall node: (DL_Node (sortedLinkNode SwtmrID)), (In node (sortlink state) <->
      exists (swtmr: SWTMRAbstractState),
      let sln := node.(dll_data) in
        ( ( (inUseStates state) sln.(data)) = Some (ID swtmr) ) /\
          (status swtmr) = 2 (* ticking *) 
    ). *)


  Definition ValidQueue (state: Glob_SWTMRAbstractState): Assertion := 
    [|True|]
    .

    Record swtmr_valid_cond_prop (st: Glob_SWTMRAbstractState) : Prop :=
    {
        (* swtmr_cond1 : ValidUsedSWTMRstate st;
        swtmr_cond2 : ValidUnUsedSWTMRstate st; *)
        swtmr_cond1 : vaild_cond1 st;
    }.

  (* 单个SWTMR的存储 *)
  (* ValidSWTMRMapAndFreeList /\ singleSWTMR *)
  Definition singleSWTMR (sg: StableGlobVars) (ID: Z) (state: Glob_SWTMRAbstractState): Assertion :=
    let CbID := ID mod SWTMR_LIMIT in 
    match state.(inUseStates) CbID with 
      | None       => (EX __, unused_complete_swtmr (sg.(g_swtmrCBArray) + CbID) ID __)
      | Some s   =>  used_complete_swtmr (sg.(g_swtmrCBArray) + CbID) s
    end.

  Definition Z_to_nat (x: Z) : nat := Z.to_nat(x).

  Fixpoint allSWTMR (sg: StableGlobVars) (l: list Z) (state: Glob_SWTMRAbstractState): Assertion :=
    match l with
      | nil => emp
      | x :: l0 => singleSWTMR sg x state ** allSWTMR sg l0 state
    end.
  (* Definition ValidSortLink(): Assertion :=
    EX l : list(sortedLinkNode SwtmrID),  *)
    (*usedSWTMR与sortlink的对应关系*)  (*l是双向链表形式存储*)

  (* Handler队列表示谓词：表示Handler及其参数如何在消息队列SWTMRHandlerQ中存储 *)
  (* *)
(* End absswtmr. *)
(* Module absswtmr from swtmr.v *)

(* Module concur_absswtmr. *)
(* 
    Definition inv_tick tgs: Assertion :=
        EX (ct_v : Z),
          [| tick_vaild_cond_prop tgs |] &&
          &("SysTick") # Ptr |-> ct_v **
          storeTick &("g_archTickTimer") ct_v tgs. *)
(* 
    Definition store_glob_swtmr (sg: StableGlobVars) (s: Glob_SWTMRAbstractState): Assertion :=
    store_used_swtmr_map sg.(g_swtmrCBArray) s.(inUseStates) **
    store_free_swtmr_list sg.(g_swtmrFreeList) s.(unUsedStates).
           *)
        
    Definition swtmr_inv (sg: StableGlobVars) (st: Los_Verify_State): Assertion :=
        (* [| valid condition |] && *)
        [| swtmr_valid_cond_prop st.(SwtmrState) |] &&
        store_glob_swtmr sg (st.(SwtmrState)) **
        store_swtmr_sorted_dll sg (sortlink (SwtmrState st)).
    
    (* Definition os_inv (sg: StableGlobVars) (st: Los_Verify_State): Assertion :=
        swtmr_inv sg st **
        inv_tick st.(g_tick_state). *)
        (* store_task_sorted_dll sg st.xxx.yyy *)
        (* storeTickSetting st.(tset) ** *)

    Definition swtmr_inv_missing_used_swtmr_without_sortlink (swtmrCbID : SWTMRCbID)  (sg: StableGlobVars) (st: Los_Verify_State): Assertion :=
        [| exists b, st.(SwtmrState).(inUseStates) swtmrCbID = Some b |] &&
        [| swtmr_valid_cond_prop st.(SwtmrState) |] &&
        store_used_swtmr_map_missing_i sg.(g_swtmrCBArray) st.(SwtmrState).(inUseStates) swtmrCbID **
        store_free_swtmr_list sg.(g_swtmrFreeList) st.(SwtmrState).(unUsedStates).

    Definition swtmr_inv_missing_used_swtmr (swtmrCbID : SWTMRCbID)  (sg: StableGlobVars) (st: Los_Verify_State): Assertion :=
        swtmr_inv_missing_used_swtmr_without_sortlink swtmrCbID sg st **
        store_swtmr_sorted_dll sg (sortlink (SwtmrState st)).

    
    Definition store_unused_swtmr_list_exclude (x : addr) (l : list SwtmrID) (sID : SwtmrID) : Assertion :=
      match l with
      | nil     => [| x = NULL |] && emp
      | a :: l0 => [| x <> NULL |] && 
                    EX y: addr,
                      (if Z.eq_dec a sID then emp else 
                      unused_complete_swtmr x a y ) **
                      store_free_swtmr_list y l0
      end.  
  
  
  Lemma derives_trans : forall P Q R : Assertion,
  P |-- Q ->
  Q |-- R ->
  P |-- R.
  Proof. Admitted.

  Lemma andp_left2 : forall P Q R : Assertion,
  Q |-- R ->
  P && Q |-- R.
  Proof. Admitted.
  Lemma exp_left : forall A (P : A -> Assertion) Q,
  (forall x : A, P x |-- Q) ->
  (EX x : A, P x) |-- Q.
  Proof. Admitted.

  Lemma swtmr_map_missing_i_to_map :
  forall base m CbId swtmr b,
  store_used_swtmr_map_missing_i base m CbId **
  used_complete_swtmr swtmr b
  |-- store_used_swtmr_map base m.
  Proof. Admitted.

  Lemma sll_exclude_to_sll :
  forall start l id x y,
  store_unused_swtmr_list_exclude start l id ** unused_complete_swtmr x id y |-- store_free_swtmr_list start l.
  Proof.
  intros start l id x y.
  induction l.
  - (* 基础情形：空链表 *)
    unfold store_free_swtmr_list, store_unused_swtmr_list_exclude.
    entailer!. admit.
  - (* 递归情形：非空链表 *)
    unfold store_free_swtmr_list, store_unused_swtmr_list_exclude.
    (* entailer!. *)
    destruct (Z.eq_dec a id).
    + (* 情况 1: a = id *)
      (* 提取 storeA x id y 并补全 sll
      的 storeA start a y *)
      apply derives_trans with 
        ([| start <> NULL |] && EX y0 : addr, unused_complete_swtmr start a y0 ** store_free_swtmr_list y0 l).
      * entailer!. Intro_any. Exists x0. entailer!. admit. admit.
      (* start <> NULL *) 
      * entailer!. Intro_any. Exists x0. entailer!. admit.
    + (* 情况 2: a ≠ id *)
      (* sll 和 sll_exclude 在此处定义相同 *)
      apply derives_trans with 
        ([| start <> NULL |] && EX y0 : addr, unused_complete_swtmr start a y0 ** store_unused_swtmr_list_exclude y0 l id).
      * 
      (* rewrite prop_andp_sepcon1. apply andp_left2.  *)
      entailer!. Intro_any. Exists x0. entailer!. admit. admit.
      (* apply exp_left. intro y0. cancel. apply IHl. *)
  Admitted.

    Definition store_unused_swtmr_missing_i (x: addr) (unUsedStates: list SwtmrID) (missed: addr): Assertion :=
        (* TODO *)
        (* exists l1 l2, *)
        EX l1 l2,
        store_free_swtmr_list_seg x missed l1 **
        store_free_swtmr_list (missed + sizeof ("tagSwTmrCtrl")) l2.
        (* store_free_swtmr_list_seg left (x + missed * sizeof(struct tagSwTmrCtrl)) l1 **
        store_free_swtmr_list (base + (missed+1) * sizeof(struct tagSwTmrCtrl)) l2. *)

    Definition swtmr_inv_missing_unused_swtmr_without_sortlink (swtmrID: SwtmrID)  (sg: StableGlobVars) (st: Los_Verify_State): Assertion :=
        [| swtmr_valid_cond_prop st.(SwtmrState) |] &&
        store_used_swtmr_map sg.(g_swtmrCBArray) st.(SwtmrState).(inUseStates) **
        store_unused_swtmr_list_exclude sg.(g_swtmrFreeList) st.(SwtmrState).(unUsedStates) swtmrID.

    Definition swtmr_inv_missing_unused_swtmr (swtmrID: SwtmrID)  (sg: StableGlobVars) (st: Los_Verify_State): Assertion :=
        swtmr_inv_missing_unused_swtmr_without_sortlink swtmrID sg st **
        store_swtmr_sorted_dll sg (sortlink (SwtmrState st)).

(* End concur_absswtmr. *)

(********************* LOS_TaskStatusGet Start *****************************)
(* UINT32 LOS_TaskStatusGet(UINT32 taskID, UINT32 *taskStatus)
{
    UINT32    intSave;
    LosTaskCB *taskCB = NULL;
    if (taskStatus == NULL) {
        return LOS_ERRNO_TSK_PTR_NULL;
    }
    if (OS_CHECK_TSK_PID_NOIDLE(taskID)) {
        return LOS_ERRNO_TSK_ID_INVALID;
    }
    taskCB = OS_TCB_FROM_TID(taskID);
    intSave = LOS_IntLock();
    if (taskCB->taskStatus & OS_TASK_STATUS_UNUSED) {
        LOS_IntRestore(intSave);
        return LOS_ERRNO_TSK_NOT_CREATED;
    }
    *taskStatus = taskCB->taskStatus;
    LOS_IntRestore(intSave);
    return LOS_OK;
} *)
(* Definition atomic_statusGet (taskID : Z) (taskstatus_ptr: Z): program (TcbGlobalState -> Prop) (option Z) :=
    choice 
    (test (taskstatus_ptr = 0);; return None )
    (test (not (taskstatus_ptr = 0)) ;; 
        choice
        (test (taskID >= 6);; return None ) 
        (test (taskID < 6) ;; 
            atomic_cmd 
            (fun s1 r s2 => 
            s1 = s2 /\  ( (exists b, s1.(usedTask) taskID = Some b /\ r = Some b.(status) ) \/
                            ( not (exists b, s1.(usedTask) taskID = Some b) /\ r = None) )
            )
        )
    ). *)

(********************* LOS_TaskStatusGet End *****************************)

(****************** OsSwtmrGetNextTimeout Start **************************)
(* UINT32 OsSwtmrGetNextTimeout() {
    UINT32 intSave = LOS_IntLock();
    UINT64 time = OsSortLinkGetNextExpireTime(g_swtmrSortLink);
    LOS_IntRestore(intSave);
    time = OS_SYS_CYCLE_TO_TICK(time);
    if (time > (UINT64)OS_NULL_INT) {
        time = (UINT64)OS_NULL_INT;
    }
    return (UINT32)time;
} *)

Definition atomic_OsSwtmrGetNextTimeout_old (sg: StableGlobVars) (Time : Z): program (Los_Verify_State -> Prop) (option Z) :=
    choice 
    (test (((Time * 100) / sg.(g_sysClock)) > 0xFFFFFFFF);; return (Some 0xFFFFFFFF) )
    (test (not (((Time * 100) / sg.(g_sysClock)) > 0xFFFFFFFF)) ;; 
          return (Some ((Time * 100) / sg.(g_sysClock))) )
    .


  (* Definition atomic_cmd {A} (c: program Los_Verify_State A): program (Los_Verify_State -> Prop) A :=
    fun X1 a X2 =>
        exists l1 l2, X1 l1 /\ c l1 a l2 /\
            X2 == (RTrans_Abs l2). *)

Definition atomic_OsSortLinkGetNextExpireTime (l: list(DL_Node(sortedLinkNode SwtmrID))): program (Los_Verify_State -> Prop) Z := 
    atomic_cmd 
    (fun s1 r s2 => 
        s1 = s2 /\ ( r = (getFirstNodeResponseTime l) )
    ).


Definition atomic_OsSwtmrGetNextTimeout (sg: StableGlobVars)(l: list(DL_Node(sortedLinkNode SwtmrID))) : program (Los_Verify_State -> Prop) (option Z) :=
    t <- atomic_OsSortLinkGetNextExpireTime l;;
    choice 
    (test (((t * 100) / sg.(g_sysClock)) > 0xFFFFFFFF);; return (Some 0xFFFFFFFF) )
    (test (not (((t * 100) / sg.(g_sysClock)) > 0xFFFFFFFF)) ;; 
            return (Some ((t * 100) / sg.(g_sysClock))) )
    .
(****************** OsSwtmrGetNextTimeout End **************************)

(****************** LOS_SwtmrTimeGet Start **************************)

Definition atomic_LOS_SwtmrTimeGet(swtmrID: SwtmrID) (tick_ptr: addr): program (Los_Verify_State -> Prop) (option Z) :=
    choice
    (test (swtmrID >= OS_SWTMR_MAX_TIMERID);; return None)
    (test (not (swtmrID >= OS_SWTMR_MAX_TIMERID)) ;;
        choice
        (test (tick_ptr = 0);; return None )
        (test (not (tick_ptr = 0)) ;; 
            atomic_cmd 
            (fun s1 r s2 => 
                s1 = s2 /\  (
                ( exists id, not (id = swtmrID) /\ r = None) \/
                ( In swtmrID s1.(SwtmrState).(unUsedStates) /\ r = None) \/
                ( exists b t, s1.(SwtmrState).(inUseStates) (unsigned_last_nbits (swtmrID mod SWTMR_LIMIT) 16) = Some b /\ 
                (
                    (not (swtmrID = b.(ID)) /\ r = None) \/
                    (swtmrID = b.(ID) /\ (
                        (b.(status) = 2 /\ r = Some t) \/
                        (not (b.(status) = 2) /\ r = None)
                    ) )
                ) )
            ) ) (* end atomic_cmd *)
            
        )
    ).
(****************** LOS_SwtmrTimeGet End **************************)

(****************** LOS_SwtmrStop Start **************************)

Definition atomic_LOS_SwtmrStop(swtmrID: SwtmrID): program (Los_Verify_State -> Prop) (unit) :=
    choice
    (test (swtmrID >= OS_SWTMR_MAX_TIMERID);; return tt)
    (test (not (swtmrID >= OS_SWTMR_MAX_TIMERID)) ;;
        atomic_cmd 
        (fun s1 r s2 => 
        (   
            ( s1 = s2 /\ exists id, not (id = swtmrID) /\ r = tt) \/
            ( s1 = s2 /\ In swtmrID s1.(SwtmrState).(unUsedStates) /\ r = tt) \/
            ( exists b, s1.(SwtmrState).(inUseStates) (unsigned_last_nbits (swtmrID mod SWTMR_LIMIT) 16) = Some b /\ 
            (
                (s1 = s2 /\ not (swtmrID = b.(ID)) /\ r = tt) \/
                (swtmrID = b.(ID) /\ (
                    (s2 = update_used_state s1 (unsigned_last_nbits (swtmrID mod SWTMR_LIMIT) 16) (changeStatus b 1) /\ b.(status) = 2 /\ r = tt) \/
                    (s1 = s2 /\ not (b.(status) = 2) /\ r = tt)
                ) )
            ) )
        ) ) (* end atomic_cmd *)
    ).
(****************** LOS_SwtmrStop End **************************)
