typedef unsigned short UINT16;
typedef unsigned int UINT32;
typedef unsigned long long UINT64;
typedef int INT32;//not support signed int
typedef char CHAR;
typedef unsigned int UINTPTR;
/*@ Import Coq Require Import LOS_Verify.lib.Los_Rules_lib */
/*@ Extern Coq TaskID := Z  */
/*@ Extern Coq addr := Z */
//@ Extern Coq (StableGlobVars :: * )
/*@ Extern Coq Record StableGlobVars {
  g_taskCBArray: addr;
  g_swtmrCBArray: addr;
  g_allSem: addr;
  g_allQueue: addr;
  g_allMux: addr;
  g_priQueueList : addr;
}
*/
/*@ Import Coq Require Import LOS_Verify.lib.Los_Rules_lib */
/*@ Import Coq Import Los_C_Rules*/
/*@ Extern Coq (not: Prop -> Prop) */
/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (dup_data_at_error : Z -> Assertion) */
/*@ Extern Coq (dup_data_at_error_prop : Prop) */
/*@ Extern Coq (option :: * => *) */
/*@ Extern Coq (Some: {A} -> A -> option A)

               (None: {A} -> option A)

               (In:{A}-> A -> list A -> Prop)*/
/*@ Extern Coq (UINT_MAX : Z) */
/*@ Extern Coq addr := Z */
/*@ include strategies "common.strategies" */
typedef struct LOS_DL_LIST {
    struct LOS_DL_LIST *pstPrev; /**< Current node's pointer to the previous node */
    struct LOS_DL_LIST *pstNext; /**< Current node's pointer to the next node */
} LOS_DL_LIST;
/*@ Import Coq Require Import LOS_Verify.lib.dll*/
/*@ Extern Coq (DL_Node :: * => *) */
/*@ Extern Coq (data: {A} -> DL_Node A -> A )

               (ptr: {A} -> DL_Node A -> Z )*/
/*@ Extern Coq (Build_DL_Node: {A} -> A -> Z -> DL_Node A)

               (store_dll: {A} -> (Z -> A -> Assertion) -> Z -> (list (DL_Node A)) -> Assertion)

               (dllseg: {A} -> (Z -> A -> Assertion) -> Z -> Z -> Z -> Z -> (list (DL_Node A)) -> Assertion)

               (dllseg_shift: {A} -> (Z -> A -> Assertion) -> Z -> Z -> (list (DL_Node A)) -> Assertion)

               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)

               (store_pend_list_dll: StableGlobVars -> Z -> list(TaskID) -> Assertion)

 */
/*@ include strategies "los_list.strategies" */
typedef struct {
    LOS_DL_LIST sortLinkNode;
    UINT64 responseTime;
} SortLinkList;
/*@ Import Coq Require Import LOS_Verify.lib.sortlink */
