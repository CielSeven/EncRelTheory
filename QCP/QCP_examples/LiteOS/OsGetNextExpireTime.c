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
/*@ Extern Coq (nil : {A} -> list A)

               (cons : {A} -> A -> list A -> list A)

               (app : {A} -> list A -> list A -> list A)

               (rev : {A} -> list A -> list A)

               (map : {A} {B} -> (A -> B) -> list A -> list B)

               (concat : {A} -> list (list A) -> list A)

               (NoDup : {A} -> list A -> Prop)

               (Znth: {A} -> Z -> list A -> A -> A)

               (replace_Znth: {A} -> Z -> A -> list A -> list A)

 */
/*@ Extern Coq addr := Z */
/*@ Extern Coq TaskID := Z */
/*@ Extern Coq SwtmrID := Z */
/*@ Extern Coq Record StableGlobVars {
  g_taskCBArray: Z;
  g_swtmrCBArray: Z;
  g_allSem: Z;
  g_allQueue: Z;
}
*/
/*@ Extern Coq Record tickState {
  ts_period : Z;
  ts_val : Z;
  ts_ctrl : Z;
  ts_startTime : Z;
  ts_timeBase : Z;
  ts_oldTimeBase : Z;
  ts_timeBaseUpdate : Z;
} */
/*@ Extern Coq Record archTickTimer {
  freqNum : Z;
  irqNum : Z;
  periodMax : Z;
} */
/*@ Extern Coq (sortedLinkNode :: * => *) */
/*@ Extern Coq (DL_Node :: * => *) */
/*@ Extern Coq (sl_data: {A} -> sortedLinkNode A -> A)
               (responseTime: {A} -> sortedLinkNode A -> Z)*/
/*@ Extern Coq (data: {A} -> DL_Node A -> A)
               (ptr: {A} -> DL_Node A -> Z)*/
/*@ Extern Coq (storesortedLinkNode: {A} -> (Z -> A -> Assertion) -> Z -> sortedLinkNode A -> Assertion)
               (task_store: StableGlobVars -> Z -> TaskID -> Assertion)
               (storesortedLinkTaskNode: (StableGlobVars -> Z -> TaskID -> Assertion) -> StableGlobVars -> Z -> sortedLinkNode TaskID -> Assertion)
               (store_sorted_dll: {A} -> (Z -> A -> Assertion)  -> Z -> list (DL_Node(sortedLinkNode A)) -> Assertion)
               (store_task_sorted_dll: StableGlobVars -> list (DL_Node(sortedLinkNode TaskID)) -> Assertion)
               (store_swtmr_sorted_dll: StableGlobVars -> list (DL_Node(sortedLinkNode SwtmrID)) -> Assertion)
               (mksortedLinkNode: {A} -> A -> Z -> sortedLinkNode A)
               (getFirstNodeExpireTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> Z) 
               (increasingSortedNode: {A} -> list (DL_Node(sortedLinkNode A)) -> Prop)
               (getNodeExpireTime: {A} -> DL_Node(sortedLinkNode A) -> Z -> Z -> Z)
               (getminExpireTime: {A} -> list (DL_Node(sortedLinkNode A)) -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> Z)
               (updateNodeTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z -> Z -> list (DL_Node(sortedLinkNode A)))
               (getFirstNodeResponseTime: {A} -> list (DL_Node(sortedLinkNode A)) -> Z)
               (sortedLinkNodeMapping : {A} -> (DL_Node(sortedLinkNode A)) -> (DL_Node(sortedLinkNode A)))
               (getFirstNodeData: {A} -> list (DL_Node(sortedLinkNode A)) -> A) 
               (storeTick: Z -> Z -> tickState -> archTickTimer -> Assertion)
               (timebase_turnover: tickState -> tickState)
               (tick_getcycle_ret: tickState -> Z)
               (ULLONG_MAX : Z)
               (obtian_first_pointer: {A} -> Z -> list (DL_Node(sortedLinkNode A)) -> Z)
*/
/*@ Extern Coq (eq_dec: Z -> Z -> Prop) */
/*@ Extern Coq (Build_DL_Node: {A} -> A -> Z -> DL_Node A)
               (store_dll: {A} -> (Z -> A -> Assertion) -> Z -> list (DL_Node A) -> Assertion)
               (dllseg: {A} -> (Z -> A -> Assertion) -> Z -> Z -> Z -> Z-> list (DL_Node A) -> Assertion)
               (dllseg_shift: {A} -> (Z -> A -> Assertion) -> Z -> Z-> list (DL_Node A) -> Assertion)
               (dll_para: {A} -> (Z -> A -> Assertion) -> Prop)
               (dllseg_shift_rev: {A} -> (Z -> A -> Assertion) -> Z -> Z-> list (DL_Node A) -> Assertion)
*/
/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (increasing: list Z -> Prop)
               (rev : {A} -> list A -> list A)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion)
               (sllseg : {A} -> (Z -> A -> Assertion) -> Z -> Z -> list A -> Assertion)
               (map : {A} {B} -> (A -> B) -> list A -> list B)
 */
/*@ include strategies "../los_sortlink.strategies" */
/*@ Import Coq Require Import LOS_Verify.lib.sortlink */
/*@ Import Coq Require Import LOS_Verify.lib.dll*/
/*@ Import Coq Require Import LOS_Verify.lib.tick_backup*/
typedef enum {
    OS_SORT_LINK_DEFAULT,
    OS_SORT_LINK_TASK,
    OS_SORT_LINK_SWTMR
} SortLinkType;
typedef struct LOS_DL_LIST{
    struct LOS_DL_LIST * pstPrev;
    struct LOS_DL_LIST * pstNext;
} LOS_DL_LIST;
typedef struct SortLinkList{
    LOS_DL_LIST sortLinkNode;
    unsigned long long responseTime;
} SortLinkList;
typedef struct SortLinkAttribute{
    LOS_DL_LIST sortLink;
} SortLinkAttribute;
unsigned int TASKID;
unsigned int SWMTRID;
extern SortLinkAttribute g_taskSortLink;
extern SortLinkAttribute g_swtmrSortLink;
unsigned long long OS_SORT_LINK_UINT64_MAX;
static inline unsigned long long GetSortLinkNextExpireTime(SortLinkAttribute *sortHead, unsigned long long startTime, unsigned long long tickPrecision)
/*@ highSpec
  With {A}(storeA: Z -> A -> Assertion) (l: list(DL_Node(sortedLinkNode A)))
  Require store_sorted_dll(storeA, &(sortHead->sortLink), l) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1) 
  Ensure  (__return == getFirstNodeExpireTime(l, startTime, tickPrecision)) &&
           store_sorted_dll(storeA, &(sortHead->sortLink), l) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1) 
*/
;
static inline unsigned long long GetSortLinkNextExpireTime(SortLinkAttribute *sortHead, unsigned long long startTime, unsigned long long tickPrecision)
/*@ taskSpec <= highSpec
  With (sg: StableGlobVars)(l: list(DL_Node(sortedLinkNode TaskID)))
  Require store_task_sorted_dll(sg, l) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1) && (sortHead == &g_taskSortLink) 
  Ensure   (__return == getFirstNodeExpireTime(l, startTime, tickPrecision)) &&
           store_task_sorted_dll(sg, l) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1)
*/
;
static inline unsigned long long GetSortLinkNextExpireTime(SortLinkAttribute *sortHead, unsigned long long startTime, unsigned long long tickPrecision)
/*@ swmtrSpec <= highSpec
  With (sg: StableGlobVars)(l: list(DL_Node(sortedLinkNode SwtmrID)))
  Require store_swtmr_sorted_dll(sg, l) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1) && (sortHead == &g_swtmrSortLink) 
  Ensure   (__return == getFirstNodeExpireTime(l, startTime, tickPrecision)) &&
           store_swtmr_sorted_dll(sg, l) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1)
*/
;
static inline unsigned long long OsGetNextExpireTime(unsigned long long startTime, unsigned long long tickPrecision)
/*@
  With (sg: StableGlobVars)(l1: list(DL_Node(sortedLinkNode TaskID)))(l2: list(DL_Node(sortedLinkNode SwtmrID)))
  Require store_task_sorted_dll(sg, l1) * store_swtmr_sorted_dll(sg, l2) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1)
  Ensure   store_task_sorted_dll(sg, l1) * store_swtmr_sorted_dll(sg, l2) * data_at(&(OS_SORT_LINK_UINT64_MAX), unsigned long long, (2^64)-1) && (__return == getminExpireTime(l1, l2, startTime, tickPrecision))      
*/
{
    unsigned long long taskExpireTime = GetSortLinkNextExpireTime(&g_taskSortLink, startTime, tickPrecision)/*@ where (taskSpec) sg = sg, l = l1*/;
    unsigned long long swtmrExpireTime = GetSortLinkNextExpireTime(&g_swtmrSortLink, startTime, tickPrecision)/*@ where (swmtrSpec) sg = sg, l = l2*/;;
    if (taskExpireTime < swtmrExpireTime){
       return taskExpireTime;
    }
    else{
        return swtmrExpireTime;
    }
}
