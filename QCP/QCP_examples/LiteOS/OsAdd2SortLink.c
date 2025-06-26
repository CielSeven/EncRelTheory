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
int LOSCFG_BASE_CORE_SWTMR;
int InvalidTime = -1;
int OS_SORT_LINK_INVALID_TIME = -1;
unsigned long long OS_SORT_LINK_UINT64_MAX = -1;
unsigned long long g_schedResponseTime = OS_SORT_LINK_UINT64_MAX;
unsigned long long OS_SCHED_MAX_RESPONSE_TIME = -1;
unsigned long long g_sysClock;
static inline void OsAddNode2SortLink(SortLinkAttribute *sortLinkHead, SortLinkList *sortList)
/*@ highSpec
    With {A}(a: A)(t: Z) (storeA: Z -> A -> Assertion) (l: list(DL_Node(sortedLinkNode A)))
    Require exists pu un,
            data_at(field_addr(&(sortList->sortLinkNode),struct LOS_DL_LIST, pstPrev),struct LOS_DL_LIST *,pu) *
            data_at(field_addr(&(sortList->sortLinkNode),struct LOS_DL_LIST, pstNext),struct LOS_DL_LIST *,un) *
            store_sorted_dll(storeA, &(sortLinkHead->sortLink), l) *
            storesortedLinkNode(storeA, &(sortList->sortLinkNode), mksortedLinkNode(a,t)) 
    Ensure  exists (l1 l2: list(DL_Node(sortedLinkNode A))),
            l == app(l1,l2) &&
            store_sorted_dll(storeA, &(sortLinkHead->sortLink), app(l1, cons(Build_DL_Node(mksortedLinkNode(a,t), sortList), l2)))
*/
;
static inline void OsAddNode2SortLink(SortLinkAttribute *sortLinkHead, SortLinkList *sortList)
/*@ taskSpec <= highSpec
    With (a: TaskID)(t: Z)(sg: StableGlobVars)(l: list(DL_Node(sortedLinkNode TaskID)))
    Require exists pu un,
            data_at(field_addr(&(sortList->sortLinkNode),struct LOS_DL_LIST, pstPrev),struct LOS_DL_LIST *,pu) *
            data_at(field_addr(&(sortList->sortLinkNode),struct LOS_DL_LIST, pstNext),struct LOS_DL_LIST *,un) *
            store_task_sorted_dll(sg,l) *
            storesortedLinkTaskNode(task_store, sg, &(sortList->sortLinkNode), mksortedLinkNode(a,t)) && (sortLinkHead == &g_taskSortLink)
    Ensure  exists (l1 l2: list(DL_Node(sortedLinkNode TaskID))),
            l == app(l1,l2) &&
            store_task_sorted_dll(sg, app(l1, cons(Build_DL_Node(mksortedLinkNode(a,t), sortList), l2)))
*/
;
void OsAdd2SortLink(SortLinkList *node, unsigned long long startTime, unsigned long long waitTicks, SortLinkType type)
/*@ With (a: TaskID)(t g: Z)(sg: StableGlobVars)(l: list(DL_Node(sortedLinkNode TaskID)))
    Require  exists pu un,
             data_at(field_addr(&(node->sortLinkNode),struct LOS_DL_LIST, pstPrev),struct LOS_DL_LIST *,pu) *
             data_at(field_addr(&(node->sortLinkNode),struct LOS_DL_LIST, pstNext),struct LOS_DL_LIST *,un) *
             storesortedLinkTaskNode(task_store, sg, &(node->sortLinkNode), mksortedLinkNode(a,t)) * 
             store_task_sorted_dll(sg, l) && data_at(&(g_sysClock), unsigned long long, g) &&
             (startTime + (waitTicks * g/100)) <= ULLONG_MAX &&
             (startTime + (waitTicks * g/100)) >= 0 &&
             (waitTicks * g) <= ULLONG_MAX &&
             (waitTicks * g) >= 0 
    Ensure  exists (l1 l2: list(DL_Node(sortedLinkNode TaskID))),
             l == app(l1,l2) && data_at(&(g_sysClock), unsigned long long, g) && 
             store_task_sorted_dll(sg, app(l1, cons(Build_DL_Node(mksortedLinkNode(a,startTime + (waitTicks * g/100)), node), l2)))
*/
{
    /*@
    storesortedLinkTaskNode(task_store, sg, &(node->sortLinkNode), mksortedLinkNode(a,t))
    which implies
    task_store(sg, &(node->sortLinkNode), a) && node->responseTime == t 
    */
    SortLinkAttribute *sortLinkHead = &g_taskSortLink;
    ((SortLinkList *)(node))->responseTime = (startTime + (((unsigned long long)(waitTicks) * g_sysClock) / (unsigned long long)(100)));
    /*@
    task_store(sg, &(node->sortLinkNode), a)  && node->responseTime == startTime + (waitTicks * g/100)
    which implies
    storesortedLinkTaskNode(task_store, sg, &(node->sortLinkNode), mksortedLinkNode(a,startTime + (waitTicks * g/100)))
    */
    OsAddNode2SortLink(sortLinkHead, node) /*@ where (taskSpec) a = a, t = startTime + (waitTicks * g/100), sg = sg, l = l*/;
}
