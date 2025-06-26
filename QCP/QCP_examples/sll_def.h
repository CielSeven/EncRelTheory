struct list {
   int data;
   struct list *next;
};

/*@ Extern Coq (sll : Z -> list Z -> Assertion)
               (sllseg: Z -> Z -> list Z -> Assertion)
               (sllbseg: Z -> Z -> list Z -> Assertion)
 */

/*@ Import Coq Require Import sll_lib */

/*@ include strategies "sll.strategies" */