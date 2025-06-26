struct list {
   int data;
   struct list *next;
};

/*@ Extern Coq (listrep : Z -> Assertion)
               (lseg: Z -> Z -> Assertion)
               (listboxseg: Z -> Z -> Assertion)
               (sll_tag : Z -> Prop)
 */

/*@ Import Coq Require Import sll_shape_lib */

/*@ include strategies "sll_shape.strategies" */
