#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"

/*@ Import Coq Require Import sll_insert_sort_lib */

/*@ Extern Coq (Permutation: list Z -> list Z -> Prop)
               (increasing: list Z -> Prop)
               (insert: Z -> list Z -> list Z)
               (strict_upperbound: Z -> list Z -> Prop)
 */

struct list * insertion(struct list * p, struct list * node)
  /*@ With l a
      Require node != 0 && node->data == a && 
              sll(p, l) * 
              undef_data_at(&(node->next), struct list*) 
      Ensure exists l0,
              l0 == insert(a, l) && sll(__return, l0)
   */
{
  struct list * res = p;
  struct list * * p2 = & res;
  /*@ Inv
    exists l1 l2,
      node == node@pre &&
      l == app(l1, l2) &&
      node->data == a &&
      strict_upperbound(a, l1) &&
      sllbseg(&res, p2, l1) * sll(*p2, l2) *
      undef_data_at(&(node->next), struct list*)
  */
  while (* p2 != (void * )0 && (* p2) -> data < node -> data) {
    /*@ exists l2, *p2 != 0 && sll(*p2, l2)
        which implies 
        exists l3, l2 == cons((*p2)->data, l3) && sll((*p2)->next, l3)
    */
    p2 = &((* p2) -> next);
  }
  node -> next = * p2;
  * p2 = node;
  /*@ exists l1, ((* p2) == node) && sllbseg(&res, p2, l1)
      which implies
      sllseg(res, node, l1) && p2 == p2
   */
  return res;
}

struct list * insertion_sort(struct list * x)
  /*@ With l
      Require sll(x, l)
      Ensure exists l0,
               Permutation(l, l0) && increasing(l0) &&
               sll(__return, l0)
   */
{
  struct list * res = (void *)0, * p = x, * q;
  /*@ Inv
    exists l0 l1 l2,
      l == app(l1, l2) &&
      Permutation(l1, l0) && increasing(l0) &&
      sll(res, l0) * sll(p, l2)
  */
  while (p != (void * )0) {
    /*@ exists l2, p != 0 && sll(p, l2)
        which implies 
        exists l3, l2 == cons(p->data, l3) && sll(p->next, l3)
    */
    q = p -> next;
    res = insertion(res, p);
    p = q;
  }
  return res;
}
