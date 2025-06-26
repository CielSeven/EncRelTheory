#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"

/*@ Import Coq Require Import sll_merge_lib */

/*@ Extern Coq (merge_rel: list Z -> list Z -> list Z -> Prop)
               (merge_steps: list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
               (split_rec_rel: list Z -> list Z -> list Z -> list Z -> list Z -> Prop)
               (merge_sort_rel: list Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop)
               (increasing: list Z -> Prop)
 */

struct list *merge(struct list *x, struct list *y)
/*@ With s1 s2
    Require sll(x, s1) * sll(y, s2)
    Ensure exists s3, merge_rel(s1, s2, s3) && sll(__return, s3)
*/
{
  struct list *ret, **t = &ret;
  /*@ Inv
    exists l1 l2 l3,
      merge_steps(s1, s2, nil, l1, l2, l3) &&
      sll(x, l1) * sll(y, l2) *
      undef_data_at(t, struct list*) * sllbseg(&ret, t, l3)
  */
  while (1)
  {
    if (x == (void *)0) {
      *t = y;
      break;
    }
    if (y == (void *)0) {
      *t = x;
      break;
    }
    /*@ exists l1, x != 0 && sll(x, l1)
        which implies 
        exists l1_new, l1 == cons(x->data, l1_new) && sll(x->next, l1_new)
    */
    /*@ exists l2, y != 0 && sll(y, l2)
        which implies 
        exists l2_new, l2 == cons(y->data, l2_new) && sll(y->next, l2_new)
    */
    if (x->data < y->data) {
      *t = x;
      t = &(x->next);
      x = x->next;
    } else {
      *t = y;
      t = &(y->next);
      y = y->next;
    }
  }
  /*@
    exists u l3, data_at(t, struct list*, u) * sllbseg(&ret, t, l3)
    which implies
    t == t && sllseg(ret, u, l3)
  */
  return ret;
}

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ With l l1 l2
      Require sll(x, l) * sll(* p, l1) * sll(* q, l2)
      Ensure exists s1 s2,
              split_rec_rel(l, l1, l2, s1, s2) &&
              sll(* p, s1) * sll(* q, s2)
  */
{
  if (x == (void *)0) {
    return;
  }
  /*@ exists l, x != 0 && sll(x, l)
      which implies
      exists l_new, l == cons(x->data, l_new) && sll(x->next, l_new)
  */
  struct list * t;
  t = x -> next;
  x -> next = * p;
  * p = x;
  /*@ exists x_data l1,
        (* p) != 0 && (* p) -> data == x_data && sll((* p) -> next, l1)
      which implies
      sll(* p, cons(x_data, l1))
  */
  split_rec(t, q, p);
}

struct list * merge_sort(struct list * x)
  /*@ high_level_spec <= low_level_spec
      With l
      Require sll(x, l)
      Ensure exists l0,
              Permutation(l, l0) && increasing(l0) &&
              sll(__return, l0)
   */
;

struct list * merge_sort(struct list * x)
  /*@ low_level_spec
      With l
      Require sll(x, l)
      Ensure exists l0,
              merge_sort_rel(l, l0) &&
              sll(__return, l0)
  */
{
  struct list * p, * q;
  p = (void *)0;
  /*@ p == 0 && emp
      which implies
      sll(p, nil) */
  q = (void *)0;
  /*@ q == 0 && emp
      which implies
      sll(q, nil) */
  split_rec(x, &p, &q);
  if (q == (void *)0) {
    return p;
  }
  /*@ exists l1, q != 0 && sll(q, l1)
      which implies
      l1 != nil && sll(q, l1) */
  p = merge_sort(p);
  q = merge_sort(q);
  return merge(p, q);
}


/* malloc version */

struct list **malloc_list_2p()
    /*@ Require emp
        Ensure exists p, data_at(__return, struct list*, p)
    */
    ;

void free_list_2p(struct list **p)
    /*@ Require exists q, data_at(p, struct list*, q)
        Ensure emp
    */
    ;

struct list *merge_malloc(struct list *x, struct list *y)
/*@ With s1 s2
    Require sll(x, s1) * sll(y, s2)
    Ensure exists s3, merge_rel(s1, s2, s3) && sll(__return, s3)
*/
{
  struct list **pret, **t, *ret;
  ret = (void*) 0;
  pret = malloc_list_2p();
  t = pret;
  /*@ Inv
    exists l1 l2 l3 u,
      merge_steps(s1, s2, nil, l1, l2, l3) &&
      sll(x, l1) * sll(y, l2) *
      data_at(t, struct list*, u) * sllbseg(pret, t, l3)
  */
  while (1)
  {
    if (x == (void *)0) {
      *t = y;
      break;
    }
    if (y == (void *)0) {
      *t = x;
      break;
    }
    /*@ exists l1 l2, x != 0 && y != 0 && sll(x, l1) * sll(y, l2)
        which implies 
        exists l1_new l2_new,
          l1 == cons(x->data, l1_new) && l2 == cons(y->data, l2_new) &&
          sll(x->next, l1_new) * sll(y->next, l2_new)
    */
    if (x->data < y->data) {
      *t = x;
      t = &(x->next);
      x = x->next;
    } else {
      *t = y;
      t = &(y->next);
      y = y->next;
    }
  }
  /*@
    exists u l3, data_at(t, struct list*, u) * sllbseg(pret, t, l3)
    which implies
    exists r, t == t && data_at(pret, struct list*, r) * sllseg(r, u, l3)
  */
  ret = *pret;
  free_list_2p(pret);
  return ret;
}
