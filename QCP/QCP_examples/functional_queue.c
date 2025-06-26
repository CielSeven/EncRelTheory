#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "functional_queue_def.h"

struct list * malloc_list_cell()
  /*@ Require emp
      Ensure __return != 0 &&
             __return -> next == 0 &&
             __return -> data == 0 && emp
   */
  ;

void free_list_cell(struct list * p)
  /*@ Require exists x y, p -> next == x && p -> data == y && emp
      Ensure emp
   */
  ;

struct list *reverse(struct list *p) 
  /*@ With (l: list Z)
      Require sll(p, l)
      Ensure sll(__return, rev(l))
   */
  ;

void push(struct list * * p, int x)
/*@ With l
    Require sll(* p, l)
    Ensure sll(* p, cons(x, l))
 */
{
  struct list * px = malloc_list_cell();
  px -> data = x;
  px -> next = * p;
  * p = px;
}

int pop(struct list * * p)
/*@ With x l
    Require sll(* p, cons(x, l))
    Ensure __return == x && sll(* p, l)
 */
{
  struct list * px = * p;
  int x0 = px -> data;
  * p = px -> next;
  free_list_cell(px);
  return x0;
}

void enqueue(struct queue * q, int x)
/*@ With l
    Require store_queue(q, l)
    Ensure store_queue(q, app(l, cons(x, nil)))
 */
{
  /*@ store_queue(q, l)
      which implies
      exists l1 l2,
        l == app(l1, rev(l2)) &&
        sll(q -> l1, l1) *
        sll(q -> l2, l2) */
  push(&(q -> l2), x);
}

int dequeue(struct queue * q)
/*@ With x l
    Require store_queue(q, cons(x, l))
    Ensure __return == x && store_queue(q, l)
 */
{
  /*@ store_queue(q, cons(x, l))
      which implies
      exists l1 l2,
        cons(x, l) == app(l1, rev(l2)) &&
        sll(q -> l1, l1) *
        sll(q -> l2, l2) */
  if (q -> l1 == (void *) 0) {
    q -> l1 = reverse(q -> l2);
    q -> l2 = (void *) 0;
    /*@ exists [rev_l2],
          cons(x, l) == rev_l2 &&
          sll(q -> l1, rev_l2)
        which implies
        sll(q -> l1, cons(x, l)) */
  }
  else {
    /*@ exists l1, q -> l1 != 0 && sll(q -> l1, l1)
        which implies
        exists z l1_tail,
          l1 == cons(z, l1_tail) &&
          sll(q -> l1, cons(z, l1_tail))
     */
  }
  return pop(&(q -> l1));
}
