#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"
#include "sll_queue_def.h"

struct list * malloc_list_cell()
  /*@ Require emp
      Ensure __return != 0 &&
             __return -> next == 0 &&
             __return -> data == 0
   */
  ;

void free_list_cell(struct list * p)
  /*@ Require exists x y, p -> next == x && p -> data == y && emp
      Ensure emp
   */
  ;

struct queue * malloc_queue_cell()
  /*@ Require emp
      Ensure __return != 0 &&
             __return -> head == 0 &&
             __return -> tail == 0
   */
  ;

void free_queue_cell(struct queue * p)
  /*@ Require exists x y, p -> head == x && p -> tail == y && emp
      Ensure emp
   */
  ;

void enqueue(struct queue * q, int x)
/*@ With l
    Require store_queue(q, l)
    Ensure store_queue(q, app(l, cons(x, nil)))
 */
{
  /*@ store_queue(q, l)
      which implies
      exists u v,
        q -> tail != 0 &&
        q -> tail -> data == u &&
        q -> tail -> next == v &&
        sllseg(q -> head, q -> tail, l) */
  struct list * p;
  p = malloc_list_cell();
  q -> tail -> data = x;
  q -> tail -> next = p;
  q -> tail = p;
}

int dequeue(struct queue * q)
/*@ With x l
    Require store_queue(q, cons(x, l))
    Ensure __return == x && store_queue(q, l)
 */
{
  /*@ store_queue(q, cons(x, l))
      which implies
      exists u v,
        q -> tail != 0 &&
        q -> tail -> data == u &&
        q -> tail -> next == v &&
        q -> head -> data == x &&
        sllseg(q -> head -> next, q -> tail, l) */
  int x0;
  struct list * p;
  p = q -> head;
  x0 = p -> data;
  q -> head = p -> next;
  free_list_cell(p);
  return x0;
}

struct queue * init_empty_queue()
/*@ Require emp
    Ensure store_queue(__return, nil)
 */
{
  struct queue * q;
  q = malloc_queue_cell();
  q -> head = malloc_list_cell();
  q -> tail = q -> head;
  return q;
}
