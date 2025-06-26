#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_queue_def.h"

struct list * malloc_list_cell()
  /*@ Require emp
      Ensure __return != 0 &&
             data_at(&(__return -> next), 0) *
             data_at(&(__return -> prev), 0) *
             data_at(&(__return -> data), 0)
   */
  ;

void free_list_cell(struct list * p)
  /*@ Require exists x y z, p -> next == x && p -> prev == y && 
             p -> data == z && emp
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
      dllseg(q -> head, 0, 0, q -> tail, l) */
  struct list * p = malloc_list_cell();
  p -> data = x;
  if (q -> head == (void *)0) {
    q -> head = p;
    q -> tail = p;
    p -> next = (void *)0;
    p -> prev = (void *)0;
  }
  else {
    /*@ q -> head != 0 && dllseg(q -> head, 0, 0, q -> tail, l)
        which implies
        exists l0,
          q -> tail != 0 &&
          l == app(l0, cons(q -> tail -> data, nil)) &&
          q -> tail -> next == 0 &&
          dllseg(q -> head, q -> tail, 0, q -> tail -> prev, l0) */
    q -> tail -> next = p;
    p -> prev = q -> tail;
    q -> tail = p;
    p -> next = (void *)0;
  }
}

int dequeue(struct queue * q)
  /*@ With x l
      Require store_queue(q, cons(x, l))
      Ensure __return == x && store_queue(q, l)
   */
{
  /*@ store_queue(q, cons(x, l))
      which implies
      q -> head -> prev == 0 &&
      q -> head -> data == x &&
      dllseg(q -> head -> next, 0, q -> head, q -> tail, l)
   */
  struct list * p = q -> head;
  int x0 = p -> data;
  q -> head = p -> next;
  free_list_cell(p);
  if (q -> head == (void *)0) {
    q -> tail = (void *)0;
  }
  else {
    /*@ q -> head != 0 && dllseg(q -> head, 0, p, q -> tail, l)
        which implies
        exists l0,
          l == cons(q -> head -> data, l0) &&
          q -> head -> prev == p &&
          dllseg(q -> head -> next, 0, q -> head, q -> tail, l0)
        */
    q -> head -> prev = (void *)0;
  }
  return x0;
}
