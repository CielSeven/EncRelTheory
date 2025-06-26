#include "verification_stdlib.h"
#include "verification_list.h"
#include "dll_shape_def.h"

struct dlist* malloc_dlist(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0 && __return -> prev == 0
*/;

void free_dlist(struct dlist * x)
/*@ With d n 
    Require x -> data == d && x -> next == n && x -> prev == 0
    Ensure emp
*/;

struct dlist * dll_copy(struct dlist * x)
/*@ Require dlistrep(x, 0)
    Ensure  dlistrep(__return, 0) * dlistrep(x, 0)
 */
{
    struct dlist *y, *p, *t;
    y = malloc_dlist(0);
    t = y;
    p = x;
    /*@ Inv exists p_prev, 
            t != 0 && t -> next == 0 && t -> data == 0 && t->prev == 0 && dllseg(x@pre,0, p_prev,p) * dlistrep(p, p_prev) * dllseg(y, 0, 0, t) */
    while (p) {
      t -> data = p -> data;
      t -> prev = p -> prev;
      t -> next = malloc_dlist(0);
      p = p -> next;
      t = t -> next;
    }
    return y;
}

void dll_free(struct dlist * x)
/*@ Require dlistrep(x, 0)
    Ensure emp
 */
{
    struct dlist *y;
    /*@ Inv exists prev, dlistrep(x, prev) */
    while (x) {
      y = x -> next;
      free_dlist(x);
      x = y;
    }
}

struct dlist *reverse(struct dlist *p)
/*@ Require dlistrep(p, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct dlist *w, *t, *v;
    w = (void *)0;
    v = p;
    /*@ Inv dlistrep(w, v) *
        dlistrep(v, w)
     */
    while (v) {
        t = v->next;
        v->next = w;
        v->prev = t;
        w = v;
        v = t;
    }
    return w;
}

struct dlist * append(struct dlist * x, struct dlist * y)
/*@ Require dlistrep(x, 0) * dlistrep(y, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct dlist *t, *u;
    if (x == 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ Inv u == t->next &&
            dlistrep(y, 0) *
            dlistrep(u, t) *
            dllseg(x, 0, t->prev, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        if (y) {
            y->prev = t;
        }
        return x;
    }
}

struct dlist *iter(struct dlist *l)
/*@ 
    Require dlistrep(l, 0)
    Ensure  dlistrep(__return, 0)
 */
{
    struct dlist *p;
    p = l;
    /*@ Inv exists p_prev,
          dllseg(l@pre, 0, p_prev, p) *
          dlistrep(p, p_prev)
     */
    while (p) {
        p = p->next;
    }
    return l;
}

struct dlist *iter_back(struct dlist *l, struct dlist *head)
/*@ With l_prev
	  Require dllseg(head, 0, l_prev, l) * dlistrep(l, l_prev)
    Ensure  dlistrep(__return, 0)
 */
{
    struct dlist *p;
    if (l == 0) {
      return head;
    }
  	else {
    	p = l;
      /*@ Inv dllseg(head@pre, 0, p->prev, p) * dlistrep(p->next , p)*/
    	while (p != head) {
      	  p = p -> prev; 
      }
    }
    return p;
}