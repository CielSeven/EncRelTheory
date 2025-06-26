#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"

/*@ Extern Coq (count: list Z -> Z -> Z)
 */

int length(struct list *p)
/*@ With (l: list Z)
    Require sll(p, l) && Zlength(l) <= 2147483647
    Ensure __return == Zlength(l) && sll(p@pre, l)
*/
{
   int n = 0;
   /*@ Inv exists l1 l2,
            l == app(l1, l2) &&
            n == Zlength(l1) &&
            sllseg(p@pre, p, l1) * sll(p, l2)
      */
   while (p) {
      /*@ exists l2, p != 0 && sll(p, l2)
          which implies
          exists l3, l2 == cons(p -> data, l3) && sll(p -> next, l3)
      */
      n++;
      p = p -> next;
   }
   return n;
}

struct list *reverse(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
   /*@ Inv exists l1 l2,
            l == app(rev(l1), l2) && 
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
      /*@ exists l2, v != 0 && sll(v, l2)
          which implies
          exists l2_new, l2 == cons(v -> data, l2_new) && sll(v -> next, l2_new)
      */
      struct list * t = v -> next;
      v -> next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_alter_style1(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
   /*@ Inv exists l1 l2,
            l == app(rev(l1), l2) && 
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
      /*@ exists l2, v != 0 && sll(v, l2)
          which implies
          exists x xs vn,
            l2 == cons(x, xs) &&
            v -> data == x &&
            v -> next == vn && sll(vn, xs)
      */
      struct list * t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_alter_style2(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list * w = (void *) 0, * v = p;
   /*@ Inv exists l1 l2 w_inv v_inv,
            l == app(rev(l1), l2) &&
            data_at(&w, w_inv) *
            data_at(&v, v_inv) *
            sll(w_inv, l1) *
            sll(v_inv, l2)
      */
   while (v) {
      /*@ exists v_inv l2,
            v_inv != 0 &&
            data_at(&v, v_inv) *
            sll(v_inv, l2)
          which implies
          exists x xs v_inv_next,
            l2 == cons(x, xs) &&
            data_at(&v, v_inv) *
            data_at(&(v_inv -> data), x) *
            data_at(&(v_inv -> next), v_inv_next) *
            sll(v_inv_next, xs)
      */
      struct list * t = v -> next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *reverse_alter_style3(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list *w;
   struct list *v;
   w = (void *)0;
   /*@ sll(w, nil) */
   v = p;
   /*@ Assert w == 0 && v == p && p == p@pre && sll(w, nil) * sll(v, l) */
   /*@ Inv Assert exists l1 l2,
            p == p@pre && l == app(rev(l1), l2) && 
            sll(w, l1) * sll(v, l2)
      */
   while (v) {
      /*@ exists l2, v != 0 && sll(v, l2)
          which implies
          exists l2_new, l2 == cons(v -> data, l2_new) && sll(v -> next, l2_new)
      */
      struct list *t;
      t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list *append(struct list *x, struct list *y)
/*@ With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
*/
{
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
    /*@ x != 0 && sll(x, l1)
        which implies
        exists l1n, l1 == cons(x -> data, l1n) && sll(x -> next, l1n) */
    t = x;
    u = t -> next;
    /*@ Inv
          exists l1a l1b,
            app(l1a, cons(t -> data, l1b)) == l1 &&
            t != 0 && t -> next == u &&
            sllseg(x, t, l1a) *
            sll(u, l1b) * sll(y, l2)
    */
    while (u != (void *)0) {
      /*@ exists l1b, u != 0 && sll(u, l1b)
          which implies 
          exists l1b_new, l1b == cons(u->data, l1b_new) && sll(u->next, l1b_new) */
      t = u;
      u = t -> next;
    }
    t -> next = y;
    return x;
  }
}

struct list *append_long(struct list *x, struct list *y)
/*@ With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
*/
{
  struct list *t, *u;
  if (x == (void *)0) {
    return y;
  } else {
    /*@ x != 0 && sll(x, l1)
        which implies
        exists a l1b xn, l1 == cons(a, l1b) && x -> data == a && x -> next == xn && sll(xn, l1b) */
    u = x -> next;
    if (u == (void *)0) {
      x -> next = y;
      return x;
    }
    t = x;
    u = t -> next;
    /*@ Inv
          exists l1a b l1c,
            app(l1a, cons(b, l1c)) == l1 &&
            t -> data == b &&
            t -> next == u &&
            t != 0 &&
            sllseg(x, t, l1a) *
            sll(u, l1c) * sll(y, l2)
    */
    while (u != (void *)0) {
      /*@ exists l1cd, u != 0 && sll(u, l1cd)
          which implies 
          exists c l1d un, l1cd == cons(c, l1d) && u->data == c && u->next == un && sll(un, l1d) */
      t = u;
      u = t -> next;
    }
    t -> next = y;
    return x;
  }
}

struct list *append_2p(struct list *x, struct list *y)
/*@ With l1 l2
    Require sll(x, l1) * sll(y, l2)
    Ensure sll(__return, app(l1, l2))
*/
{
  struct list * * pres = & x, * * pt = pres;
  /*@ Inv
        exists l1a l1b,
            app(l1a, l1b) == l1 &&
            pres == &x &&
            sllbseg(pres, pt, l1a) *
            sll(* pt, l1b) * sll(y, l2)
    */
  while (* pt) {
    pt = &((* pt) -> next);
  }
  * pt = y;
  /*@ exists l1a, ((* pt) == y) && sllbseg(pres, pt, l1a)
      which implies
      sllseg(*pres, y, l1a) && pt == pt
   */
  return * pres;
}