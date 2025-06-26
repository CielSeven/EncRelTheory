#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list* malloc_list(int data)
/*@ With data0 
    Require data == data0 && emp
    Ensure __return != 0 && __return -> data == data0 && __return -> next == 0
*/;

void free_list(struct list * x)
/*@ With d n 
    Require x -> data == d && x -> next == n
    Ensure emp
*/;

struct list * sll_copy(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    struct list *y, *p, *t;
    y = malloc_list(0);
    t = y;
    p = x;
    /*@ Inv t != 0 && t -> next == 0 && t -> data == 0 && lseg(x@pre,p) * listrep(p) * lseg(y, t) */
    while (p) {
      t -> data = p -> data;
      t -> next = malloc_list(0);
      p = p -> next;
      t = t -> next;
    }
    return y;
}

void sll_free(struct list * x)
/*@ Require listrep(x)
    Ensure emp
 */
{
    struct list *y;
    /*@ Inv listrep(x) */
    while (x) {
      y = x -> next;
      free_list(x);
      x = y;
    }
}

struct list *reverse(struct list *p) 
/*@ Require listrep(p)
    Ensure listrep(__return)
*/
{
   struct list * w = (void *) 0, * v = p;
   /*@ Inv listrep(w) * listrep(v) */
   while (v) {
      struct list * t = v -> next;
      v -> next = w;
      w = v;
      v = t;
   }
   return w;
}

struct list * append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == (struct list*) 0) {
        return y;
    } else {
        t = x;
        u = t->next;
        /*@ Inv  exists w, t != 0 && 
            data_at(field_addr(t, next), u) * 
            data_at(field_addr(t, data), w) *
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->next;
        }
        t->next = y;
        return x;
    }
}

struct list *merge(struct list *x , struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *z, *t;
    if (x == 0) {
      return y; 
    }
    else {
      z = x;
      t = y;
      /*@ Inv y == t && x != 0 && lseg(z , x) * listrep(x) * listrep(y) */
      while (y) {
        t = y -> next;
        y -> next = x -> next;
        x -> next = y;
        if (y -> next == 0) {
          y -> next = t;
          return z;
        }
        else {
          x = y -> next;
          y = t;
        }
      }
    }
    
    return z;
}


struct list *multi_append(struct list *x, struct list *y, struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == 0) {
        t = append(y , z);
        return t;
    } else {
        t = x;
        u = t->next;
        /*@ Inv exists v, t != 0 &&
            data_at(field_addr(t, data), v) * 
            data_at(field_addr(t, next), u) * 
            listrep(y) *
            listrep(z) * 
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            if (y) {
              t -> next = y;
              t = y;
              y = y -> next;
              t -> next = u;
              t = u;
              u = u -> next;
            }
            else {
              u = append(u , z);
              t -> next = u;
              return x;   
            }
        }
        t->next = append(y,z);
        return x;
    }
}