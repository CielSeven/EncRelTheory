#include "verification_stdlib.h"
#include "verification_list.h"
#include "poly_sll_def.h"

struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/
{
   struct list *w = (void *)0, *v = p;
   /*@ Inv exists l1 l2,
            l == app(rev(l1), l2) && 
            sll(storeA, w, l1) * sll(storeA, v, l2)
      */
   while (v) {
      /*@ exists l2, v != 0 && sll(storeA, v, l2)
          which implies 
          exists x xs, l2 == cons(x, xs) && storeA(v->data, x) * sll(storeA, v->next, xs)
      */
      struct list *t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}
