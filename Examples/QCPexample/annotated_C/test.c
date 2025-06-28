#include "verification_stdlib.h"
#include "verification_list.h"
#include "safeexec_def.h"
#include "sll_def.h"


/*@ Extern Coq 
               (maketuple: list Z -> list Z ->  ((list Z) * (list Z)))
               (split_rec_rel: list Z -> list Z -> list Z -> program unit ((list Z) * (list Z)))
               (split_rel: list Z -> program unit ((list Z) * (list Z)))
               (reversepair: ((list Z) * (list Z)) -> program unit ((list Z) * (list Z)))
                */
               

int add(int x, int y)
  /*@ Require
        0 <= x && x <= 100 && 
        0 <= y && y <= 100 && emp
      Ensure
        __return == x + y && emp
   */
{
  int z;
  z = x + y;
  return z;
}


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


void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ high_level_spec <= low_level_spec
      With l X
      Require Exec(ATrue, split_rel(l), X) &&
              sll(x, l) * sll(* p, nil) * sll(* q, nil)
      Ensure exists s1 s2,
              Exec(ATrue, return(maketuple(s1, s2)), X) && 
              sll(* p, s1) * sll(* q, s2)
   */
;

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} l l1 l2 (c : ((list Z) * (list Z)) -> program unit B) X
      Require Exec(ATrue, bind(split_rec_rel(l, l1, l2), c), X) &&
              sll(x, l) * sll(* p, l1) * sll(* q, l2)
      Ensure exists s1 s2,
              Exec(ATrue, applyf(c, maketuple(s1,s2)), X) &&
              sll(* p, s1) * sll(* q, s2)
   */
;

void split_rec(struct list * x, struct list * * p, struct list * * q)
  /*@ low_level_spec
      With l l1 l2 X
      Require Exec(ATrue, split_rec_rel(l, l1, l2), X) &&
              sll(x, l) * sll(* p, l1) * sll(* q, l2)
      Ensure exists s1 s2,
              Exec(ATrue, return(maketuple(s1, s2)), X) &&
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
  /*@ exists l_new x_data, 
        Exec(ATrue, split_rec_rel(l, l1, l2), X) && l == cons(x_data, l_new) &&
        (* p) != 0 && (* p) -> data == x_data && sll((* p) -> next, l1) * sll(t,l_new)
      which implies
      Exec(ATrue, bind(split_rec_rel(l_new, l2, cons(x_data, l1)), reversepair) , X) && sll(* p, cons(x_data, l1)) * sll(t,l_new)
  */
  split_rec(t, q, p) /*@ where(low_level_spec_aux) l1 = l2, c = reversepair,  X = X; B = (list Z) * (list Z) */; 
}
