#include "verification_stdlib.h"

/*@ Import Coq Require Import swap_lib */

/*@ Extern Coq (swap_para :: *) */
/*@ Extern Coq (swap_eq_para : Z -> swap_para)
               (swap_neq_para : Z -> Z -> swap_para)
               (swap_pre : Z -> Z -> swap_para -> Assertion)
               (swap_post : Z -> Z -> swap_para -> Assertion) */


void swap(int * px, int * py)
/*@ all
    With para
    Require swap_pre(px, py, para)
    Ensure swap_post(px, py, para)
*/;

void swap(int * px, int * py)
/*@ neq <= all
    With x y
    Require x == *px && y == *py
    Ensure  y == *px && x == *py
*/;

void swap(int * px, int * py)
/*@ eq <= all
    With x
    Require px == py && x == *px
    Ensure  x == *py
*/;

void swap(int * px, int * py)
/*@ all */
{
  /*@ Assert (exists x y, x == * px@pre && y == * py@pre &&
                          px == px@pre && py == py@pre &&
                          para == swap_neq_para(x, y)) ||
             (exists x, px == py && x == * px &&
                        px == px@pre && px@pre == py@pre &&
                        para == swap_eq_para(x)) */
  int t;
  t = * px;
  * px = * py;
  * py = t;
}

void swap_test1(int *x, int *y) 
/*@ 
   Require x != y && *x == 1 && *y == 2
   Ensure  *y == 1 && *x == 2
*/
{
  swap(x, y) /*@ where (neq) */;
}

void swap_test2(int *x, int *y) 
/*@ 
   Require x == y && *x == 1
   Ensure  *y == 1
*/
{
  swap(x, y) /*@ where (eq) */;
}