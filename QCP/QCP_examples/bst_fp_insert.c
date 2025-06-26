#include "verification_stdlib.h"
#include "bst_fp_def.h"

struct tree * malloc_tree_node()
  /*@ Require emp
      Ensure __return != 0 &&
             undef_data_at(&(__return -> key)) *
             undef_data_at(&(__return -> value)) *
             undef_data_at(&(__return -> left)) *
             undef_data_at(&(__return -> right)) *
             undef_data_at(&(__return -> father))
   */;

void insert(struct tree **b, int x, int value)
  /*@ high_level_spec <= low_level_spec
      With m
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_map(* b, m)
      Ensure
        store_map(* b, map_insert(x, value, m))
   */
;

void insert(struct tree **b, int x, int value)
  /*@ low_level_spec
      With tr
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_tree(* b, 0, tr)
      Ensure
        store_tree(* b, 0, tree_insert(x, value, tr))
   */
{
  struct tree * fa = (void *) 0;
  /*@ Inv
        exists pt0 tr0,
          combine_tree(pt0, tree_insert(x@pre, value@pre, tr0)) ==
            tree_insert(x@pre, value@pre, tr) &&
          store_ptb(b, b@pre, fa, 0, pt0) * store_tree(* b, fa, tr0)
   */
  while (1) {
    if (* b == (void *)0) {
      * b = malloc_tree_node();
      (* b) -> key = x;
      (* b) -> value = value;
      (* b) -> left = (void *)0;
      (* b) -> right = (void *)0;
      (* b) -> father = fa;
      return;
    } else {
      /*@ exists tr0, * b != 0 && store_tree(* b, fa, tr0)
          which implies
          exists l0 r0,
            INT_MIN <= (* b) -> key && (* b) -> key <= INT_MAX &&
            (* b) -> father == fa &&
            tr0 == make_tree(l0, (* b) -> key, (* b) -> value, r0) &&
            store_tree((* b) -> left, * b, l0) *
            store_tree((* b) -> right, * b, r0) */
      if (x < (* b) -> key) {
        fa = * b;
        b = &((* b) -> left);
      } else if ((* b) -> key < x) {
        fa = * b;
        b = &((* b) -> right);
      } else {
        (* b) -> value = value;
        return;
      }
    }
  }
}

