#include "bst_def.h"
#include "verification_stdlib.h"

struct tree * malloc_tree_node()
  /*@ Require emp
      Ensure __return != 0 &&
             undef_data_at(&(__return -> key)) *
             undef_data_at(&(__return -> value)) *
             undef_data_at(&(__return -> left)) *
             undef_data_at(&(__return -> right))
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
        store_tree(* b, tr)
      Ensure
        store_tree(* b, tree_insert(x, value, tr))
   */
{
  /*@ Inv
        exists pt0 tr0,
          combine_tree(pt0, tree_insert(x@pre, value@pre, tr0)) ==
            tree_insert(x@pre, value@pre, tr) &&
          store_ptb(b, b@pre, pt0) * store_tree(* b, tr0)
   */
  while (1) {
    struct tree *p;
    p = *b;
    if (p == (void *)0) {
      p = malloc_tree_node();
      p->key = x;
      p->value = value;
      p->left = (void *)0;
      p->right = (void *)0;
      *b = p;
      return;
    } else {
      /*@ exists tr0, p != 0 && store_tree(p, tr0)
          which implies
          exists l0 r0,
            INT_MIN <= p -> key && p -> key <= INT_MAX &&
            tr0 == make_tree(l0, p -> key, p -> value, r0) &&
            store_tree(p -> left, l0) *
            store_tree(p -> right, r0) */
      int y;
      y = p->key;
      if (x < y) {
        b = &p->left;
      } else if (y < x) {
        b = &p->right;
      } else {
        p->value = value;
        return;
      }
    }
  }
}

