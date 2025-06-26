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

struct tree * insert(struct tree * b, int x, int value)
  /*@ high_level_spec <= low_level_spec
      With m
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_map(b, m)
      Ensure
        store_map(__return, map_insert(x, value, m))
   */
;

struct tree * insert(struct tree * b, int x, int value)
  /*@ low_level_spec
      With tr
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_tree(b, tr)
      Ensure
        store_tree(__return, tree_insert(x, value, tr))
   */
{
  if (b == (void *)0) {
    b = malloc_tree_node();
    b -> key = x;
    b -> value = value;
    b -> left = (void *)0;
    b -> right = (void *)0;
    return b;
  }
  /*@ exists tr0, b != 0 && store_tree(b, tr0)
        which implies
        exists l0 r0,
          INT_MIN <= b -> key && b -> key <= INT_MAX &&
          tr0 == make_tree(l0, b -> key, b -> value, r0) &&
          store_tree(b -> left, l0) *
          store_tree(b -> right, r0) */
  if (x < b -> key) {
    b -> left = insert(b -> left, x, value);
    return b;
  } else if (b -> key < x) {
    b -> right = insert(b -> right, x, value);
    return b;
  } else {
    b -> value = value;
    return b;
  }
}

