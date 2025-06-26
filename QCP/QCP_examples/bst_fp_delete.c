#include "verification_stdlib.h"
#include "bst_fp_def.h"


void free_tree_node(struct tree *b)
  /*@ Require
        exists k v f l r, b -> key == k &&
        b -> value == v && b -> father == f &&
        b -> left == l && b -> right == r && emp 
      Ensure emp
  */
;

void replace_min(struct tree ** b, struct tree * ptr)
/*@ With tr k v
    Require
      ptr != 0 && ptr -> key == k && ptr -> value == v &&
      INT_MIN <= ptr -> key && ptr -> key <= INT_MAX &&
      (* b) != 0 && store_tree(* b, ptr, tr)
    Ensure
      ptr -> key == min_key(k, tr) && ptr -> value == min_value(v, tr) &&
      INT_MIN <= ptr -> key && ptr -> key <= INT_MAX &&
      store_tree(* b, ptr, delete_min(tr))
*/
{
  struct tree * fa = ptr;
  /*@ Inv
        exists pt0 tr0,
        tr == combine_tree(pt0, tr0) && min_key(k, tr) == min_key(k, tr0) &&
        min_value(v, tr) == min_value(v, tr0) && (* b) != 0 &&
        delete_min(tr) == combine_tree(pt0, delete_min(tr0)) &&
        store_ptb(b, b@pre, fa, ptr@pre, pt0) * store_tree(* b, fa, tr0)
  */
  while(1) {
    /*@ exists tr0,
            (* b) != 0 && store_tree(* b, fa, tr0)
          which implies
          exists l0 r0,
            INT_MIN <= (* b) -> key && (* b) -> key <= INT_MAX &&
            (* b) -> father == fa &&
            tr0 == make_tree(l0, (* b) -> key, (* b) -> value, r0) &&
            store_tree((* b) -> left, * b, l0) *
            store_tree((* b) -> right, * b, r0)
    */
    if((* b) -> left != (void *) 0) {
      fa = * b;
      b = &((* b) -> left);
    } else {
      struct tree * to_free = (* b);
      if((* b) -> right != (void *) 0) {
        /*@ exists tr0, (* b) -> right != 0 && store_tree((* b) -> right, * b, tr0)
            which implies
            exists l0 r0,
            INT_MIN <= (* b) -> right -> key && (* b) -> right -> key <= INT_MAX &&
            tr0 == make_tree(l0, (* b) -> right -> key, (* b) -> right -> value, r0) &&
            (* b) -> right -> father == (* b) &&
            store_tree((* b) -> right -> left, (* b) -> right, l0) *
            store_tree((* b) -> right -> right, (* b) -> right, r0)
        */
        (* b) -> right -> father = (* b) -> father;
      }
      ptr -> key = (* b) -> key;
      ptr -> value = (* b) -> value;
      (* b) = (* b) -> right;
      free_tree_node(to_free);
      return;
    }
  }
}

void Delete(struct tree **b, int x)
  /*@ high_level_spec <= low_level_spec
      With m
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_map(* b, m)
      Ensure
        store_map(* b, map_delete(x, m))
  */
;

void Delete(struct tree **b, int x)
  /*@ low_level_spec
      With tr
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_tree(* b, 0, tr)
      Ensure
        store_tree(* b, 0, tree_delete(x, tr))
  */
{
  struct tree * fa = (void *) 0;
  /*@ Inv
        exists pt0 tr0,
          combine_tree(pt0, tree_delete(x@pre, tr0)) ==
            tree_delete(x@pre, tr) &&
          store_ptb(b, b@pre, fa, 0, pt0) * store_tree(* b, fa, tr0)
  */
  while (1) {
    if (* b != (void *)0) {
      /*@ exists tr0, * b != 0 && store_tree(* b, fa, tr0)
          which implies
          exists l0 r0,
          INT_MIN <= (* b) -> key && (* b) -> key <= INT_MAX &&
          (* b) -> father == fa &&
          tr0 == make_tree(l0, (* b) -> key, (* b) -> value, r0) &&
          store_tree((* b) -> left, * b, l0) *
          store_tree((* b) -> right, * b, r0)
      */
      if (x < (* b) -> key) {
        fa = * b;
        b = &((* b) -> left);
      } else if ((* b) -> key < x) {
        fa = * b;
        b = &((* b) -> right);
      } else if ((* b) -> right == (void *)0) {
        struct tree * to_free = (* b);
        if((* b) -> left != (void *)0) {
          /*@ exists tr0, ((* b) -> left) != 0 && store_tree((* b) -> left, * b, tr0)
              which implies
              exists l0 r0,
              INT_MIN <= (* b) -> left -> key && (* b) -> left -> key <= INT_MAX &&
              (* b) -> left -> father == (* b) &&
              tr0 == make_tree(l0, (* b) -> left -> key, (* b) -> left -> value, r0) &&
              store_tree((* b) -> left -> left, (* b) -> left, l0) *
              store_tree((* b) -> left -> right, (* b) -> left, r0)
          */
          (* b) -> left -> father = fa;
        }
        (* b) = (* b) -> left;
        free_tree_node(to_free);
        return;
      } else if ((* b) -> left == (void *)0) {
        struct tree * to_free = (* b);
        if((* b) -> right != (void *)0) {
          /*@ exists tr0, ((* b) -> right) != 0 && store_tree((* b) -> right, * b, tr0)
              which implies
              exists l0 r0,
              INT_MIN <= (* b) -> right -> key && (* b) -> right -> key <= INT_MAX &&
              (* b) -> right -> father == (* b) &&
              tr0 == make_tree(l0, (* b) -> right -> key, (* b) -> right -> value, r0) &&
              store_tree((* b) -> right -> left, (* b) -> right, l0) *
              store_tree((* b) -> right -> right, (* b) -> right, r0)
          */
          (* b) -> right -> father = fa;
        }
        (* b) = (* b) -> right;
        free_tree_node(to_free);
        return;
      } else {
        /*@ exists tr0, ((* b) -> right) != 0 && store_tree((* b) -> right, * b, tr0)
            which implies
            exists l0 r0,
            INT_MIN <= (* b) -> right -> key && (* b) -> right -> key <= INT_MAX &&
            (* b) -> right -> father == (* b) &&
            tr0 == make_tree(l0, (* b) -> right -> key, (* b) -> right -> value, r0) &&
            store_tree((* b) -> right -> left, (* b) -> right, l0) *
            store_tree((* b) -> right -> right, (* b) -> right, r0)
        */
        replace_min(&((* b) -> right), * b);
        return;
      }
    } else {
      return;
    }
  }
}