#include "bst_def.h"
#include "verification_stdlib.h"


void free_tree_node(struct tree *b)
  /*@ Require exists k v l r, 
                b -> key == k && b -> value == v && 
                b -> left == l && b -> right == r && emp
      Ensure emp
   */;

struct tree* get_pre(struct tree *t)
/*@ 
    With tr
    Require t != 0 && store_tree(t,tr)
    Ensure __return != 0 &&
        exists pt tr_ret_left, 
        (forall tr_ret_right,
        tree_pre_merge(tr,tr_ret_right) == combine_tree(pt, 
          make_tree(tr_ret_left,__return->key,__return->value,tr_ret_right))) && 
        __return->right == 0 && 
        INT_MIN <= __return->key && __return->key <= INT_MAX &&
        store_tree(__return->left, tr_ret_left) * 
        store_pt(__return, t, pt)
*/
{ 
   /*@ t != 0 && store_tree(t, tr)
          which implies
          exists l0 r0,
            INT_MIN <= t -> key && t -> key <= INT_MAX &&
            tr == make_tree(l0, t -> key, t -> value, r0) &&
            store_tree(t -> left, l0) *
            store_tree(t -> right, r0) 
      */
    if(t->right == (void *)0) return t;
    return get_pre(t->right);
}

void delete(struct tree **b, int x)
  /*@ high_level_spec <= low_level_spec
      With m
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_map(* b, m)
      Ensure
        store_map(* b, map_delete(x, m))
   */
;

void delete(struct tree **b, int x)
  /*@ low_level_spec
      With tr
      Require
        INT_MIN <= x && x <= INT_MAX &&
        store_tree(* b, tr)
      Ensure
        store_tree(* b, tree_delete(x, tr))
   */
{
  struct tree *p = *b;
  if(p == (void *)0) return;
  /*@ p != 0 && store_tree(p, tr)
        which implies
        exists l0 r0,
        INT_MIN <= p -> key && p -> key <= INT_MAX &&
        tr == make_tree(l0, p -> key, p -> value, r0) &&
        store_tree(p -> left, l0) *
        store_tree(p -> right, r0) 
    */
  int y = p->key;
  if(x < y){
    delete(&p->left, x);
  }else if(x > y){
    delete(&p->right, x);
  }else{
    if(p->left == (void *)0){
        *b = p->right;
        free_tree_node(p);
    }else{
        struct tree *pre = get_pre(p->left);
        pre->right = p->right;
        p->right = (void *)0;
        *b = p->left;
        free_tree_node(p);
    }
  }
}