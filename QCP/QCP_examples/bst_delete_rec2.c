#include "bst_def.h"
#include "verification_stdlib.h"

/*@ Import Coq Import naive_C_Rules */


void free_tree_node(struct tree *b)
  /*@ Require exists k v l r, 
                b -> key == k && b -> value == v && 
                b -> left == l && b -> right == r && emp
      Ensure emp
   */;

struct tree** get_pre(struct tree **t)
/*@ 
  With t_left t_key t_value t_right
  Require (*t) != 0 && 
          (*t)->key == t_key && (*t)->value == t_value &&
          INT_MIN <= t_key && t_key <= INT_MAX &&
          store_tree((*t)->left,t_left) *
          store_tree((*t)->right,t_right)
  Ensure exists t_pt ret_left,
        (*__return) != 0 &&
        INT_MIN <= (*__return)->key && (*__return)->key <= INT_MAX &&
        find_pre(t_left,t_key,t_value,t_right).k == (*__return)->key &&
        find_pre(t_left,t_key,t_value,t_right).v == (*__return)->value &&
        find_pre(t_left,t_key,t_value,t_right).pt == t_pt &&
        find_pre(t_left,t_key,t_value,t_right).l_tree == ret_left &&
        (*__return)->right == 0 && 
        store_ptb(__return,t,t_pt) *
        store_tree((*__return)->left, ret_left)
*/
{
  if((*t)->right == (void *)0) return t;
  /*@ (*t)->right != 0 && store_tree((*t)->right, t_right)
      which implies
      exists l0 r0 t_k t_v,
        t_k == (*t)->right->key && t_v == (*t)->right->value &&
        INT_MIN <= t_k && t_k <= INT_MAX &&
        t_right == make_tree(l0, t_k, t_v, r0) &&
        store_tree((*t)->right->left, l0) *
        store_tree((*t)->right->right, r0)
  */
  return get_pre(&((*t)->right));
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
        store_tree(* b, tree_delete'(x, tr))
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
      /*@ exists l0, p->left != 0 && store_tree(p->left, l0)
          which implies
          exists l0' r0' p_l_k p_l_v,
            p_l_k == p->left->key && p_l_v == p->left->value &&
            INT_MIN <= p_l_k && p_l_k <= INT_MAX &&
            l0 == make_tree(l0', p_l_k, p_l_v, r0') &&
            store_tree(p->left->left, l0') *
            store_tree(p->left->right, r0')
      */
      struct tree **pre = get_pre(&(p->left));
      p->key = (*pre)->key;
      p->value = (*pre)->value;
      struct tree *tmp = *pre;
      *pre = (*pre)->left;
      free_tree_node(tmp);
    }
  }
}