#include "verification_stdlib.h"
#include "verification_list.h"
#include "eval_def.h"

enum BinOpType {
  T_PLUS,
  T_MINUS,
  T_MUL,
  T_DIV,
  T_MOD,
  T_LT,
  T_GT,
  T_LE,
  T_GE,
  T_EQ,
  T_NE,
  T_AND,
  T_OR
};

enum UnOpType {
  T_UMINUS,
  T_NOT
};

enum ExprType {
  T_CONST/* = 0*/,
  T_VAR,
  T_BINOP,
  T_UNOP
};

struct expr {
  enum ExprType t;
  union {
    struct {int value; } CONST;
    struct {int name; } VAR;
    struct {enum BinOpType op; struct expr * left; struct expr * right; } BINOP;
    struct {enum UnOpType op; struct expr * arg; } UNOP;
  } d;
};

int eval(struct expr * e, int * var_value)
/*@ With (e0: expr) (l: list Z)
    Require safe_eval(e0, l) && store_expr(e, e0) * store_int_array(var_value, 100, l)
    Ensure __return == expr_eval(e0, l) && store_expr(e, e0) * store_int_array(var_value, 100, l)
*/
{
  /*@ store_expr(e, e0)
        which implies
      store_expr_aux(e, e -> t, e0) */
  switch (e -> t) {
    case T_CONST: {
      /*@ e -> t == T_CONST && store_expr_aux(e, e -> t, e0)
          which implies
          exists n, e -> t == T_CONST && e0 == EConst(n) && e ->d.CONST.value == n */
      return e -> d.CONST.value;
    }
    case T_VAR: {
      /*@ e -> t == T_VAR && safe_eval(e0, l) && store_expr_aux(e, e -> t, e0) * store_int_array(var_value, 100, l)
          which implies
          exists n, 0 <= n && n < 100 && e -> t == T_VAR && e0 == EVar(n) && e ->d.VAR.name == n && store_int_array(var_value, 100, l) */
      return var_value[e ->d.VAR.name];
    }
    case T_BINOP: {
      /*@ e -> t == T_BINOP && store_expr_aux(e, e -> t, e0)
          which implies
          exists e1 e2 op,
            e -> t == T_BINOP &&
            e0 == EBinop(op, e1, e2) &&
            e -> d.BINOP.op == BinOpID(op) &&
            store_expr(e -> d.BINOP.left, e1) *
            store_expr(e -> d.BINOP.right, e2) */
      if (e -> d.BINOP.op == T_AND) {
        if (eval(e -> d.BINOP.left, var_value)) {
          if (eval(e -> d.BINOP.right, var_value)) {
            return 1;
          } else {
            return 0;
          }
        } else {
          return 0;
        }
      } else if (e -> d.BINOP.op == T_OR) {
        if (eval(e -> d.BINOP.left, var_value)) {
          return 1;
        } else {
          if (eval(e -> d.BINOP.right, var_value)) {
            return 1;
          } else {
            return 0;
          }
        }
      } else {
        int left_val = eval(e -> d.BINOP.left, var_value);
        int right_val = eval(e -> d.BINOP.right, var_value);
        switch (e -> d.BINOP.op) {
        case T_PLUS:
          return left_val + right_val;
        case T_MINUS:
          return left_val - right_val;
        case T_MUL:
          return left_val * right_val;
        case T_DIV:
          return left_val / right_val;
        case T_MOD:
          return left_val % right_val;
        case T_LT:
          return left_val < right_val;
        case T_GT:
          return left_val > right_val;
        case T_LE:
          return left_val <= right_val;
        case T_GE:
          return left_val >= right_val;
        case T_EQ:
          return left_val == right_val;
        case T_NE:
          return left_val != right_val;
        }
      }
    }
    case T_UNOP: {
      /*@ e -> t == T_UNOP && store_expr_aux(e, e -> t, e0)
          which implies
          exists op e1,
            e -> t == T_UNOP && e0 == EUnop(op, e1) &&
            e -> d.UNOP.op == UnOpID(op) &&
            store_expr(e -> d.UNOP.arg, e1) */
      if (e -> d.UNOP.op == T_NOT) {
        return ! eval(e -> d.UNOP.arg, var_value);
      }
      else {
        return - eval(e -> d.UNOP.arg, var_value);
      }
    }
  }
}
