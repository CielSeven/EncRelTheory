/*@ Extern Coq (should_be_equal: {A} -> A -> A -> Prop) */
/*@ Extern Coq (dup_data_at_error : Z -> Assertion)*/
/*@ Extern Coq (dup_data_at_error_prop : Prop) */
/*@ Extern Coq (option :: * => *) */
/*@ Extern Coq (Some: {A} -> A -> option A)
               (None: {A} -> option A) */
/*@ Extern Coq (UINT_MAX : Z) */

enum TypeOp
{
    AT_ATOM,
    AT_ARROW,
    AT_APP,
    AT_VAR
};

struct atype
{
    enum TypeOp t;
    union
    {
        struct
        {
            struct atype *from;
            struct atype *to;
        } ARROW;
        struct
        {
            struct atype *tfn;
            struct atype *rand;
        } APP;
        struct
        {
            int name;
        } VAR;
        struct
        {
            int name;
        } ATOM;
    } d;
};

/*@ Import Coq Require Import typeinfer_lib */
/*@ Import Coq Import naive_C_Rules */


/*@ Extern Coq (TypeTree :: *) */
/*@ Extern Coq (sol :: *) */
/*@ Extern Coq
    (store_type : Z -> TypeTree -> Assertion)
    (store_type_aux : Z -> Z -> TypeTree -> Assertion)
    (store_option_type : Z -> option TypeTree -> Assertion)
    (store_solution : Z -> sol -> Assertion)
    (store_solution_aux : Z -> sol -> Z -> Z -> option TypeTree -> Assertion)
    (unify_rel : TypeTree -> TypeTree -> sol -> sol -> Prop)
    (solution_at : sol -> Z -> TypeTree -> Prop)
    (sol_update : sol -> Z -> TypeTree -> sol)
    (TVar : Z -> TypeTree)
    (TAtom : Z -> TypeTree)
    (TArrow : TypeTree -> TypeTree -> TypeTree)
    (TApply : TypeTree -> TypeTree -> TypeTree)
    (repr_rel_node : sol -> TypeTree -> TypeTree -> Prop)
    (not_occur_final: sol -> Z -> TypeTree -> Prop)
    (debug : Assertion)
*/

/*@ include strategies "common.strategies" */
/*@ include strategies "typeinfer.strategies" */
