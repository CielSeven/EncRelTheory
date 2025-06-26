struct dlist {
    struct dlist *next;
    struct dlist *prev;
    int data;
};

/*@ Extern Coq (dlistrep : Z -> Z -> Assertion)
               (dllseg: Z -> Z -> Z -> Z -> Assertion)
               (dll_tag : Z -> Z -> Prop)
 */

/*@ Import Coq Require Import dll_shape_lib */

/*@ include strategies "dll_shape.strategies" */