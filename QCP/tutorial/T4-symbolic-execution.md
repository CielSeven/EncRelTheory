Our tool runs symbolic execution on an annotated C program. It generates separation logic assertions before and after each statement. By doing so, correctness of the program is reduced to entailments between assertions.

# Executing a Single Step

The following is our annotated C program (same as in T3).


```c
#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"

struct list *reverse(struct list *p) 
/*@ With (l: list Z)
    Require sll(p, l)
    Ensure sll(__return, rev(l))
*/
{
   struct list *w;
   struct list *v;
   w = (void *)0;
   v = p;
   /*@ Assert Inv
          exists p_v w_v v_v l1 l2,
          l == app(rev(l1), l2) &&
          data_at(&p, p_v) *
          data_at(&w, w_v) *
          data_at(&v, v_v) *
          sll(w_v, l1) *
          sll(v_v, l2)
      */
   while (v) {
      /*@ Assert
            exists p_v w_v v_v v_data v_next l2_new l1 l2,
            l == app(rev(l1), l2) &&
            l2 == cons(v_data, l2_new) &&
            data_at(&p, p_v) *
            data_at(&w, w_v) *
            data_at(&v, v_v) *
            data_at(&(v_v -> data), v_data) *
            data_at(&(v_v -> next), v_next) *
            sll(w_v, l1) *
            sll(v_next, l2_new)
      */
      struct list * t;
      t = v -> next;
      v -> next = w;
      w = v;
      v = t;
   }
   return w;
}

```

We also know from T3 that we have the symbolic state `exists p_v, data_at(&p, p_v) * sll(p_v, l)`, which is transformed from the precondition, before the function body begins.


## Symbolic execution of variable declaration

According to the C semantics, some memory is allocated (on the stack, but we do not make the distinction) for `w`. This part of the memory is uninitialized, for which we write `undef_data_at(&w)`: `undef_data_at(a)` means that the address `a` is possibly uninitialized, and we are not allowed to load from it. After the first two lines the symbolic state turns to `exists p_v, data_at(&p, p_v) * sll(p_v, l) * undef_data_at(&w) * undef_data_at(&v)`.

## Symbolic execution of variable assignment

To execute `w = (void *)0`, our tool naively searches for `undef_data_at(&w)` or `data_at(&w, _)` at changes that to `data_at(&w, 0)`. When the right hand side of `=` is not so simple, we must compute its (symbolic) value first. After the next two lines, the symbolic state turns to `(exists p_v, data_at(&p, p_v) * sll(p_v, l) * data_at(&w, 0) * data_at(&v, p_v))`.

## Symbolic execution meets assertions

When we meet an assertion provided manually, we use that as our symbolic state afterwards and require, by record the condition in the Coq output, that the current symbolic states implies the manual one. The invariant turns the symbolic state to `exists p_v w_v v_v l1 l2, v_v != 0 && l == app(rev(l1), l2) && data_at(&p, p_v) * data_at(&w, w_v) * data_at(&v, v_v) * sll(w_v, l1) * sll(v_v, l2)`.

## Symbolic execution of conditions (in `if`, `while`, etc.)

After we enter the loop, we know that the loop condition is nonzero. So before the loop body, the symbolic state turns to `exists p_v w_v v_v l1 l2, v_v != 0 && l == app(rev(l1), l2) && data_at(&p, p_v) * data_at(&w, w_v) * data_at(&v, v_v) * sll(w_v, l1) * sll(v_v, l2)`. It is similar to compute the state after the loop, taking the loop condition to be zero. The same also works for `if` and other loop constructs.

Now we know how to execute until the end of the loop body. Omitting the details, we get `exists p_v w_v v_v v_data v_next l2_new l1 l2, l == app(rev(l1), l2) && l2 == cons(v_data, l2_new) && data_at(&p, p_v) * data_at(&w, v_v) * data_at(&v, v_next) * data_at(&(v_v -> data), v_data) * data_at(&(v_v -> next), w_v) * data_at(&t, v_next) * sll(w_v, l1) * sll(v_next, l2_new)`.

## Symbolic execution out of scope

According to the C semantics, local variables declared inside a pair of curly braces are invisible outside. We must free their memory occupied after the right curly brace. After deleting the variable `t`, the symbolic state after the loop body turns to `exists p_v w_v v_v v_data v_next l2_new l1 l2, l == app(rev(l1), l2) && l2 == cons(v_data, l2_new) && data_at(&p, p_v) * data_at(&w, v_v) * data_at(&v, v_next) * data_at(&(v_v -> data), v_data) * data_at(&(v_v -> next), w_v) * sll(w_v, l1) * sll(v_next, l2_new)`. 

By the very definition of a loop invariant, we require the previous assertion to imply the loop invariant.

## Symbolic execution of `return`

Finally, we execute `return w;` and ends this function. We compute the value of the return value `w`, here `w_v`, and substitute it for `__return` in the postcondition. The assertion with local variables deleted should imply the substituted postcondition: `forall l p_v w_v v_v l1 l2, v_v == 0 && l == app(rev(l1), l2) && data_at(&p, p_v) * sll(w_v,l1)* sll(v_v,l2) |-- sll(w_v,rev(l))`.

# Verification-condition Generation

In the previous example, we required the user to prove, 3 time, an assertion implies another. These conditions are called verification conditions (VC). Our tool exports the conditions to Coq scripts. it will generate 3 Coq output files: (1) the "goal" file contains propositions to prove, (2) the "proof auto" file contains the proofs automatically generated (to be done), and (3) the "proof manual" file contains missing proofs for users to fill in. We present the 3 conditions in the previous example in the following.

1. The state before the loop implies the loop invariant.

```
sll p l |-- EX l1 l2 : list Z, [|l = rev l1 ++ l2|] && sll 0 l1 ** sll p l2
```

2. The state after the loop body implies the loop invariant.

```
[|v_data = x|] && [|l2 = x :: xs|] && [|v <> 0|] && [|l = rev l1 ++ l2|] &&
  sll v_next xs **
  &( v # "list" ->ₛ "next") # Ptr |-> w **
  &( v # "list" ->ₛ "data") # Int |-> v_data **
  sll w l1 |--
EX l0 l3 : list Z, [|l = rev l0 ++ l3|] && sll v l0 ** sll v_next l3
```

3. The state after `return` implies the function postcondition.

```
[|v = 0|] && [|l = rev l1 ++ l2|] && sll w l1 ** sll v l2 |-- sll w (rev l)
```
