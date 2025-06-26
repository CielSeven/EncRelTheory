# Example: Polymorphic List and its Reversal

Consider the following C program.

```c
struct list {
  void * data;
  struct list * next;
};

struct list *reverse(struct list *p) {
  struct list *w, *t, *v;
  w = (void *) 0;
  v = p;
  while (v) {
    t = v->next;
    v->next = w;
    w = v;
    v = t;
  }
  return w;
}
```

Here the member `data` is a pointer to `void`, which means to store different kinds of data. It can even store complex data structures, such as a pointer to the root of a binary tree.

# Defining a Polymorphic Representation Predicate

We can utilize polymorphism in Coq to define the representation predicate.

```
Fixpoint sll {A: Type} (storeA: addr -> A -> Assertion)
             (x: addr) (l: list A): Assertion :=
  match l with
    | nil     => [| x = NULL |] && emp
    | a :: l0 => [| x <> NULL |] && 
                 EX h y: addr,
                   &(x # "list" ->ₛ "data") # Ptr |-> h **
                   &(x # "list" ->ₛ "next") # Ptr |-> y **
                   storeA h a **
                   sll storeA y l0
  end.
```

Here `storeA` is the abstracted representation predicate of member `data`. To declare a polymorphic representation predicate in C, we use the following grammar.

```c
/*@ Import Coq Require Import poly_sll_lib */
/*@ Extern Coq (sll : {A} -> (Z -> A -> Assertion) -> Z-> list A -> Assertion) */
```

We require that such polymorphic terms declared in C must have implicit type arguments in the prefix.

# Polymorphic Specification

The function `reverse` in T2 does not inspect or modify the member `data`, so it works on any list. Its specification is thus polymorphic as well. We use the following grammar to write polymorphic specifications, again requiring that type arguments are implicit and in the prefix.

```
struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/
```
