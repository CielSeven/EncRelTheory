The verification goal of a C function is its *specification*. A specification consists of a (optional) list of auxiliary logical variables, the precondition, and the postcondition.

## Example: list reversal

The following function reverses a list defined in T1.

```c
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

We can assign the following specification to the function.

```c
struct list *reverse(struct list *p);
  /*@ With (l: list Z)
      Require sll(p, l)
      Ensure sll(__return, rev(l))
  */
```

The specification reads: for any `l`, if `sll(p, l)` holds at function entry, then `sll(__return, rev(l))` holds at function exit. Here `rev` is list reversal in Coq, and `__return` denotes the return value. The pre- and postcondition can mention the value of function arguments.

The assertion language in C is different from that in Coq. The following table is a quick translation; M0_frontend_assertions.md explains it in detail.

| Explaination           | Coq term       | C annotation                                          |
|:-----------------------|:---------------|:------------------------------------------------------|
| Separating conjunction | P ** Q         | P * Q                                                 |
| Existential            | EX             | exists                                                |
| Equality               | =              | ==                                                    |
| Inequality             | <>             | !=                                                    |
| Function and predicate | f x y          | f(x, y)                                               |
| Pure Coq proposition   | [\| P \|]      | P                                                     |
| 4-byte integer storage | p # Int \|-> v | data_at(p, int, v)                                    |
| pointer storage        | p # Ptr \|-> v | data_at(p, int *, v) <br> data_at(p, int * *, v) etc. |
