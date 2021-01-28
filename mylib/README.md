## mylib.v

### binary relation library

Library for general binary relations.

```Coq
Variable (T:Type).
Variable (R:rel T).

Definition strict : rel T := R x y && ~~ R y x.
Definition equiv : rel T := R x y && R y x.
Definition comparable : rel T := R x y || R y x.
Definition incomp : rel T := ~~ R x y && ~~ R y x.
```

We can divide a goals by all relations between x y:T by using "/(relP R x y)".
If `R` is total, we can use "totalP" instead of "relP".

```Coq
Variable (S:Type).
Variable (f:S -> T).

Definition argrel : rel S := fun x y => R (f x) (f y).

Variable (Q:rel S).

Definition lexicographic : rel (T * S) :=
  fun x y => strict x.1 y.1 || equiv x.1 y.1 && Q x.2 y.2.
```
