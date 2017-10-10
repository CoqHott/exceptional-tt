Require Import Effects.Effects.

Inductive foo (A : Type) (x : A) (y := x) (y : A) := Foo.

Effect Translate foo.
Parametricity Translate foo.
Effect Translate eq.
Parametricity Translate eq.

Effect Translate eq_rect.
Parametricity Translate eq_rect.

Inductive bar : nat -> nat -> Type := Bar : bar 0 1.

Effect Translate nat.
Parametricity Translate nat.
Effect Translate bar.
Parametricity Translate bar.

Effect Translate bool.
Parametricity Translate bool.
Effect Translate list.
Parametricity Translate list.
Effect Translate nat_rect.
Effect Translate False.
Parametricity Translate False.

Require Import Streams.

Effect Translate Stream.
Parametricity Translate Stream.
Effect Translate tl.
Effect Translate Nat.pred.
Effect Translate Str_nth_tl.

Effect Translate unit.
Parametricity Translate unit.

Effect Translate sum.
Parametricity Translate sum.

Effect Translate sum_rect.

Definition test (A : Type) (f : A -> A) (b : bool) : A -> A :=
match b with
| true => f
| false => fun x => x
end.

Effect Translate test.

Effect Translate eq_trans.
Parametricity Translate eq_trans.
Effect Translate eq_trans_assoc.
Parametricity Translate eq_trans_assoc.

Definition qux (A : Type) := list (A -> A).

Effect Translate qux.
Parametricity Translate qux.
