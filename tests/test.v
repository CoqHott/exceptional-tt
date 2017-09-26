Require Import Effects.Effects.

Inductive foo (A : Type) (x : A) (y := x) (y : A) := Foo.

Effect Translate foo.
Effect Translate eq.

Effect Translate eq_rect.

Inductive bar : nat -> nat -> Type := Bar : bar 0 1.

Effect Translate nat.
Effect Translate bar.

Effect Translate bool.
Effect Translate list.
Effect Translate nat_rect.
Effect Translate False.

Require Import Streams.

Effect Translate Stream.
Effect Translate tl.
Effect Translate Nat.pred.
Effect Translate Str_nth_tl.

Effect Translate unit.

Effect Translate sum.

Effect Translate sum_rect.

Definition test (A : Type) (f : A -> A) (b : bool) : A -> A :=
match b with
| true => f
| false => fun x => x
end.

Effect Translate test.

Effect Translate eq_trans.
Effect Translate eq_trans_assoc.

Definition qux (A : Type) := list (A -> A).

Effect Translate qux.
