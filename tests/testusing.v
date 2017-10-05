Require Import Effects.Effects.

Inductive foo (A : Type) (x : A) (y := x) (y : A) := Foo.

Effect Translate foo using unit.
Effect Translate eq using unit.

Effect Translate eq_rect using unit.

Inductive bar : nat -> nat -> Type := Bar : bar 0 1.

Effect Translate nat.
Effect Translate bar using unit.

Effect Translate bool using unit.
Effect Translate list using unit.
Effect Translate nat_rect using unit.
Effect Translate False.

Require Import Streams.

Effect Translate Stream using unit.
Effect Translate tl using unit.
Effect Translate Nat.pred using unit.
Effect Translate Str_nth_tl using unit.

Effect Translate unit.

Effect Translate sum.

Effect Translate sum_rect.

Definition test (A : Type) (f : A -> A) (b : bool) : A -> A :=
match b with
| true => f
| false => fun x => x
end.

Effect Translate test using unit.

Effect Translate eq_trans using unit.
Effect Translate eq_trans_assoc using unit.

Definition qux (A : Type) := list (A -> A).

Effect Translate qux using unit.
