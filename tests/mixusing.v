Require Import Weakly.Effects.

Definition foo (A : Type) (x : A) := x.
Definition bar (A : Type) (x : A) := x.
Definition qux (A : Type) (x : A) := x.

Effect Translate foo using unit.
Parametricity Translate foo using unit.

Effect Translate bar using unit.
Fail Parametricity Translate bar.
(** Cannot happen because needs the effect translation to be generic. *)

Effect Translate qux.
Parametricity Translate qux using unit.
