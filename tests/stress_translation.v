Require Import Weakly.Effects.

Inductive empty: Type := . Print sigT.

Inductive vec (A: Type): nat -> Type :=
| vnil: vec A 0
| vconst: forall n, A -> vec A n -> vec A (S n).

Effect List Translate empty unit bool nat list vec sum sig sigT.
Effect List Translate False True and or ex eq.