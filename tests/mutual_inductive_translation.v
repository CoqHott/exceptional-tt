Require Import Effects.Effects.

Effect Translate nat. Parametricity Translate nat.

Inductive even: nat -> Prop :=
| evZ: even 0
| evS: forall n, odd n -> even (S n)
with
odd: nat -> Prop :=
| oddS: forall n, even n -> odd (S n).

Effect Translate even. Parametricity Translate even.

Inductive mTest1: Prop :=
| cmTest11: mTest1
| cmTest12: mTest1 -> mTest3 -> mTest2 -> mTest1
| cmTest13: mTest2 -> mTest1
with
mTest2: Prop :=
| cmTest21: mTest1 -> mTest2
with
mTest3: Prop :=
| cmTest31: mTest1 -> mTest2 -> mTest3
with
mTest4: Prop :=
| cmTest41: mTest4
| cmTest42: mTest1 -> mTest2 -> mTest3 -> mTest4 -> mTest4.

Effect Translate mTest2. Parametricity Translate mTest4.
Print mTest4ᴿ.