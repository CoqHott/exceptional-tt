
Require Import Effects.Effects.

Effect Translate eq.
Effect Translate nat.
Effect Translate bool.

Parametricity Translate eq.
Parametricity Translate nat.
Parametricity Translate bool.

Set Primitive Projections.
Record recordTest (A: Type) (B: A -> Type): Type := recordTestB {
  c1: A -> Type;
  c2: A;
  c3: B c2;
  c4: forall (x: B c2), A -> x = c3;
  c5: c1 c2;
}.
Unset Primitive Projections.
Effect Translate recordTest.
Parametricity Translate recordTest.

Record sigR (A: Type) (B: A -> Type): Type := exR {
  fst: A;
  snd: B fst;
}.
Effect Translate sigR.
Parametricity Translate sigR.

(** Primitive record on body no handled yet.
    Fail to find default exceptional for primitive record *)
Definition fail_1 A B := sigR A B.
Definition fail_2 A := sigR A.
Definition fail_3 := sigR.
(*
Fail Effect Translate fail_1.
Fail Effect Translate fail_2.
Fail Effect Translate fail_3.
*)

Definition primitive_id: sigR nat (fun n: nat => bool) -> sigR nat (fun n: nat => bool) := fun a => a.
Effect Translate primitive_id.
Parametricity Translate primitive_id.

Definition test: sigR nat (fun n: nat => bool) := {|
  fst := 0 ;
  snd := true ;
|}.
Effect Translate test.
Parametricity Translate test.

Definition app_test := primitive_id test.
Effect Translate app_test.
Parametricity Translate app_test.
