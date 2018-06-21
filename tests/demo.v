Require Import Weakly.Effects.

Effect List Translate nat bool list eq ex False True unit.
Weakly List Translate nat bool list eq ex False True unit. 
Parametricity List Translate nat bool list eq ex False True unit.

Print eqᵂ. Print exᵂ.

Effect Definition raise: forall A, A using unit.
Proof. intros E A. exact (Err A tt). Defined.

Definition exist_good: exists n, n = raise nat.
Proof. exists (raise nat); reflexivity. Defined.
Effect Translate exist_good using unit. 
Weakly Translate exist_good using unit.
Fail Parametricity Translate exist_good using unit.

Definition exist_bad: exists n, n = raise nat.
Proof. exact (raise _). Defined.
Effect Translate exist_bad using unit. 
Fail Weakly Translate exist_bad using unit.

(**  Translation on inductives **)

Print natᵂ.
Print listᵂ.
Print eqᵂ.
Print exᵂ.

Inductive mTest1 (A: Type): Type -> Prop :=
| cmTest11: mTest1 A bool
| cmTest12: mTest1 A nat -> mTest3 A -> mTest2 A bool 0 -> mTest1 A bool
| cmTest13: mTest2 A nat 3 -> mTest1 A bool
with
mTest2 (A:Type): Type -> nat -> Prop :=
| cmTest21: mTest1 A bool -> mTest2 A nat 3
with
mTest3 (A: Type): Prop :=
| cmTest31: mTest1 A bool -> mTest2 A nat 3-> mTest3 A
with
mTest4 (A: Type): Prop :=
| cmTest41: mTest4 A
| cmTest42: mTest1 A bool -> mTest2 A nat 3 -> mTest3 A -> mTest4 A -> mTest4 A.

Effect Translate mTest1. Print mTest1ᵒ.
(* Weakly Translate mTest1. Print mTest1ᵂ.

Definition constructorTest := cmTest42 (list nat) (cmTest11 (list nat))
                                       (cmTest21 (list nat) (cmTest11 (list nat))) 
                                       (cmTest31 (list nat) (cmTest11 (list nat))
                                                 (cmTest21 (list nat) (cmTest11 (list nat))))
                                       (cmTest41 (list nat)).

Effect Translate constructorTest. Print constructorTestᵉ.
Weakly Translate constructorTest. Print constructorTestᵂ.
*)

(** Translation on mixing *)

Definition sort_mixing1 (A: Type) (B: Prop) (a: A) (b: B) (P: A -> B -> Prop) (H: P a b) := H.
Definition sort_mixing2 (A: Type) (B: Prop) (a: A) (b: B) (P: A -> B -> Type) (H: P a b) := H.

Effect List Translate sort_mixing1 sort_mixing2.
Weakly List Translate sort_mixing1 sort_mixing2.
Print sort_mixing1ᵂ. Print sort_mixing2ᵂ.

(** Translation of match **)

(*
Definition match1 (m1: mTest1 nat bool) : True :=
  match m1 with
  | cmTest11 _ => I
  | cmTest12 _ a b c => I
  | cmTest13 _ a => I
  end.
Effect Translate match1. Print match1ᵉ.
Weakly Translate match1. Print match1ᵂ.
*)

Effect Definition O_fail: 0 = raise nat -> False using unit.
Proof. intros E H. inversion H. exact (Falseᴱ E X0). Qed.

Weakly Definition O_fail using unit.
Proof. intros E H H'. simpl in *. inversion H'. Qed.

Effect Definition S_fail: forall n, S n = raise nat -> False using unit.
Proof. intros E n H. inversion H. exact (Falseᴱ E X0). Qed.

Weakly Definition S_fail using unit.
Proof. intros E n H H'. inversion H'. Qed.

Definition nat_fail: forall (n: nat), n = raise nat -> False := fun n H =>
  match n as m return (m = raise nat -> False) with
  | O => fun H => O_fail H
  | S n => fun H => S_fail n H
  end H.
Effect Translate nat_fail using unit.
Fail Weakly Translate nat_fail using unit.

Effect List Translate le lt gt.
Weakly List Translate le lt gt.


