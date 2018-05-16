
Require Import Weakly.Effects.

Set Printing Universes.
Set Printing Implicit.

Effect Translate nat.
Effect Translate bool. 
Effect Translate list.
Effect Translate eq.
Effect Translate True.
Weakly Translate nat.
Weakly Translate bool.
Weakly Translate list.
Weakly Translate eq.
Weakly Translate True.

Inductive mTest1 (A: Type): Type -> Prop :=
| cmTest11: mTest1 A bool
| cmTest12: mTest1 A nat -> mTest3 A -> mTest2 A bool 0 -> mTest1 A bool
| cmTest13: mTest2 A nat 10 -> mTest1 A bool
with
mTest2 (A:Type): Type -> nat -> Prop :=
| cmTest21: mTest1 A (list nat) -> mTest2 A nat 0
with
mTest3 (A: Type): Prop :=
| cmTest31: mTest1 A nat -> mTest2 A bool 10-> mTest3 A
with
mTest4 (A: Type): Prop :=
| cmTest41: mTest4 A
| cmTest42: mTest1 A bool -> mTest2 A nat 10-> mTest3 A -> mTest4 A -> mTest4 A.

Definition testList := let A:= nat in list A.

Effect Translate mTest1.
Weakly Translate mTest1.

Definition match1 (m1: mTest1 nat bool) :=
  match m1 with
  | cmTest11 _ => I
  | cmTest12 _ a b c => I
  | cmTest13 _ a => I
  end.

Effect Translate match1.
Weakly Translate match1.

Inductive even: nat -> Prop :=
| evZ: even 0
| evS: forall n, odd n -> even (S n)
with
odd: nat -> Prop :=
| oddS: forall n, even n -> odd (S n).

Effect Translate nat. Parametricity Translate nat.
Weakly Translate nat.

Effect Translate even. Parametricity Translate even.
Weakly Translate even.

Effect Translate list. Parametricity Translate list.
Weakly Translate list.

Inductive listP (A: Type): Prop :=
  nilP : listP A | consP : A -> list A -> listP A.
Effect Translate listP. Weakly Translate listP.

Inductive test (A: Type) (B: Prop) (b: B) (a: A): A -> B -> Type := . 

Effect Translate test. Parametricity Translate test.
Weakly Translate test. 

Inductive o : Type :=
with k : Prop :=.
Effect Translate o. Fail Weakly Translate o.

Definition id (A: Type) := A.
Effect Translate id. Weakly Translate id.

Definition idT := id Type.
Effect Translate idT. Weakly Translate idT. Print idTᵂ.

Definition ind_test := mTest4.
Effect Translate ind_test. Weakly Translate ind_test. Print ind_testᵂ.

Definition constructorTest := cmTest42 cmTest11
                                       (cmTest21 cmTest11) 
                                       (cmTest31 cmTest11 (cmTest21 cmTest11))
                                       cmTest41.
Effect Translate constructorTest. Weakly Translate constructorTest.

Definition b1 := Type.
Effect Translate b1. Parametricity Translate b1. Print b1ᴿ.
Weakly Translate b1.

Definition b2 := fun A: Type => A.
Effect Translate b2.
Weakly Translate b2.

Definition b3 (A: Type) (B: Prop): A -> B -> B := fun _ c => c.
Effect Translate b3. Parametricity Translate b3. Print b3ᴿ.
Weakly Translate b3. 

Definition b4 (A: Type) (B: Prop): A -> B -> A := fun c _ => c.
Effect Translate b4. Parametricity Translate b4. Print b4ᴿ.
Weakly Translate b4. 

Definition t1 := Type.
Effect Translate t1. Parametricity Translate t1. Print t1ᴿ.
Weakly Translate t1.

Definition t2 (A: Type) := Type.
Effect Translate t2. Parametricity Translate t2. Print t2ᴿ.
Weakly Translate t2.

Definition t3 (A: Type) := True.
Effect Translate t3. Parametricity Translate t3. Print t3ᴿ.
Weakly Translate t3.

Definition t4 : Type -> Prop -> Prop := fun _ _ => True.
Effect Translate t4. Parametricity Translate t4. Print t4ᴿ.
Weakly Translate t4.

Definition t5 (A: Type) : A  -> Type := fun _ => Type.
Effect Translate t5. Parametricity Translate t5. Print t5ᴿ.
Weakly Translate t5.

Definition t6 (A: Type) (B: Prop) (C: Type): A -> B -> B -> Prop := fun _ _ _ => True.
Effect Translate t6. Parametricity Translate t6. Print t6.
Weakly Translate t6.

Definition t7 (A: Type) (P: Type -> Type): P A -> Type := fun _ => Type.
Effect Translate t7. Parametricity Translate t7. Print t7ᴿ.
Weakly Translate t7. 

Definition t8 (A: Prop): (fun a: Type => a) Prop -> Type := fun _ => True.
Effect Translate t8. Parametricity Translate t8. Print t8ᴿ.
Weakly Translate t8.

Definition t9 (A: Type) (B: Prop) (P: A -> B -> Prop) (a: A) (b: B): P a b -> Prop := fun _ => True.
Effect Translate t9.
Weakly Translate t9.

  