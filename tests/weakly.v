
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

Parametricity Translate nat.
Parametricity Translate bool.
Parametricity Translate list.
Parametricity Translate eq.
Parametricity Translate True.

Inductive mTest1 (A: Type): Type -> Prop :=
| cmTest11: mTest1 A bool
| cmTest12: mTest1 A nat -> mTest3 A -> mTest2 A bool 0 -> mTest1 A bool
| cmTest13: mTest2 A nat 10 -> mTest1 A bool
with
mTest2 (A:Type): Type -> nat -> Prop :=
| cmTest21: mTest1 A bool -> mTest2 A nat 10
with
mTest3 (A: Type): Prop :=
| cmTest31: mTest1 A bool -> mTest2 A nat 10-> mTest3 A
with
mTest4 (A: Type): Prop :=
| cmTest41: mTest4 A
| cmTest42: mTest1 A bool -> mTest2 A nat 10 -> mTest3 A -> mTest4 A -> mTest4 A.

Effect Translate mTest1.
Weakly Translate mTest1.

Definition constructorTest := cmTest42 (list nat) (cmTest11 (list nat))
                                       (cmTest21 (list nat) (cmTest11 (list nat))) 
                                       (cmTest31 (list nat) (cmTest11 (list nat))
                                                 (cmTest21 (list nat) (cmTest11 (list nat))))
                                       (cmTest41 (list nat)).

Effect Translate constructorTest. Weakly Translate constructorTest.

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

Effect Translate even. Parametricity Translate even.
Weakly Translate even.

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
Effect Translate idT. Weakly Translate idT.

Definition ind_test := mTest4.
Effect Translate ind_test. Weakly Translate ind_test.


Definition b1 := Type.
Effect Translate b1. Parametricity Translate b1.
Weakly Translate b1.

Definition b2 := fun A: Type => A.
Effect Translate b2.
Weakly Translate b2.

Definition b3 (A: Type) (B: Prop): A -> B -> B := fun _ c => c.
Effect Translate b3. Parametricity Translate b3.
Weakly Translate b3. 

Definition b4 (A: Type) (B: Prop): A -> B -> A := fun c _ => c.
Effect Translate b4. Parametricity Translate b4.
Weakly Translate b4. 

Definition t1 := Type.
Effect Translate t1. Parametricity Translate t1.
Weakly Translate t1.

Definition t2 (A: Type) := Type.
Effect Translate t2. Parametricity Translate t2.
Weakly Translate t2.

Definition t3 (A: Type) := True.
Effect Translate t3. Parametricity Translate t3.
Weakly Translate t3.

Definition t4 : Type -> Prop -> Prop := fun _ _ => True.
Effect Translate t4. Parametricity Translate t4.
Weakly Translate t4.

Definition t5 (A: Type) : A  -> Type := fun _ => Type.
Effect Translate t5. Parametricity Translate t5.
Weakly Translate t5.

Definition t6 (A: Type) (B: Prop) (C: Type): A -> B -> B -> Prop := fun _ _ _ => True.
Effect Translate t6. Parametricity Translate t6.
Weakly Translate t6.

Definition t7 (A: Type) (P: Type -> Type): P A -> Type := fun _ => Type.
Effect Translate t7. Parametricity Translate t7.
Weakly Translate t7.

Definition t8 (A: Prop): (fun a: Type => a) Prop -> Type := fun _ => True.
Effect Translate t8. Parametricity Translate t8.
Weakly Translate t8.

Definition t9 (A: Type) (B: Prop) (P: A -> B -> Prop) (a: A) (b: B): P a b -> Prop := fun _ => True.
Effect Translate t9.
Weakly Translate t9.

Module NewTrans.
Import NewExc.
Inductive True' (E: Type): Prop := 
| I: True' E
| True_': E -> True' E.
Inductive False' (E: Type): Prop :=
| False_': E -> False' E.
Inductive and' (E: Type) (A B: @sEl E sProp): Prop :=
| conj': spEl A -> spEl B -> and' E A B
| and_': E -> and' E A B.
Inductive nat' (E: Type): Type :=
| O': nat' E
| S': nat' E -> nat' E
| nat_': E -> nat' E.

Inductive or' (E: Type) (A B: @sEl E sProp): Prop :=
| orL : spEl A -> or' E A B
| orR : spEl B -> or' E A B
| or_': E -> or' E A B.

(* This doesn't go through  because of singleton elimination *)
Fail Definition g_match (E: Type) (A B: @sEl E sProp) (H: or' E A B) :=
  match H with
  | orL _ _ _ _ => sPropVal E (True' E) (True_' E)
  | _ => sPropVal E (False' E) (False_' E)
  end.


Check (forall (E: Type), and' E (sPropVal E (True' E) (True_' E)) 
                                (sPropVal E (False' E) (False_' E))).
Check (fun (E: Type) =>
  let t := (sPropVal E (True' E) (True_' E)) in
  let f := (sPropVal E (False' E) (False_' E)) in
  let a := (sPropVal E (and' E t f) (and_' E t f)) in
  sPropVal E (and' E a a) (and_' E a a)).

End NewTrans.
