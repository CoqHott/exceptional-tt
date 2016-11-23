Require Import Effects.
Require Import exception.Eff.

Set Universe Polymorphism.

Module E.
Definition E := unit.
End E.

Module Import Exception := Make(E).

Declare Effect Exception.

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using Exception.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using Exception.

Effect Definition E : Type using Exception.
Proof.
refine (ret (exist _ _ E.E _)).
refine (fun e => match e with Ok _ e => e | Err _ e => e end).
Defined.

Effect Definition abort : E -> forall A, A using Exception.
Proof.
refine (fun e A => hzero e).
Defined.

Definition quz := foo Type Type.

Effect Translate quz using Exception.
