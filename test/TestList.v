Require Import Effects.
Require Import list.Eff.

Set Universe Polymorphism.

Declare Effect list.Eff.

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using list.Eff.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using list.Eff.

Effect Definition amb : forall A, A -> A -> A using list.Eff.
Proof.
refine (fun A => @happ A).
Defined.

Definition quz := foo Type Type.

Effect Translate quz using list.Eff.

Effect Translate bool using list.Eff.
Effect Translate eq using list.Eff.
Effect Translate list using list.Eff.
