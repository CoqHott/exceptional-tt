Require Import Effects.
Require Import list.Eff.

Set Universe Polymorphism.

Module Import NonDet := list.Eff.

Declare Effect NonDet.

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using NonDet.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using NonDet.

Effect Definition amb : forall A, A -> A -> A using NonDet.
Proof.
refine (fun A => @happ A).
Defined.

Definition quz := foo Type Type.

(* Effect Translate quz using NonDet. *)

Effect Translate bool using NonDet.
Effect Translate eq using NonDet.
Effect Translate list using NonDet.
