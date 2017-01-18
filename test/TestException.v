Require Import Effects.
Require Import exception.Eff.

Set Universe Polymorphism.

Parameter E_:Type. 

Module E.
Definition E := E_.
End E.

Module Import Exception := Make(E).

Declare Effect Exception.

Effect Definition E : Type using Exception.
Proof.
  refine (ret (exist _ _ E.E _)).
  refine (fun e => match e with Ok _ e => e | Err _ e => e end).
Defined.

Effect Definition fail : E -> forall A, A using Exception.
Proof.
refine (fun e A => (El A).(prf) (Err _ e)).
Defined.

(* some definitions to play with the plugin *)

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using Exception.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using Exception.

Definition quz := foo Type Type.

Effect Translate quz using Exception.

Effect Translate bool using Exception.
Effect Translate eq using Exception.
Effect Translate list using Exception.
