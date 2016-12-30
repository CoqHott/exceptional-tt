Declare ML Module "exception".

Set Universe Polymorphism.
Set Primitive Projections.

(** Redefinition of standard stuff to get primitive projections and universe
    polymorphism. *)

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Definition prod A B := sig A (fun _ => B).
Definition pair {A B} (x : A) (y : B) := exist _ _ x y.
Definition fst {A B} (p : prod A B) : A := p.(wit).
Definition snd {A B} (p : prod A B) : B := p.(prf).

Inductive unit := tt.
