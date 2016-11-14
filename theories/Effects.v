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

Inductive unit := tt.
