Declare ML Module "exception".

Set Universe Polymorphism.
Set Primitive Projections.

Record Pack A := {
  wit : bool;
  val : if wit then A else unit;
}.
