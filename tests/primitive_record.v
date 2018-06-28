
Require Import Effects.Effects.

Set Primitive Projections.

Effect Translate nat.
Effect Translate bool.

Record sigR (A: Type) (B: A -> Type): Type := exR {
  fst: A;
  snd: B fst;
}. 
Effect Translate sigR.

Definition tt: sigR _ (fun _ => bool) := {|
  fst := 0 ;
  snd := true
|}.

Effect Translate tt.
Definition f := snd nat (fun _ => bool) tt.
Effect Translate f.
