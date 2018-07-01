
Require Import Effects.Effects.

Effect Translate eq.
Effect Translate nat.
Effect Translate bool.

Parametricity Translate eq.

Effect Translate ex.
Parametricity Translate ex. Print exᴿ.

Definition g (A: Type) (B: A -> Type): A -> Type := fun _ => Type.
Effect Translate g.
Parametricity Translate g. Print gᴿ.

Record tsigR (A: Type) (B: A -> Type): Type := texR {
  tzero: A -> Type;
  tfst: A;
  tsnd: B tfst;
  tthd: forall (x: B tfst), A -> x = tsnd;
  tfth: tzero tfst;
}.
Print tsigR.
Effect Translate tsigR. Print tsigRᵒ.
Parametricity Translate tsigR. Print tsigRᴿ.

Set Primitive Projections.
Record sigR (A: Type) (B: A -> Type): Type := exR {
  zero: A -> Type;
  fst: A;
  snd: B fst;
  thd: forall (x: B fst), A -> x = snd;
  fth: zero fst;
}. 
Effect Translate sigR. Print sigR.
Parametricity Translate sigR. Print sigRᴿ. 

Definition tt: sigR _ (fun _ => bool) := {|
  fst := 0 ;
  snd := true
|}.
Effect Translate tt.
Parametricity Translate tt.

Effect Translate tt.
Definition f := snd nat (fun _ => bool) tt.
Effect Translate f.

CoInductive stream (A: Type) := Stream {
  hd: A;
  tl: stream A
}. Print stream.  