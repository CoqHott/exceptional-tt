
Require Import Effects.Effects.

Effect Translate eq.
Effect Translate nat.
Effect Translate bool.
Effect Translate sigT.

Parametricity Translate eq.
Parametricity Translate nat.
Parametricity Translate bool.
Parametricity Translate sigT.

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
Effect Translate sigR. Print sigRᵒ.
Parametricity Translate sigR. Print sigRᴿ.

Record ss (A: Type) (B: A -> Type): Type := sexR {
  sfst: A;
  ssnd: B sfst;
}.

Effect Translate ss.
Parametricity Translate ss. Check sexRᴿ.
Print sigT.
Definition gg A := @tsigR A.
Effect Translate gg. Print ggᵉ.
Parametricity Translate gg. Print ggᴿ.

Definition tt: ss nat (fun n: nat => bool) := {|
  sfst := 0 ;
  ssnd := true ;
|}.
Print tt.
Effect Translate tt. Check sexRᴿ.
Parametricity Translate tt.

(*
Illegal application: 
The term "sexRᴿ" of type
 "forall (E : Type) (A : El Typeᵉ) (Aᴿ : El A -> Type) (B : El A -> El Typeᵉ)
    (Bᴿ : forall H : El A, Aᴿ H -> El (B H) -> Type) (r : ssᵒ E A B) (sfstᴿ : Aᴿ (sfstᵉ _ _ _ r)),
  Bᴿ (sfstᵉ _ _ _ r) sfstᴿ (ssndᵉ _ _ _ r) -> ssᴿ E A Aᴿ B Bᴿ r"
cannot be applied to the terms
 "E" : "Type"
 "TypeVal E (natᵒ E) (natᴱ E)" : "type E"
 "natᴿ E" : "natᵒ E -> Type"
 "fun _ : natᵒ E => TypeVal E (boolᵒ E) (boolᴱ E)" : "natᵒ E -> type E"
 "fun (n : natᵒ E) (_ : natᴿ E n) => boolᴿ E" : "forall n : natᵒ E, natᴿ E n -> boolᵒ E -> Type"
 "Oᵉ E" : "natᵒ E"
 "Oᴿ E" : "natᴿ E (Oᵉ E)"
 "trueᵉ E" : "boolᵒ E"
 "trueᴿ E" : "boolᴿ E (trueᵉ E)"
The 6th term has type "natᵒ E" which should be coercible to
 "ssᵒ E (TypeVal E (natᵒ E) (natᴱ E)) (fun _ : natᵒ E => TypeVal E (boolᵒ E) (boolᴱ E))".
*)

Effect Translate tt.
Definition f := snd nat (fun _ => bool) tt.
Effect Translate f.

CoInductive stream (A: Type) := Stream {
  hd: A;
  tl: stream A
}.