
Require Import Effects.Effects.

Effect Translate eq.
Effect Translate nat.
Effect Translate bool.

Parametricity Translate eq.
Parametricity Translate nat.

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

Definition a (A: Type) (B: A -> Type) (f: A) (snd: B f): snd = snd.
Proof. reflexivity. Defined.
Effect Translate a. Print aᵉ.
Parametricity Translate a. Print aᴿ.

Definition id (A: Type) : A -> A := fun a => a.
Effect Translate id. Print idᵉ.
Parametricity Translate id. Print idᴿ.

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

Record msigR (E: Type) (A: El Typeᵉ) 
    (A': El A -> Type) 
    (B: El A -> El Typeᵉ)
    (B': forall H: @El E A, A' H -> @El E (B H) ->Type)
    (r: sigRᵒ E A B) := {
  mzero: forall H: @El E A, A' H -> @El E (zeroᵉ _ _ _ r H) -> Type;
  mfst: A' (fstᵉ _ _ _ r);
  msnd: B' (fstᵉ _ _ _ r) mfst (sndᵉ _ _ _ r);
  mthd: forall (x: @El E (B (fstᵉ _ _ _ r)))
               (x': B' (fstᵉ _ _ _ r) mfst x)
               (a: @El E A)
               (a': A' a),
               eqᴿ E (B (fstᵉ _ _ _ r)) (B' (fstᵉ _ _ _ r) mfst)
                   x x' (sndᵉ _ _ _ r) msnd (thdᵉ _ _ _ r x a);
  mfth: mzero (fstᵉ _ _ _ r) mfst (fthᵉ _ _ _ r);
}.

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