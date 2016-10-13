Declare ML Module "exception".

Set Universe Polymorphism.
Set Primitive Projections.

Record Pack (A : bool -> Type) := mkPack {
  wit : bool;
  val : A wit;
}.

Definition TYPE := Pack (fun b => if b return Type then Type else unit).

Definition El (T : TYPE) : Type :=
match T.(wit _) as wit return (if wit then Type else unit) -> Type with
| true => fun T => Pack (fun b => if b then T else unit)
| false => fun _ => unit
end T.(val _).

Definition empty (A : TYPE) : El A.
Proof.
unfold El.
destruct A as [[|] A]; cbn.
refine (mkPack _ false tt).
exact tt.
Defined.

Definition mkTYPE (A : Type) : TYPE := mkPack (fun b => if b then Type else unit) true A.

Definition Typeᵉ : TYPE := mkTYPE Type.
Definition Setᵉ : TYPE := mkTYPE Set.
Definition Propᵉ : TYPE := mkTYPE Prop.

Definition Prod₀ᵉ (A B : TYPE) : TYPE := mkTYPE (El A -> El B).

Definition Lam₀ᵉ (A B : TYPE) (f : El A -> El B) : El (Prod₀ᵉ A B) :=
  mkPack _ true f.

Definition App₀ᵉ (A B : TYPE) (f : El (Prod₀ᵉ A B)) (x : El A) : El B :=
match f.(wit _) as wit return (if wit then El A -> El B else unit) -> El B with
| true => fun f => f x
| false => fun _ => empty B
end f.(val _)
.

(*
Definition Prodᵉ (A : TYPE) (B : El (Prod₀ᵉ A Typeᵉ)) : TYPE :=
  mkTYPE (
    forall x : El A,
      match B.(wit _) as wit return (if wit then El A -> TYPE else unit) -> Type with
      | true => fun B => El (B x)
      | false => fun _ => unit
      end B.(val _)
  ).

Definition Lamᵉ (A : TYPE) (B : forall x : El A, TYPE)
  (f : forall x : El A, El (B x)) : El (Prodᵉ A (mkPack _ true B)) :=
  mkPack _ true f.
*)

Definition Prodᵉ (A : TYPE) (B : El A -> TYPE) : TYPE :=
  mkTYPE (forall x : El A, El (B x)).

Definition Lamᵉ {A : TYPE} {B : forall x : El A, TYPE}
  (f : forall x : El A, El (B x)) : El (Prodᵉ A B) :=
  mkPack _ true f.

Definition Appᵉ {A : TYPE} {B : forall x : El A, TYPE}
  (f : El (Prodᵉ A B)) (x : El A) : El (B x) :=
  match f.(wit _) as wit return (if wit then forall x : El A, El (B x) else unit) -> El (B x) with
  | true => fun f => f x
  | false => fun _ => empty (B x)
  end f.(val _)
.

(*
Check Typeᵉ : El Typeᵉ.
Check Propᵉ : El Typeᵉ.
*)
