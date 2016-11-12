Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
Axiom Ω : Type.

Record Pack (A : Ω -> Type) (Aᴿ : (forall ω : Ω, A ω) -> Type) := mkPack {
  elt : forall ω, A ω;
  prp : Aᴿ elt;
}.

Arguments elt {_ _} _.
Arguments prp {_ _} _.

Record TYPE := mkTYPE {
  wit : Ω -> Type;
  rel : (forall ω : Ω, wit ω) -> Type;
}.

Definition El (A : TYPE) : Type := Pack A.(wit) A.(rel).

Definition Typeᶠ : TYPE := {|
  wit := fun _ => Type;
  rel := fun A => (forall ω : Ω, A ω) -> Type;
|}.

Definition Typeᵇ : El Typeᶠ.
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun _ => Type).
+ refine (fun A => (forall ω, A ω) -> Type).
Defined.

(** TYPE and El Typeᶠ are trivially isomorphic.
    We could do without expliciting the iso but that would require ugly bootstrapping. *)

Definition inj (A : El Typeᶠ) : TYPE := mkTYPE A.(elt) A.(prp).
Definition prj (A : TYPE) : El Typeᶠ := mkPack _ _ A.(wit) A.(rel).

Notation "[ A ]" := (inj A).

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := fun ω => forall x : El A, (B x).(wit) ω;
  rel := fun f => forall x : El A, (B x).(rel) (fun ω => f ω x);
|}.

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω x => (f x).(elt) ω).
+ refine (fun x => (f x).(prp)).
Defined.

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω => f.(elt) ω x).
+ refine (f.(prp) x).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Definition Ωᶠ : TYPE := {| wit := fun _ => Ω; rel := fun _ => unit |}.

Definition readᶠ : El Ωᶠ := mkPack _ _ (fun ω => ω) tt.

Inductive boolᴿ : (Ω -> bool) -> Type :=
| trueᴿ : boolᴿ (fun _ => true)
| falseᴿ : boolᴿ (fun _ => false).

Definition boolᶠ : TYPE :=
  {| wit := fun _ => bool; rel := boolᴿ |}.

Definition trueᶠ : El boolᶠ := {| elt := fun _ => true; prp := trueᴿ |}.
Definition falseᶠ : El boolᶠ := {| elt := fun _ => false; prp := falseᴿ |}.

Definition bool_rectᶠ : El
  (Prodᶠ
    (Prodᶠ boolᶠ (fun _ => Typeᶠ)) (fun P =>
      Prodᶠ [Appᶠ P trueᶠ] (fun _ =>
        Prodᶠ [Appᶠ P falseᶠ] (fun _ => Prodᶠ boolᶠ (fun b => [Appᶠ P b])))
  )).
Proof.
apply Lamᶠ; intros P.
apply Lamᶠ; intros Pt.
apply Lamᶠ; intros Pf.
apply Lamᶠ; intros b.
refine (
match b.(prp) as br in boolᴿ b return El [Appᶠ P (mkPack _ _ b br)] with
| trueᴿ => Pt
| falseᴿ => Pf
end
).
Defined.

Eval compute in eq_refl :
  (fun P Pt Pf => Appᶠ (Appᶠ (Appᶠ ((Appᶠ bool_rectᶠ) P) Pt) Pf) trueᶠ) = (fun P Pt Pf => Pt).

Eval compute in eq_refl :
  (fun P Pt Pf => Appᶠ (Appᶠ (Appᶠ ((Appᶠ bool_rectᶠ) P) Pt) Pf) falseᶠ) = (fun P Pt Pf => Pf).
