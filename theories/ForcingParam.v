Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
Axiom Ω : Type.

Record Pack (A : Ω -> Type) (Aᴿ : Ω -> (forall ω : Ω, A ω) -> Type) := mkPack {
  elt : forall ω, A ω;
  prp : forall ω, Aᴿ ω elt;
}.

Arguments elt {_ _} _.
Arguments prp {_ _} _.

Record TYPE := mkTYPE {
  wit : Ω -> Type;
  rel : Ω -> (forall ω : Ω, wit ω) -> Type;
}.

Definition El (A : TYPE) : Type := Pack A.(wit) A.(rel).

Definition Typeᶠ : TYPE := {|
  wit := fun _ => Type;
  rel := fun _ A => (forall ω : Ω, A ω) -> Type;
|}.

Definition Typeᵇ : El Typeᶠ.
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun _ => Type).
+ refine (fun _ A => (forall ω, A ω) -> Type).
Defined.

(** TYPE and El Typeᶠ are trivially isomorphic. *)

Definition inj (A : El Typeᶠ) : TYPE := mkTYPE A.(elt) A.(prp).
Definition prj (A : TYPE) : El Typeᶠ := mkPack _ _ A.(wit) A.(rel).

Notation "[ A ]" := (inj A).

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := fun ω => forall x : El A, (B x).(wit) ω;
  rel := fun ω f => forall x : El A, (B x).(rel) ω (fun ω => f ω x);
|}.

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω x => (f x).(elt) ω).
+ refine (fun ω x => (f x).(prp) ω).
Defined.

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω => f.(elt) ω x).
+ refine (fun ω => f.(prp) ω x).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Definition Ωᶠ : TYPE := {| wit := fun _ => Ω; rel := fun _ _ => unit |}.

Definition readᶠ : El Ωᶠ := mkPack _ _ (fun ω => ω) (fun _ => tt).

Inductive boolᴿ : (Ω -> bool) -> Type :=
| trueᴿ : boolᴿ (fun _ => true)
| falseᴿ : boolᴿ (fun _ => false).

Definition boolᶠ : TYPE :=
  {| wit := fun _ => bool; rel := fun _ => boolᴿ |}.

Definition trueᶠ : El boolᶠ := {| elt := fun _ => true; prp := fun _ => trueᴿ |}.
Definition falseᶠ : El boolᶠ := {| elt := fun _ => false; prp := fun _ => falseᴿ |}.

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
unshelve refine (mkPack _ _ _ _).
destruct b as [b bᴿ]; cbn in *.
+ intros ω.
cbn.
Admitted.
