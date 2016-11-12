Set Universe Polymorphism.
Set Primitive Projections.

Axiom R : Type.

Record TYPE := {
  wit : R -> Type;
  prm : (forall p, wit p) -> Type;
}.

Definition Elᶠ (p : R) (T : TYPE) : Type := T.(wit) p.

Record Elᵇ (T : TYPE) : Type := mkᵇ {
  elt : forall q, T.(wit) q;
  box : T.(prm) elt
}.

Arguments elt {_} _ _.
Arguments box {_} _.

Definition Typeᶠ (p : R) : TYPE :=
  {| wit := fun _ => TYPE; prm := fun T => forall q, (T p).(wit) q = (T q).(wit) q |}.

Definition Typeᴿ (p : R) : (Typeᶠ p).(prm) Typeᶠ := fun _ => eq_refl.

Definition Typeᵇ (p : R) : Elᵇ (Typeᶠ p) :=
  mkᵇ (Typeᶠ p) Typeᶠ (Typeᴿ p).

Definition Πᶠ (p : R) (A : forall p, Elᵇ (Typeᶠ p)) (B : Elᵇ (A.(elt) p) -> Elᵇ (Typeᶠ p)) : TYPE.
Proof.
unshelve refine (
{|
  wit := fun p => forall x : Elᵇ (A.(elt) p), Elᶠ p (B x);
  prm := fun f => forall x : (forall q, Elᵇ q (A q)), (B p (x p)).(prm) (fun q => _)
|}
).
pose (f q (x q)).
pose (B p (x p)).(prm).

cbn.
  {| wit := fun _ => TYPE; prm := fun T => forall q, (T p).(wit) q = (T q).(wit) q |}.
