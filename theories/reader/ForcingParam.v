Axiom Ω : Type.
Axiom R : Ω -> Ω -> Type.

Definition Θ : Ω -> Ω -> Type :=
  fun p q => forall r, R p r -> R q r.

Definition refl : forall p, Θ p p := fun p r k => k.
Definition trns : forall p q r, Θ p q -> Θ q r -> Θ p r := fun p q r θ₁ θ₂ s k =>
  θ₂ _ (θ₁ _ k).

Notation "α ∘ β" := (trns _ _ _ α β) (at level 35).

Goal forall (p : Ω) (q : Ω) (α : Θ q p)
  (A : forall (r : Ω) (β : Θ r q), Type)
  (x : forall (r : Ω) (β : Θ r q), A r β), A q (refl q).
Proof.
refine (
  fun p q α A x => x q (refl q)
).
Abort.

Set Universe Polymorphism.
Set Primitive Projections.

Record sigT (A : Type) (P : A -> Type) : Type := exist {
  fst : A;
  snd : P fst;
}.

Arguments fst {_ _} _.
Arguments snd {_ _} _.

Notation "{ x : A  & P }" := (sigT A (fun x => P)) : type_scope.

Definition Typeᵒ p := forall (q : Ω) (α : Θ q p), Type.
Definition Typeᴿ p (A : Typeᵒ p) := {
    Aε :
      forall (q : Ω) (α : Θ q p),
        (forall (r : Ω) (β : Θ r q), A r (β ∘ α)) -> Type
    &
      forall (q : Ω) (α : Θ q p),
      forall (x : forall r (β : Θ r q), A r (β ∘ α)),
        Aε q α x ->
        forall (r : Ω) (β : Θ r q),
        Aε r (β ∘ α) (fun s γ => x s (γ ∘ β))
}.

Definition Typeᶱ : forall p (A : Typeᵒ p) (Aε : Typeᴿ p A) q (α : Θ q p),
  Typeᴿ q (fun r β => A r (β ∘ α)).
Proof.
unshelve refine (fun p A Aε q α => exist _ _ _ _).
+ refine (fun r β x => Aε.(fst) r (β ∘ α) x).
+ refine (fun r β x xε s γ => _).
  refine (Aε.(snd) r (β ∘ α) x xε s γ).
Defined.

Goal forall (p : Ω),
  { f : (forall (q : Ω) (α : Θ q p)
    (A : Typeᵒ q)
    (Aε : Typeᴿ q A)
    (x : forall (r : Ω) (β : Θ r q), A r β)
    (xε : Aε.(fst) q (refl q) x),
    A q (refl q))
  &
    forall
    (A : Typeᵒ p)
    (Aε : Typeᴿ p A)
    (x : forall (r : Ω) (β : Θ r p), A r β)
    (xε : Aε.(fst) p (refl p) x),
    Aε.(fst) p (refl p)
      (fun q α => f q α
          (fun r β => A r (β ∘ α))
          (Typeᶱ _ A Aε _ _)
          (fun r β => x r (β ∘ α))
          (Aε.(snd) _ _ _ xε _ _)
      )
  }.
Proof.
unshelve refine (fun p => exist _ _ _ _).
refine (
  fun q α A Aε x xε => x q (refl q)
).
cbn.
refine (
  fun A Aε x xε => xε
).
Defined.
