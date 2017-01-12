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

Definition TYPE p := {A : Typeᵒ p & Typeᴿ p A}.
Definition El p (A : TYPE p) :=
  { x : forall (q : Ω) (α : Θ q p), A.(fst) q α & A.(snd).(fst) p (refl p) x }.

Definition Typeᶱ : forall p (A : Typeᵒ p) (Aε : Typeᴿ p A) q (α : Θ q p),
  Typeᴿ q (fun r β => A r (β ∘ α)).
Proof.
unshelve refine (fun p A Aε q α => exist _ _ _ _).
+ refine (fun r β x => Aε.(fst) r (β ∘ α) x).
+ refine (fun r β x xε s γ => _).
  refine (Aε.(snd) r (β ∘ α) x xε s γ).
Defined.

Definition Type0 p : TYPE p.
Proof.
unshelve refine (
  exist (Typeᵒ p) (Typeᴿ p) (fun q α => Type) (exist _ _ (fun q α => Typeᴿ q) _)
).
refine (fun q α A Aε r β => Typeᶱ q A Aε r β).
Defined.

Definition Typeᶠ p : El p (Type0 p) := Type0 p.

Definition TYPEᶱ p (A : TYPE p) q (α : Θ q p) : TYPE q :=
  exist (Typeᵒ q) (Typeᴿ q) (fun r β => A.(fst) r (β ∘ α)) (Typeᶱ p A.(fst) A.(snd) q α).

Definition θ {p} {A : TYPE p} (x : El p A) {q} (α : Θ q p) : El q (TYPEᶱ p A q α).
Proof.
unshelve refine (exist _ _ _ _).
+ refine (fun r β => x.(fst) r (β ∘ α)).
+ refine (A.(snd).(snd) p (refl p) x.(fst) x.(snd) q α).
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

Definition Arrowᵒ p (q : Ω) (α : Θ q p) (A : TYPE q) (B : TYPE q) : Type :=
  forall x : El q A, B.(fst) q (refl q).

Definition Arrowᴿ p (q : Ω) (α : Θ q p) (A : TYPE q) (B : TYPE q) :
  Typeᴿ q (fun r β => Arrowᵒ p r (β ∘ α) (TYPEᶱ q A r β) (TYPEᶱ q B r β)).
Proof.
unshelve refine (exist _ _ _ _); cbn in *.
  - unshelve refine
    (fun r β f =>
      forall
        (s : Ω) (γ : Θ s r) (x : El s (TYPEᶱ q A s (γ ∘ β))),
        B.(snd).(fst) s (γ ∘ β) (fun t δ => f t (δ ∘ γ) (θ x δ))
    ).
  - unshelve refine (fun r β f fε s γ t δ x => fε _ _ _).
Defined.

Definition Arrow0 p (A : El p (Typeᶠ p)) (B : El p (Typeᶠ p)) : El p (Typeᶠ p).
Proof.
unshelve refine (exist _ _ _ _).
+ refine (fun q α => Arrowᵒ p q α (θ A α) (θ B α)).
+ refine (Arrowᴿ p p (refl p) A B).
Defined.

(*
Definition Arrowᶠ p :
  { T :
    forall (q : Ω) (α : Θ q p)
    (A : TYPE q)
    (B : TYPE q),
    Type
  & forall (q : Ω) (α : Θ q p)
    (A : TYPE q)
    (B : TYPE q),
    Typeᴿ q (fun r β => T r (β ∘ α) (TYPEᶱ q A r β) (TYPEᶱ q B r β)) }
.
Proof.
unshelve refine (exist _ _ _ _).
+ refine (Arrowᵒ p).
+ refine (fun q α => Arrowᴿ q q (refl _)).
Defined.*)

(* Notation "A →ᶠ B" := (Arrowᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200). *)


(* Check (fun p => Arrowᶠ p) : forall p, El p (Arrowᶠ p Typeᶠ. *)

(**

Definition Arrowᵒ p
  (q : Ω) (α : Θ q p)
  (A : Typeᵒ q)
  (Aε : Typeᴿ q A)
  (B : Typeᵒ q)
  (Bε : Typeᴿ q B)
  : Type.
Proof.
refine (
  forall
    (x : (forall r (β : Θ r q), A r β))
    (xε : Aε.(fst) q (refl q) x),
    B q (refl q)
).
Defined.


Definition Arrowᴿ p
  (q : Ω) (α : Θ q p)
  (A : Typeᵒ q)
  (Aε : Typeᴿ q A)
  (B : Typeᵒ q)
  (Bε : Typeᴿ q B)
  : Typeᴿ q (fun r β =>
    Arrowᵒ q r β
      (fun s γ => A s (γ ∘ β))
      (Typeᶱ _ A Aε _ _)
      (fun s γ => B s (γ ∘ β))
      (Typeᶱ _ B Bε _ _)
  ).
Proof.
unshelve refine (exist _ _ _ _); unfold Arrowᵒ; cbn in *.
+ unshelve refine
  (fun r β f =>
    forall
      (s : Ω) (γ : Θ s r)
      (x : (forall t δ, A t (δ ∘ γ ∘ β)))
      (xε : Aε.(fst) s (γ ∘ β) x),
      Bε.(fst) s (γ ∘ β)
        (fun t δ => f t (δ ∘ γ) (fun u ε => x u (ε ∘ δ)) (Aε.(snd) s (γ ∘ β) x xε t δ))
  ).
+ unshelve refine (fun r β f fε s γ t δ x xε => fε _ _ _ _).
Defined.

Definition Prodᵒ p
  (q : Ω) (α : Θ q p)
  (A : Typeᵒ q)
  (Aε : Typeᴿ q A)
  (B : forall (r : Ω) (β : Θ r q)
    (x : forall (s : Ω) (γ : Θ s r), A s (γ ∘ β))
    (xε : Aε.(fst) r _ x), Type)
  (Bε : forall (r : Ω) (β : Θ r q)
    (x : forall (s : Ω) (γ : Θ s r), A s (γ ∘ β))
    (xε : Aε.(fst) r β x),
      Typeᴿ r (fun s γ => B s (γ ∘ β) (fun t δ => x t (δ ∘ γ)) (Aε.(snd) _ _ x xε _ _)))
  : Type.
Proof.
refine (
  forall
    (x : (forall r (β : Θ r q), A r β))
    (xε : Aε.(fst) q (refl q) x),
    B _ (refl _) x xε
).
Defined.

Definition Prodᴿ p
  (q : Ω) (α : Θ q p)
  (A : Typeᵒ q)
  (Aε : Typeᴿ q A)
  (B : forall (r : Ω) (β : Θ r q)
    (x : forall (s : Ω) (γ : Θ s r), A s (γ ∘ β))
    (xε : Aε.(fst) r _ x), Type)
  (Bε : forall (r : Ω) (β : Θ r q)
    (x : forall (s : Ω) (γ : Θ s r), A s (γ ∘ β))
    (xε : Aε.(fst) r β x),
      Typeᴿ r (fun s γ => B s (γ ∘ β) (fun t δ => x t (δ ∘ γ)) (Aε.(snd) _ _ x xε _ _)))
  :
  Typeᴿ q (fun r γ =>
      Prodᵒ q r γ
        (fun s δ => A s (δ ∘ γ))
        (Typeᶱ _ _ Aε _ _)
        (fun s δ x xε => B s (δ ∘ γ) x xε)
        (fun s δ x xε => Bε _ _ x xε)
    ).
Proof.
unshelve refine (exist _ _ _ _).
+ unshelve refine (
  fun r γ f =>
    forall
      (x : (forall s δ, A s (δ ∘ γ)))
      (xε : Aε.(fst) _ _ x),
      (Bε _ _ x xε).(fst) r (refl r)
        (fun s δ => f s _
          (fun t ε => x t (ε ∘ δ))
          (Aε.(snd) _ _ x xε _ _)
        )
).
+ unshelve refine (
    fun r γ f fε s δ x xε => _
  ).
cbn in *.
Abort.

*)

Inductive unitᵒ (p : Ω) := ttᵒ.
Inductive unitε (p : Ω) : (forall q (α : Θ q p), unitᵒ q) -> Type :=
| ttε : unitε p (fun q _ => ttᵒ q).

Definition unitᴿ p : Typeᴿ p (fun q α => unitᵒ q).
Proof.
unshelve refine (exist _ _ _ _).
+ refine (fun q α => unitε q).
+ unshelve refine (fun q α i iε r β => _).
  destruct iε; constructor.
Defined.

Definition unit_indᵒ
  (p : Ω)
  (q : Ω) (α : Θ q p)
  (P : forall r (β : Θ r q)
    (i : forall s (γ : Θ s r), unitᵒ s)
    (iε : (unitᴿ r).(fst) r (refl r) i),
    Type)
  (Pε : forall
    (i : forall r (β : Θ r q), unitᵒ r)
    (iε : (unitᴿ q).(fst) q (refl _) i),
    Typeᴿ q (fun r β =>
      P r β
        (fun s γ => i s (γ ∘ β))
        ((unitᴿ q).(snd) _ (refl q) i iε _ β)
    )
  )
  (π : forall r (β : Θ r q), P r β (fun s γ => ttᵒ s) (ttε r))
  (πε : (Pε (fun r β => ttᵒ r) (ttε q)).(fst) q (refl q) π)
  (i : forall r (β : Θ r q), unitᵒ r)
  (iε : (unitᴿ q).(fst) q (refl q) i) :
  P q (refl q) i iε.
Proof.
refine (
  match iε in unitε _ i return P q (refl q) i iε with
  | ttε _ => π _ _
  end
).
Defined.

(* Definition unit_indᴿ *)
Goal Type.
unshelve refine (forall
  (p : Ω)
  (q : Ω) (α : Θ q p)
  (P : forall r (β : Θ r q)
    (i : forall s (γ : Θ s r), unitᵒ s)
    (iε : (unitᴿ r).(fst) r (refl r) i),
    Type)
  (Pε : forall
    (i : forall r (β : Θ r q), unitᵒ r)
    (iε : (unitᴿ q).(fst) q (refl _) i),
    Typeᴿ q (fun r β =>
      P r β
        (fun s γ => i s (γ ∘ β))
        ((unitᴿ q).(snd) _ (refl q) i iε _ β)
    )
  )
  (π : forall r (β : Θ r q), P r β (fun s γ => ttᵒ s) (ttε r))
  (πε : (Pε (fun r β => ttᵒ r) (ttε q)).(fst) q (refl q) π)
  (i : forall r (β : Θ r q), unitᵒ r)
  (iε : (unitᴿ q).(fst) q (refl q) i)
  ,
  (Pε i iε).(fst) q (refl q)
    (fun r β =>
      unit_indᵒ q r β
        (fun s γ i iε => P s (γ ∘ β) i iε)
        (fun i iε => _)
        (fun s γ => π s (γ ∘ β))
        _
        (fun s γ => i s (γ ∘ β))
        ((unitᴿ q).(snd) q (refl q) i iε r β)
  )).


cbn in *.
pose (unitᴿ r).(snd).
cbn in *.

refine (let X := Typeᶱ q (fun r β => P r β (fun s γ => i s (γ ∘ β)) _) in _).


pose (Typeᶱ r (fun s γ =>
  P s (γ ∘ β)
    (fun t δ => i t (δ ∘ γ))
    ((unitᴿ r).(snd) r (refl r) i iε _ _)
)).
cbn in *.
refine (Typeᶱ q (fun s γ => P s γ _ _) _ r β).
refine (Pε _ _).
