Set Universe Polymorphism.
Set Primitive Projections.

Record Pack (A₀ A₁ : Type) (Aᴿ : A₀ -> A₁ -> Type) := mkPack {
  el₀ : A₀;
  el₁ : A₁;
  prp : Aᴿ el₀ el₁;
}.

Arguments el₀ {_ _ _} _.
Arguments el₁ {_ _ _} _.
Arguments prp {_ _ _} _.

Definition TYPE :=
  (Pack Type Type (fun A₀ A₁ => A₀ -> A₁ -> Type)).

Definition mkTYPE (A₀ A₁: Type) (Aᴿ : A₀ -> A₁ -> Type) :=
  mkPack Type Type (fun A₀ A₁ => A₀ -> A₁ -> Type) A₀ A₁ Aᴿ.

Definition El (A : TYPE) : Type := Pack A.(el₀) A.(el₁) A.(prp).

Definition Typeᶠ : TYPE :=
  mkTYPE Type Type (fun A₀ A₁ => A₀ -> A₁ -> Type).

Check Typeᶠ : El Typeᶠ.

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : TYPE :=
  mkTYPE
    (forall x : El A, (B x).(el₀))
    (forall x : El A, (B x).(el₁))
    (fun f₀ f₁ => forall x : El A, (B x).(prp) (f₀ x) (f₁ x)).

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (mkPack _ _ _ _ _ _).
+ refine (fun x => (f x).(el₀)).
+ refine (fun x => (f x).(el₁)).
+ refine (fun x => (f x).(prp)).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (mkPack _ _ _ _ _ _).
+ refine (f.(el₀) x).
+ refine (f.(el₁) x).
+ refine (f.(prp) x).
Defined.

Notation "t · u" := (Appᶠ t u) (at level 65, left associativity).

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Inductive boolᴿ : bool -> bool -> Type :=
| trueᴿ : boolᴿ true true
| falseᴿ : boolᴿ false false.

Definition boolᶠ : TYPE := mkTYPE bool bool boolᴿ.

Definition trueᶠ : El boolᶠ := {| prp := trueᴿ |}.
Definition falseᶠ : El boolᶠ := {| prp := falseᴿ |}.

Definition bool_rectᶠ : El
  (Πᶠ (P : El (boolᶠ →ᶠ Typeᶠ)), P · trueᶠ →ᶠ P · falseᶠ →ᶠ
  Πᶠ (b : El boolᶠ), P · b).
Proof.
apply Lamᶠ; intros P.
apply Lamᶠ; intros Pt.
apply Lamᶠ; intros Pf.
apply Lamᶠ; intros b.
refine (
match b.(prp) as br in boolᴿ b₀ b₁ return El (Appᶠ P (mkPack _ _ _ b₀ b₁ br)) with
| trueᴿ => Pt
| falseᴿ => Pf
end
).
Defined.

Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · trueᶠ) = (fun P Pt Pf => Pt).

Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · falseᶠ) = (fun P Pt Pf => Pf).

Inductive sumᵀ (A B : TYPE) : Type :=
| inlᵀ : El A -> sumᵀ A B
| inrᵀ : El B -> sumᵀ A B.

Inductive sumᴿ (A B : TYPE) : sumᵀ A B -> sumᵀ A B -> Type :=
| inlᴿ : forall x, sumᴿ A B (inlᵀ _ _ x) (inlᵀ _ _ x)
| inrᴿ : forall y, sumᴿ A B (inrᵀ _ _ y) (inrᵀ _ _ y)
.

Definition sumᶠ : El (Typeᶠ →ᶠ Typeᶠ →ᶠ Typeᶠ).
Proof.
apply Lamᶠ; intros A; apply Lamᶠ; intros B.
refine (mkTYPE (sumᵀ A B) (sumᵀ A B) (sumᴿ A B)).
Defined.

Inductive emptyᵀ : Type := .
Inductive emptyᴿ : emptyᵀ -> emptyᵀ -> Type := .
Definition emptyᶠ := mkTYPE emptyᵀ emptyᵀ emptyᴿ.
