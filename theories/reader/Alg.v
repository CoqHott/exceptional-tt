Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
Axiom Ω : Type.

Definition M A := Ω -> A.

Definition pointwise {A} (P : A -> Type) (x : M A) ω := P (x ω).

Definition TYPE := M Type.

Definition El (A : TYPE) : Type :=
  forall ω, pointwise (fun X => X) A ω.

Definition ret {A} (x : A) : M A := fun ω => x.

Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun ω => f (x ω) ω.

Definition hbind {A B} (x : M A) (f : A -> El B) : El B :=
  fun ω => f (x ω) ω.

Definition Typeᶠ : TYPE := ret Type.

Check Typeᶠ : El Typeᶠ.

Definition mkTYPE (A : Ω -> Type) : El Typeᶠ := A.

Definition mkEl (A : TYPE) (x : forall ω, A ω) : El A := x.

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : TYPE :=
    (fun ω => forall x : El A, (B x) ω).

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
refine (fun ω x => (f x) ω).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
refine (fun ω => f ω x).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Notation "t · u" := (Appᶠ t u) (at level 11, left associativity).

Definition boolᶠ : TYPE := fun _ => bool.

Definition trueᶠ : El boolᶠ := (fun _ => true).
Definition falseᶠ : El boolᶠ := (fun _ => false).

Definition bool_caseᶠ : El (Πᶠ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶠ), P) :=
  λᶠ P Pt Pf b,
  @hbind bool _ b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶠ · P · Pt · Pf · trueᶠ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶠ · P · Pt · Pf · falseᶠ) = (fun P Pt Pf => Pf)).

Definition θ_bool : El (Πᶠ (n : El boolᶠ), (boolᶠ →ᶠ Typeᶠ) →ᶠ Typeᶠ) :=
  λᶠ n,
  bool_caseᶠ · ((boolᶠ →ᶠ Typeᶠ) →ᶠ Typeᶠ) ·
    (Lamᶠ (fun k => k · trueᶠ)) · (Lamᶠ (fun k => k · falseᶠ)) · n.

Inductive box (A : TYPE) := Box : El A -> box A.

Definition boxᶠ : El (Typeᶠ →ᶠ Typeᶠ) := λᶠ A, fun ω => box A.

Definition Boxᶠ : El (Πᶠ (A : El Typeᶠ), A →ᶠ boxᶠ · A) :=
  λᶠ A x, fun ω => Box A x.

Definition box_caseᶠ : El (Πᶠ (A : El Typeᶠ) (P : El Typeᶠ),
  (A →ᶠ P) →ᶠ boxᶠ · A →ᶠ P) :=
  λᶠ A P f b, @hbind (box A) _ b
    (fun b => match b return El P with Box _ x => f · x end).

Definition equiv {A} (x y : El A) := forall ω, x ω = y ω.

Notation "x ≡ y" := (equiv x y) (at level 70, no associativity).

(** Linear definition taken from Paul Blain Levy *)
Definition linear {A B} (f : El (A →ᶠ B)) : Prop :=
  forall b : El (boxᶠ · A),
    f · (box_caseᶠ · A · A · (λᶠ x, x) · b) ≡ box_caseᶠ · A · B · f · b.

Lemma linear_bool_storage_compat : forall (P : El (boolᶠ →ᶠ Typeᶠ)),
  linear P -> forall n, θ_bool · n · P ≡ P · n.
Proof.
intros P HP b ω.
compute.
pose (b₀ := fun ω => Box _ (fun _ => b ω)).
specialize (HP b₀ ω).
compute in HP; revert HP; clear b₀.
destruct (b ω); intuition.
Qed.
