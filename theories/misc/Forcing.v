Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.

Axiom Ω : Type.
Axiom R : Ω -> Ω -> Type.
Definition Θ ω₁ ω₂ := forall ρ, R ω₁ ρ -> R ω₂ ρ.
Definition refl {ω} : Θ ω ω := fun _ k => k.
Definition trns {ω₁ ω₂ ω₃} (f : Θ ω₁ ω₂) (g : Θ ω₂ ω₃) : Θ ω₁ ω₃ :=
  fun _ k => g _ (f _ k).

Record Pack ω
  (A : forall ω₀ ω₁, Θ ω₁ ω₀ -> Type) :=
mkPack {
  src : Ω;
  rel : Θ ω src;
  elt : forall ω (α : Θ ω src), A _ _ α;
}.

Arguments src {_ _} _.
Arguments rel {_ _} _.
Arguments elt {_ _} _.

Definition TYPEi ω := @Pack ω (fun _ _ _ => Type).
Definition TYPE := forall ω, (@Pack ω (fun _ _ _ => Type)).

Definition Eli (A : TYPE) (ω : Ω) : Type :=
  Pack ω (fun ω₀ ω₁ α => (A ω₁).(elt) ω₁ (A ω₁).(rel)).
Definition El (A : TYPE) : Type :=
  forall ω, Pack ω (fun ω₀ ω₁ α => (A ω₁).(elt) ω₁ (A ω₁).(rel)).

Definition lift {A : TYPE} {ω₀ ω₁} (α : Θ ω₁ ω₀) (x : Eli A ω₀) : Eli A ω₁ :=
  mkPack _ _ _ (trns α x.(rel)) x.(elt).

Definition Typeᶠ : TYPE := fun ω =>
  mkPack
  ω
  (fun _ _ _ => Type)
  ω
  refl
  (fun _ _ => Type).

Check Typeᶠ : El Typeᶠ.

(*
Definition mkTYPE (A : Ω -> Type) (Aᴿ : (forall ω : Ω, A ω) -> Type) : El Typeᶠ :=
  mkPack (fun (_ : Ω) => Type) (fun A => (forall ω : Ω, A ω) -> Type) A Aᴿ.

Definition mkEl (A : TYPE) (x : forall ω, A.(elt) ω) (xᴿ : A.(prp) x) : El A :=
  mkPack _ _ x xᴿ.
*)

Definition Prodᶠ (A : TYPE) (B : forall ω, Pack ω (fun ω₀ ω₁ α => forall x : Eli A ω₁, Type)) : TYPE.
Proof.
refine (
  fun ω =>
    mkPack ω
    (fun _ _ _ => Type)
    ω
    refl
    (fun ω₀ α => forall x : Eli A ω₀, _)
).
refine (
  (B ω₀).(elt) ω₀ (B ω₀).(rel) x
).
Defined.

Definition Arrowᶠ (A B : TYPE) : TYPE :=
  Prodᶠ A (fun ω => mkPack _ _ ω refl (fun ω₀ α _ => (B ω₀).(elt) ω₀ (B ω₀).(rel))).

Notation "A →ᶠ B" := (Arrowᶠ A B) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lam₀ᶠ {A} {B} (f : forall ω, Eli A ω -> Eli B ω) : El (A →ᶠ B).
Proof.
refine (fun ω => mkPack _ _ ω refl (fun ω₀ α x => (f ω₀ x).(elt) _ (f ω₀ x).(rel))).
Defined.

Definition App₀ᶠ {A} {B} (f : El (A →ᶠ B)) (x : El A) : El B.
Proof.
refine (fun ω => mkPack _ _ ω refl (fun ω₀ α => _)).
refine ((f ω₀).(elt) ω₀ (f ω₀).(rel) (x ω₀)).
Defined.



Definition Lamᶠ {A} {B : El (A →ᶠ Typeᶠ)}
  (f : forall ω (x : Eli A ω), Eli B) : El (Prodᶠ A B).
Proof.
unshelve refine (fun ω => mkPack ω _ ω refl _).
refine (fun ω₀ α x => f _ x _ refl).
Defined.

Eval compute in (fun A B f x => @App₀ᶠ A B (Lamᶠ f) x) = (fun A B f x ω => mkPack _ _ ω refl (f ω (x ω))).
Eval compute in fun A B f x => @App₀ᶠ A B (Lamᶠ f) x.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A} {B : El (A →ᶠ Typeᶠ)} (f : El (Prodᶠ A B)) (x : El A) :
  forall ω, Eli ((B ω).(elt) _ (B ω).(rel) (x ω)) ω.
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω => f.(elt) ω x).
+ refine (f.(prp) x).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Notation "t · u" := (Appᶠ t u) (at level 11, left associativity).

Definition Ωᶠ : TYPE := {| elt := fun _ => Ω; prp := fun _ => unit |}.

Definition readᶠ : El Ωᶠ := mkPack _ _ (fun ω => ω) tt.

Inductive boolᴿ : (Ω -> bool) -> Type :=
| trueᴿ : boolᴿ (fun _ => true)
| falseᴿ : boolᴿ (fun _ => false).

Definition boolᶠ : TYPE :=
  {| elt := fun _ => bool; prp := boolᴿ |}.

Definition trueᶠ : El boolᶠ := {| elt := fun _ => true; prp := trueᴿ |}.
Definition falseᶠ : El boolᶠ := {| elt := fun _ => false; prp := falseᴿ |}.

Definition bool_rectᶠ : El
  (Πᶠ (P : El (boolᶠ →ᶠ Typeᶠ)), P · trueᶠ →ᶠ P · falseᶠ →ᶠ
  Πᶠ (b : El boolᶠ), P · b).
Proof.
apply Lamᶠ; intros P.
apply Lamᶠ; intros Pt.
apply Lamᶠ; intros Pf.
apply Lamᶠ; intros b.
refine (
match b.(prp) as br in boolᴿ b return El (Appᶠ P (mkPack _ _ b br)) with
| trueᴿ => Pt
| falseᴿ => Pf
end
).
Defined.

Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · trueᶠ) = (fun P Pt Pf => Pt).
Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · falseᶠ) = (fun P Pt Pf => Pf).

Inductive natᵀ :=
| Oᵀ : natᵀ
| Sᵀ : (Ω -> natᵀ) -> natᵀ.

Inductive natᴿ : (Ω -> natᵀ) -> Type :=
| Oᴿ : natᴿ (fun _ => Oᵀ)
| Sᴿ : forall n, natᴿ n -> natᴿ (fun _ => Sᵀ n).

Definition natᶠ : TYPE := {| prp := natᴿ |}.

Definition Oᶠ : El natᶠ := {| prp := Oᴿ |}.
Definition Sᶠ : El (natᶠ →ᶠ natᶠ) :=
  Lamᶠ (fun n : El natᶠ => mkPack _ natᶠ.(prp) (fun ω => Sᵀ n.(elt)) (Sᴿ n.(elt) n.(prp))).

Definition nat_rectᶠ : El (
  (Πᶠ (P : El (natᶠ →ᶠ Typeᶠ)), P · Oᶠ →ᶠ (Πᶠ (n : El natᶠ), P · n →ᶠ P · (Sᶠ · n)) →ᶠ
  Πᶠ (n : El natᶠ), P · n)).
Proof.
apply Lamᶠ; intros P.
apply Lamᶠ; intros P0.
apply Lamᶠ; intros PS.
apply Lamᶠ; intros n.
destruct n as [n nᴿ]; induction nᴿ; cbn.
+ apply P0.
+ refine (PS · (mkPack _ _ n nᴿ) · IHnᴿ).
Defined.

Check (eq_refl : (fun P P0 PS n => nat_rectᶠ · P · P0 · PS · Oᶠ) = (fun P P0 PS n => P0)).
Check (eq_refl : (fun P P0 PS n => nat_rectᶠ · P · P0 ·  PS · (Sᶠ · n)) = (fun P P0 PS n => PS · n · (nat_rectᶠ · P · P0 · PS · n))).

Inductive eqᵀ (A : TYPE) (x : El A) : El A -> Type :=
| reflᵀ : eqᵀ A x x.

Inductive eqᴿ (A : TYPE) (x : El A) : forall y, (Ω -> eqᵀ A x y) -> Type :=
| reflᴿ : eqᴿ A x x (fun _ => reflᵀ A x).

Definition eqᶠ : El (Πᶠ (A : El Typeᶠ), A →ᶠ A →ᶠ Typeᶠ) :=
  λᶠ (A : El Typeᶠ) x y, mkTYPE (fun _ => eqᵀ A x y) (eqᴿ A x y).

Definition reflᶠ : El (Πᶠ (A : El Typeᶠ) (x : El A), eqᶠ · A · x · x) :=
  λᶠ (A : El Typeᶠ) x, mkEl (eqᶠ · A · x · x) (fun _ => reflᵀ A x) (reflᴿ A x).

Definition eq_rectᶠ : El (
  Πᶠ (A : El Typeᶠ) (x : El A) (P : El (Πᶠ (y : El A), eqᶠ · A · x · y →ᶠ Typeᶠ)),
  P · x · (reflᶠ · A · x) →ᶠ Πᶠ (y : El A) (e : El (eqᶠ · A · x · y)), P · y · e).
Proof.
refine (λᶠ A x P Prefl y e, _).
destruct e as [e eᴿ]; induction eᴿ.
apply Prefl.
Defined.

Inductive Falseᴿ : (Ω -> False) -> Type :=.

Definition Falseᶠ := mkTYPE (fun _ => False) Falseᴿ.

(** Playing with types *)

Definition Propᶠ := mkTYPE (fun _ => Prop) (fun A => (forall ω : Ω, A ω) -> Prop).

(** Impredicative product *)
Definition iProdᶠ (A : TYPE) (B : El A -> El Propᶠ) : El Propᶠ :=
  mkPack
    (fun (_ : Ω) => Prop)
    (fun A => (forall ω : Ω, A ω) -> Prop)
    (fun ω => forall x : El A, (B x).(elt) ω)
    (fun f => forall x : El A, (B x).(prp) (fun ω => f ω x)).

Definition i (A : El Propᶠ) : El Typeᶠ := mkTYPE A.(elt) A.(prp).

Notation "A i→ᶠ B" := (iProdᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).

Section NegPropext.

Variable Ω_is_nat : Ω = nat.

Definition of_nat := match Ω_is_nat in _ = A return A -> Ω with eq_refl => fun x => x end.
Definition to_nat := match Ω_is_nat in _ = A return Ω -> A with eq_refl => fun x => x end.

Lemma cast_id : forall n, to_nat (of_nat n) = n.
Proof.
intros n.
compute.
destruct Ω_is_nat.
reflexivity.
Qed.

Definition P₀ : El Propᶠ.
Proof.
unshelve refine (mkPack _ _ (fun ω => _) (fun _ => True)); cbn.
refine ((fix F n := match n with 0 => True | 1 => False | S (S n) => F n end) (to_nat ω)).
Defined.

Definition P₁ : El Propᶠ.
Proof.
unshelve refine (mkPack _ _ (fun ω => _) (fun _ => True)); cbn.
refine ((fix F n := match n with 0 => False | 1 => True | S (S n) => F n end) (to_nat ω)).
Defined.

Lemma not_commut : forall A : El Typeᶠ, (El A -> False) -> El (A →ᶠ Falseᶠ).
Proof.
intros A f.
apply Lamᶠ; intros x; elim (f x).
Qed.

Lemma neg_propext : El (Πᶠ (A B : El Propᶠ),
  i (i A i→ᶠ B) →ᶠ i (i B i→ᶠ A) →ᶠ eqᶠ · Propᶠ · A · B) -> False.
Proof.
intros F.
apply elt with (ω := of_nat 0) in F.
specialize (F P₀ P₁); cbn in *.
cut (eqᵀ Propᶠ P₀ P₁ -> False); [intros f; apply f; clear f; apply F|]; clear F.
+ unshelve refine (mkPack _ _ _ _).
  - intros ω e.
    pose (c := e.(elt) (of_nat 1)); clearbody c.
    cbn in c; rewrite cast_id in c; elim c.
  - cbn; intros _; exact I.
+ unshelve refine (mkPack _ _ _ _).
  - intros ω e.
    pose (c := e.(elt) (of_nat 0)); clearbody c.
    cbn in c; rewrite cast_id in c; elim c.
  - cbn; intros _; exact I.
+ intros e; assert (rw : P₀ = P₁) by (destruct e; reflexivity); clear e.
  apply f_equal with (f := fun P => elt P (of_nat 0)) in rw.
  revert rw; cbn.
  rewrite cast_id.
  intros []; exact I.
Qed.
