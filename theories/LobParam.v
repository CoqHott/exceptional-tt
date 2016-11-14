Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.

Inductive unit := tt.

Inductive Ω : Type :=
| Ω0 : Ω
| ΩS : Ω -> Ω.

Record Pack (A : Ω -> Type) (Aᴿ : (forall ω : Ω, A ω) -> Type) := mkPack {
  elt : forall ω, A ω;
  prp : Aᴿ elt;
}.

Arguments elt {_ _} _.
Arguments prp {_ _} _.

Definition TYPE :=
  (Pack (fun (_ : Ω) => Type) (fun A => (forall ω : Ω, A ω) -> Type)).

Definition mkTYPE (A : Ω -> Type) (Aᴿ : (forall ω : Ω, A ω) -> Type) : TYPE :=
  mkPack (fun (_ : Ω) => Type) (fun A => (forall ω : Ω, A ω) -> Type) A Aᴿ.

Definition El (A : TYPE) : Type := Pack A.(elt) A.(prp).

Definition Typeᶠ : TYPE := mkTYPE
  (fun _ => Type)
  (fun A => (forall ω : Ω, A ω) -> Type).

Check Typeᶠ : El Typeᶠ.

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : TYPE :=
  mkTYPE
    (fun ω => forall x : El A, (B x).(elt) ω)
    (fun f => forall x : El A, (B x).(prp) (fun ω => f ω x)).

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω x => (f x).(elt) ω).
+ refine (fun x => (f x).(prp)).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (mkPack _ _ _ _).
+ refine (fun ω => f.(elt) ω x).
+ refine (f.(prp) x).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Definition Ωᶠ : TYPE := mkTYPE (fun _ => Ω) (fun _ => unit).

Definition readᶠ : El Ωᶠ := mkPack _ _ (fun ω => ω) tt.

Inductive boolᴿ : (Ω -> bool) -> Type :=
| trueᴿ : boolᴿ (fun _ => true)
| falseᴿ : boolᴿ (fun _ => false).

Definition boolᶠ : TYPE :=
  {| elt := fun _ => bool; prp := boolᴿ |}.

Definition trueᶠ : El boolᶠ := {| elt := fun _ => true; prp := trueᴿ |}.
Definition falseᶠ : El boolᶠ := {| elt := fun _ => false; prp := falseᴿ |}.

Definition bool_rectᶠ : El
  (Πᶠ (P : El (boolᶠ →ᶠ Typeᶠ)), Appᶠ P trueᶠ →ᶠ Appᶠ P falseᶠ →ᶠ
  Πᶠ (b : El boolᶠ), Appᶠ P b).
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
  (fun P Pt Pf => Appᶠ (Appᶠ (Appᶠ ((Appᶠ bool_rectᶠ) P) Pt) Pf) trueᶠ) = (fun P Pt Pf => Pt).

Eval compute in eq_refl :
  (fun P Pt Pf => Appᶠ (Appᶠ (Appᶠ ((Appᶠ bool_rectᶠ) P) Pt) Pf) falseᶠ) = (fun P Pt Pf => Pf).

Definition unitᶠ : TYPE := mkTYPE (fun _ => unit) (fun _ => unit).

Definition laterᶠ : El (Typeᶠ →ᶠ Typeᶠ).
Proof.
apply Lamᶠ; intros A.
unshelve refine (
  mkTYPE
    (fun ω => match ω with Ω0 => unit | ΩS ω => A.(elt) ω end)
    (fun x => forall ω : Ω, A.(prp) (fun ω => x (ΩS ω)))
).
Defined.

Definition nextᶠ : El (Πᶠ (A : El Typeᶠ), A →ᶠ Appᶠ laterᶠ A).
Proof.
apply Lamᶠ; intros A.
apply Lamᶠ; intros x.
unshelve refine (
  mkPack _ _
    (fun ω => match ω return elt (Appᶠ laterᶠ A) ω with Ω0 => tt | ΩS ω => x.(elt) ω end)
    (fun _ => _)
  ).
refine x.(prp).
Defined.

Definition predᶠ : El (Πᶠ (A : El Typeᶠ), Appᶠ laterᶠ A →ᶠ A).
Proof.
apply Lamᶠ; intros A.
apply Lamᶠ; intros x.
unshelve refine (
  mkPack _ _
    (fun ω => x.(elt) (ΩS ω)) _
  ).
refine (x.(prp) Ω0).
Defined.

Eval compute in fun A x => Appᶠ (Appᶠ predᶠ A) (Appᶠ (Appᶠ nextᶠ A) x).
Eval compute in fun A x => Appᶠ (Appᶠ nextᶠ A) (Appᶠ (Appᶠ predᶠ A) x).

Definition fixᶠ : El (Πᶠ (A : El Typeᶠ), (A →ᶠ Appᶠ laterᶠ A) →ᶠ A).
Proof.
apply Lamᶠ; intros A.
apply Lamᶠ; intros f.
unshelve refine (
  mkPack _ _
    (fun ω => _)
    _
  ).
+ cbn; induction ω.
  - exact tt.
  -


Definition fixᶠ : El (Πᶠ (A : El Typeᶠ), (Appᶠ laterᶠ A →ᶠ A) →ᶠ A).
Proof.
apply Lamᶠ; intros A.
apply Lamᶠ; intros f.
unfold El.
unshelve refine (
  mkPack (elt A) _
    (fun ω => _)
    _
  ).
+
  pose (f.(elt) ω).
cbn in *.
unfold Appᶠ, El in x.
cbn in *.
admit.
+
  induction ω as [|ω].

cbn in *.