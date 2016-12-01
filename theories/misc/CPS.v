Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
Axiom Ω : Type.

Inductive unit := tt.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Definition M A := (A -> Ω) -> Ω.
Definition ret {A} (x : A) : M A := fun k => k x.

(** The underlying type is the type of stacks *)
Inductive Typeᴿ : ((Type -> Ω) -> Ω) -> Type :=
| IsType : forall (A : Type), ((A -> Ω) -> Type) -> Typeᴿ (ret A)
.

Definition TYPE := sig (M Type) Typeᴿ.

Definition Typeᶠ : TYPE :=
  exist _ _ (ret (Type -> Ω)) (IsType _ Typeᴿ).

Definition C (A : TYPE) : Type :=
  match A.(prf) with IsType A Aᴿ => A end.

Definition Cᴿ (A : TYPE) : (C A -> Ω) -> Type :=
  match A.(prf) as T return
    (match T with IsType A _ => _ end -> _) -> Type
  with IsType A Aᴿ => Aᴿ end.

Definition El (A : TYPE) : Type := sig (C A -> Ω) (Cᴿ A).

Check Typeᶠ : El Typeᶠ.

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : TYPE.
Proof.
unshelve refine (exist _ _ (ret _) _).
+ refine (sig (El A) (fun x => C (B x))).
+ refine (IsType _ (fun f => _)).
  refine (forall x : El A, Cᴿ (B x) (fun ω => f (exist _ _ x ω))).
Defined.

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (exist _ _ (fun ω => _) _).
+ unshelve refine ((f ω.(wit)).(wit) ω.(prf)).
+ unshelve refine (fun x => (f x).(prf)).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (exist _ _ (fun ω => f.(wit) (exist _ _ x ω)) _).
unshelve refine (f.(prf) _).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Notation "t · u" := (Appᶠ t u) (at level 11, left associativity).

Inductive Falseᴿ : M False -> Type :=.

Definition Falseᶠ : TYPE :=
  exist _ _ (ret (False -> Ω)) (IsType _ Falseᴿ).

Definition squash : El (Typeᶠ →ᶠ Typeᶠ).
Proof.
refine (λᶠ A, _).
unshelve refine (exist _ _ (ret (C A)) (IsType _ _)).
unshelve refine (fun _ => unit).
Defined.

Lemma cc : El (Πᶠ (A B : El Typeᶠ), ((A →ᶠ squash · B) →ᶠ A) →ᶠ squash · A).
Proof.
refine (λᶠ A B f, _).
simple refine (exist _ _ (fun ω => _) _).
+ unshelve refine ((f).(wit) (exist _ _ _ _)); [|refine ω].
  unshelve refine (exist _ _ (fun k => (k.(wit).(wit) ω)) _).
  refine (fun _ => tt).
+ refine tt.
Defined.

Inductive boolᴿ : M bool -> Type :=
| trueᴿ : boolᴿ (ret true)
| falseᴿ : boolᴿ (ret false).

Definition boolᶠ : TYPE :=
  exist _ _ (ret (bool -> Ω)) (IsType _ boolᴿ).

Definition trueᶠ : El boolᶠ := exist _ _ _ trueᴿ.
Definition falseᶠ : El boolᶠ := exist _ _ _ falseᴿ.

Definition bool_rectᶠ : El
  (Πᶠ (P : El (boolᶠ →ᶠ Typeᶠ)), P · trueᶠ →ᶠ P · falseᶠ →ᶠ
  Πᶠ (b : El boolᶠ), P · b).
Proof.
refine (λᶠ P Pt Pf b, _).
refine (
match b.(prf) as br in boolᴿ b return El (Appᶠ P (exist _ _ _ br)) with
| trueᴿ => Pt
| falseᴿ => Pf
end
).
Defined.

Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · trueᶠ) = (fun P Pt Pf => Pt).
Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · falseᶠ) = (fun P Pt Pf => Pf).
