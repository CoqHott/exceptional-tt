Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
Axiom Ω : Type.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Definition M A := Ω -> prod A Ω.

Definition ret {A : Type} (x : A) : M A := fun ω => pair x ω.

Definition pointwise {A : Ω -> Type} (P : A -> Type) (x : prod A Ω) := P x.(fst).

Definition TYPE := M (sig (Ω -> Type) (fun A => forall ω, prod (A ω) Ω -> A ω)).

Definition El (A : TYPE) : Type :=
  forall ω, pointwise (fun A => forall ω, A.(wit) ω) (A ω).

Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun ω => f (x ω).(fst) (x ω).(snd).

(*
Definition hbind {A B} (x : M A) (f : A -> El B) : El B.
Proof.
refine (fun ω => _).
refine (_ (f (x ω).(
compute in *.
  fun ω => hwrite (pair (f (x ω).(fst)) (x ω).(snd)) ω.
*)

Definition Typeᶠ : TYPE.
Proof.
refine (ret _).
unshelve refine (exist _ _ (fun _ => TYPE) _).

unfold TYPE in *.
refine (@bind b _).


 := ret (exist _ _ TYPE (fun b => bind b (fun x => x))).

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

Definition bool_caseᶠ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶠ) : El P :=
  @hbind bool _ b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶠ P Pt Pf trueᶠ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶠ P Pt Pf falseᶠ) = (fun P Pt Pf => Pf)).
