Set Universe Polymorphism.
Set Primitive Projections.

Axiom Ω : Type.

Inductive list A :=
| nil : list A
| cons : A -> list A -> list A.

Fixpoint app {A} (l1 l2 : list A) : list A :=
match l1 with
| nil _ => l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Definition prod A B := sig A (fun _ => B).
Definition pair {A B} (x : A) (y : B) : prod A B := exist _ _ x y.

Definition M A := prod A (list Ω).

Definition ret {A} (x : A) : M A := pair x (nil Ω).

Definition pointwise {A} (f : A -> Type) (T : M A) : Type := f T.(wit).

Definition TYPE := M (sig Type (fun A => M A -> A)).

Definition mkTYPE (A : Type) (alg : M A -> A) : TYPE := pair (exist _ _ A alg) (nil Ω).

Definition El (A : TYPE) : Type := pointwise wit A.

Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  let r := f x.(wit) in
  pair r.(wit) (app x.(prf) r.(prf)).

Definition hbind {A B} (x : M A) (f : A -> El B) : El B :=
match x.(prf) with
| nil _ => f x.(wit)
| _ => B.(wit).(prf) (pair (f x.(wit)) x.(prf))
end.

Definition Typeᶫ : TYPE.
Proof.
refine (ret (exist _ _ TYPE _)).
refine (fun T => bind T (fun X => X)).
Defined.

Check Typeᶫ : El Typeᶫ.

Definition free A := mkTYPE (M A) (fun b => bind b (fun X => X)).

Definition pbind {A} {B : A -> El Typeᶫ} (x : M A) (f : forall x : A, El (B x)) : El (hbind x B) :=
match x.(prf) as p return El (hbind (pair x.(wit) p) B) with
| nil _ => f x.(wit)
| _ => (B _).(wit).(prf) (pair (f x.(wit)) x.(prf))
end.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE.
Proof.
refine (ret (exist _ _ (forall x : El A, El (B x)) _)).
refine (fun f x => hbind f (fun f => f x)).
Defined.

Notation "A →ᶫ B" := (Prodᶫ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶫ'  x .. y , P" := (Prodᶫ _ (fun x => .. (Prodᶫ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition pbind' {A R}
  {B : A -> El (R  →ᶫ Typeᶫ)}
  (x : M A) (r : El R) (f : forall x : A, El (B x r)) : El (hbind x B r) :=
match x.(prf) as p return El (hbind (pair x.(wit) p) B r) with
| nil _ => f x.(wit)
| _ => (B _ _).(wit).(prf) (pair (f x.(wit)) x.(prf))
end.

Definition boolᶫ : TYPE.
Proof.
refine (ret (exist _ _ (M bool) _)).
refine (fun b => bind b (fun b => b)).
Defined.

Definition trueᶫ : El boolᶫ := ret true.
Definition falseᶫ : El boolᶫ := ret false.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition θ_bool (n : El boolᶫ) : (El boolᶫ -> El Typeᶫ) -> El Typeᶫ :=
  bool_caseᶫ ((boolᶫ →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k trueᶫ) (fun k => k falseᶫ) n.

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b) :=
  pbind b (bool_rec _ Pt Pf).

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Inductive nat_ :=
| O_ : nat_
| S_ : M nat_ -> nat_.

Definition natᶫ : TYPE := mkTYPE (M nat_) (fun l => bind l (fun n => n)).

Definition Oᶫ : El natᶫ := ret O_.
Definition Sᶫ : El (natᶫ →ᶫ natᶫ) := fun n => ret (S_ n).

Definition nat_caseᶫ (P : TYPE) (P0 : El P) (PS : El natᶫ -> El P -> El P) (n : El natᶫ) : El P.
Proof.
refine (hbind n (fun n => _)).
refine ((fix F n := match n return El P with O_ => P0 | S_ n => PS n (hbind n F) end) n).
Defined.

Check (eq_refl : (fun P P0 PS n => nat_caseᶫ P P0 PS Oᶫ) = (fun P P0 PS n => P0)).
Check (eq_refl : (fun P P0 PS n => nat_caseᶫ P P0 PS (Sᶫ n)) = (fun P P0 PS n => PS n (nat_caseᶫ P P0 PS n))).

Definition θ_nat (n : El natᶫ) : (El natᶫ -> El Typeᶫ) -> El Typeᶫ :=
  nat_caseᶫ ((natᶫ →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k Oᶫ) (fun _ r k => r (fun n => k (Sᶫ n))) n.

Definition nat_rectᶫ (P : El natᶫ -> TYPE) (P0 : El (P Oᶫ)) (PS : forall n : El natᶫ, El (θ_nat n P) -> El (θ_nat (Sᶫ n) P)) (n : El natᶫ) :
  El (θ_nat n P).
Proof.
refine (pbind' n _ (fun n => _)).
match goal with [ |- El (?X n P) ] => set (K := X) end.
refine ((fix F n := match n return El (K n P) with O_ => P0 | S_ n => PS n _ end) n).
refine (@pbind' nat_ (Πᶫ _ : El natᶫ, Typeᶫ) _ n P F).
Defined.

Check (eq_refl : (fun P P0 PS n => nat_rectᶫ P P0 PS Oᶫ) = (fun P P0 PS n => P0)).
Check (eq_refl : (fun P P0 PS n => nat_rectᶫ P P0 PS (Sᶫ n)) = (fun P P0 PS n => PS n (nat_rectᶫ P P0 PS n))).

(** Proving that linear terms commute with storage operators *)

Inductive box (A : TYPE) := Box : El A -> box A.

Definition boxᶫ (A : TYPE) : TYPE :=
  mkTYPE (M (box A)) (fun b => bind b (fun b => b)).

Definition Boxᶫ (A : TYPE) (x : El A) : El (boxᶫ A) := ret (Box _ x).

Definition box_rectᶫ (A : TYPE) (P : TYPE) (pb : El A -> El P) (b : El (boxᶫ A)) : El P :=
  hbind b (fun b => box_rect A (fun _ => El P) pb b).

(** Linear definition taken from Paul Blain Levy last POPL article. *)
Definition linear {A B} (f : El (A →ᶫ B)) : Prop :=
  forall b : El (boxᶫ A), f (box_rectᶫ _ _ (fun x => x) b) = box_rectᶫ _ _ f b.
