Set Universe Polymorphism.
Set Primitive Projections.

Axiom E : Type.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Inductive M (A : Type) :=
| Ok : A -> M A
| Err : E -> M A.

Fixpoint map {A B} (f : A -> B) (l : M A) : M B :=
match l with
| Ok _ x => Ok _ (f x)
| Err _ e => Err _ e
end.

Fixpoint pointwise {A} (f : A -> Type) (l : M A) : Type :=
match l with
| Ok _ x => f x
| Err _ _ => E
end.

Definition hlist (T : M Type) := pointwise (fun A => A) T.
Definition is_alg (T : M Type) := pointwise (fun A => M A -> A) T.

Record TYPE := {
  wit : M Type;
  alg : is_alg wit;
}.

Definition El (A : TYPE) : Type := hlist A.(wit).

Fixpoint bind {A B} (l : M A) (f : A -> M B) : M B :=
match l with
| Ok _ x => f x
| Err _ e => Err _ e
end.

Fixpoint pointwise_alg {T} (f : is_alg T) (l : M (hlist T)) : hlist T :=
match T return is_alg T -> M (hlist T) -> hlist T with
| Ok _ x => fun f l => f l
| Err _ e => fun f l => e
end f l.

Definition Typeᶫ : TYPE.
Proof.
refine {|
  wit := Ok _ TYPE;
  alg := fun T => {| wit := bind T wit; alg := _ |};
|}.
unfold is_alg.
destruct T as [A|e].
+ apply A.(alg).
+ exact e.
Defined.

Check Typeᶫ : El Typeᶫ.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := Ok _ (forall x : El A, El (B x));
  alg := fun f x => pointwise_alg (B x).(alg) (map (fun f => f x) f)
|}.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition boolᶫ : TYPE := {| wit := Ok _ (M bool); alg := fun b => bind b (fun b => b) |}.
Definition trueᶫ : El boolᶫ := Ok _ true.
Definition falseᶫ : El boolᶫ := Ok _ false.

Fixpoint hbind {A B} (l : M A) (f : A -> El B) {struct l} : El B :=
match l with
| Ok _ x => f x
| Err _ e => pointwise_alg B.(alg) (Err _ e)
end.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b).
Proof.
induction b as [be|be b IHb]; cbn in *.
+ destruct be; [exact Pt|exact Pf].
+ exact be.
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition Eᶫ : El Typeᶫ :=
  {| wit := Ok _ E; alg := fun e => match e with Ok _ e => e | Err _ e => e end |}.

Definition fail : El (Prodᶫ Eᶫ (fun _ => Prodᶫ Typeᶫ (fun A => A))) :=
  fun e A => pointwise_alg A.(alg) (Err _ e).
