Set Universe Polymorphism.
Set Primitive Projections.

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

Inductive nlist (A : Type) :=
| nil : A -> nlist A
| cons : A -> nlist A -> nlist A.

Definition ret {A} (x : A) := nil A x.

Fixpoint map {A B} (f : A -> B) (l : nlist A) : nlist B :=
match l with
| nil _ x => nil _ (f x)
| cons _ x l => cons _ (f x) (map f l)
end.

Fixpoint pointwise {A} (f : A -> Type) (l : nlist A) : Type :=
match l with
| nil _ x => f x
| cons _ x l => prod (f x) (pointwise f l)
end.

Definition TYPE := nlist (sig Type (fun A => nlist A -> A)).

Definition El (A : TYPE) : Type := pointwise wit A.

Fixpoint app {A} (l1 l2 : nlist A) :=
match l1 with
| nil _ x => cons _ x l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Fixpoint bind {A B} (l : nlist A) (f : A -> nlist B) : nlist B :=
match l with
| nil _ x => f x
| cons _ x l => app (f x) (bind l f)
end.

Fixpoint happ {A} : El A -> El A -> El A :=
match A return El A -> El A -> El A with
| nil _ A => fun x y => A.(prf) (cons _ x (nil _ y))
| cons _ A T => fun x y =>
  pair (A.(prf) (cons _ x.(fst) (nil _ y.(fst))))  (happ x.(snd) x.(snd))
end.

Fixpoint hbind {A B} (l : nlist A) (f : A -> El B) {struct l} : El B :=
match l with
| nil _ x => f x
| cons _ x l => happ (f x) (hbind l f)
end.

Definition Typeᶫ : TYPE.
Proof.
refine (ret (exist _ _ TYPE _)).
refine (fun T => bind T (fun X => X)).
Defined.

Check Typeᶫ : El Typeᶫ.

Fixpoint pointwise_app {A} (f : A -> Type) (l1 l2 : nlist A)
  (p1 : pointwise f l1) (p2 : pointwise f l2) {struct l1} : pointwise f (app l1 l2) :=
match l1 return forall l2, pointwise f l1 -> _ -> pointwise f (app l1 l2) with
| nil _ x => fun l2 p1 p2 => pair p1 p2
| cons _ x l1 => fun l2 p1 p2 => pair p1.(fst) (pointwise_app f l1 l2 p1.(snd) p2)
end l2 p1 p2.

Fixpoint pbind {A} {B : A -> El Typeᶫ} (l : nlist A) (f : forall x : A, El (B x)) {struct l} :=
match l return El (hbind l B) with
| nil _ x => f x
| cons _ x l => @pointwise_app _ wit (B x) (hbind l B) (f x) (pbind l f)
end.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE.
Proof.
refine (nil _ (exist _ _ (forall x : El A, El (B x)) _)).
refine (fun f x => hbind f (fun f => f x)).
Defined.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition boolᶫ : TYPE.
Proof.
refine (nil _ (exist _ _ (nlist bool) _)).
refine (fun b => bind b (fun b => b)).
Defined.

Definition trueᶫ : El boolᶫ := nil _ true.
Definition falseᶫ : El boolᶫ := nil _ false.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b) :=
  pbind b (bool_rec _ Pt Pf).

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).
