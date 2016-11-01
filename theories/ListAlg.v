Set Universe Polymorphism.
Set Primitive Projections.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Inductive nlist (A : Type) :=
| nil : A -> nlist A
| cons : A -> nlist A -> nlist A.

Fixpoint hlist (T : nlist Type) := match T with
| nil _ A => A
| cons _ A T => prod A (hlist T)
end.

Fixpoint has_amb (T : nlist Type) := match T with
| nil _ A => A -> A -> A
| cons _ A T => prod (A -> A -> A) (has_amb T)
end.

Record TYPE := {
  wit : nlist Type;
  amb : has_amb wit;
}.

Definition El (A : TYPE) : Type := hlist A.(wit).

Fixpoint app {A} (l1 l2 : nlist A) :=
match l1 with
| nil _ x => cons _ x l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Fixpoint happ (T1 T2 : nlist Type) (amb1 : has_amb T1) (amb2 : has_amb T2) {struct T1} : has_amb (app T1 T2) :=
match T1 return forall T2, has_amb T1 -> has_amb T2 -> has_amb (app T1 T2) with
| nil _ A => fun T2 amb1 amb2 => pair amb1 amb2
| cons _ A T1 => fun T2 amb1 amb2 => pair amb1.(fst) (happ T1 T2 amb1.(snd) amb2)
end T2 amb1 amb2.

Fixpoint hamb (T : nlist Type) {struct T} : has_amb T -> hlist T -> hlist T -> hlist T :=
match T return has_amb T -> hlist T -> hlist T -> hlist T with
| nil _ A => fun f => f
| cons _ A T => fun f p q => pair (f.(fst) p.(fst) q.(fst)) (hamb T f.(snd) p.(snd) q.(snd))
end.

Fixpoint app2 {T1 T2 : nlist Type} (x : hlist T1) (y : hlist T2) {struct T1} : hlist (app T1 T2) :=
match T1 return forall T2, hlist T1 -> hlist T2 -> hlist (app T1 T2) with
| nil _ A => fun T2 x y => pair x y
| cons _ A T1 => fun T2 x y => pair x.(fst) (app2 x.(snd) y)
end T2 x y.

Definition Typeᶫ : TYPE := {|
  wit := nil _ TYPE;
  amb := fun T1 T2 =>
    {| wit := app T1.(wit) T2.(wit); amb := happ _ _ T1.(amb) T2.(amb) |}
|}.

Check Typeᶫ : El Typeᶫ.

Definition ambᶫ (A : TYPE) (x y : El A) : El A := hamb A.(wit) A.(amb) x y.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := nil _ (forall x : El A, El (B x));
  amb := fun f1 f2 x => ambᶫ (B x) (f1 x) (f2 x)
|}.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition boolᶫ : TYPE := {| wit := nil _ (nlist bool); amb := app |}.
Definition trueᶫ : El boolᶫ := nil _ true.
Definition falseᶫ : El boolᶫ := nil _ false.

Fixpoint bind {A B} (l : nlist A) (f : A -> El B) {struct l} :=
match l with
| nil _ x => f x
| cons _ x l => ambᶫ B (f x) (bind l f)
end.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  bind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b).
Proof.
induction b as [be|be b IHb]; cbn in *.
+ destruct be; [exact Pt|exact Pf].
+ refine (app2 _ IHb).
  destruct be; [exact Pt|exact Pf].
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).
