Set Universe Polymorphism.
Set Primitive Projections.

Axiom R : Type.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Record TYPE_ := {
  wit : R -> Type;
  alg : forall r, (R -> wit r) -> wit r;
}.

Definition TYPE := R -> TYPE_.

Definition El (A : TYPE) : Type := forall r, (A r).(wit) r.

Definition Typeᶫ : TYPE.
Proof.
refine (fun _ => {|
  wit := fun _ => TYPE_;
  alg := fun r T => {| wit := (T r).(wit); alg := _ |};
|}).
intros r' m; apply (m r').
Defined.

Eval compute in El Typeᶫ.

Check Typeᶫ : El Typeᶫ.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE.
Proof.
refine (fun r => {|
  wit := fun _ => forall x : El A, El (B x);
  alg := fun r f => (f r)
|}).
Defined.

Eval lazy in fun A B => El (Prodᶫ A B).

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition boolᶫ : TYPE := {| wit := nil _ (nlist bool); alg := fun b => bind b (fun b => b) |}.
Definition trueᶫ : El boolᶫ := nil _ true.
Definition falseᶫ : El boolᶫ := nil _ false.

Fixpoint hbind {A B} (l : nlist A) (f : A -> El B) {struct l} : El B :=
match l with
| nil _ x => f x
| cons _ x l => pointwise_alg B.(alg) (cons _ (f x) (nil _ (hbind l f)))
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
+ refine (pointwise_app _ _ _ _ IHb).
  destruct be; [exact Pt|exact Pf].
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).
