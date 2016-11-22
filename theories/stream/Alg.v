Set Universe Polymorphism.
Set Primitive Projections.

Inductive unit := tt.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Inductive sum A B :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

CoInductive M (A : Type) := node {
  step : sum A (M A);
}.

Arguments node {_} _.
Arguments step {_} _.

Definition ret {A} (x : A) : M A := node (inl x).

CoFixpoint map {A B} (f : A -> B) (s : M A) : M B :=
  {| step :=
    match s.(step) with
    | inl x => inl (f x)
    | inr s => inr (map f s)
    end
  |}.

(*
Inductive hsum {A B} (fA : A -> Type) (fB : B -> Type) : sum A B -> Type :=
| hinl : forall x, fA x -> hsum fA fB (inl x)
| hinr : forall y, fB y -> hsum fA fB (inr y).

CoInductive hM {A} (f : A -> Type) (s : M A) : Type := {
  hstep : hsum f (hM _ f) s.(step)
}.
*)

Definition pointwise {A} (f : A -> Type) (s : M A) : Type :=
match s.(step) with
| inl x => f x
| inr s => unit
end.

Definition hlist (T : M Type) := pointwise (fun A => A) T.
Definition is_alg (T : M Type) := pointwise (fun A => M A -> A) T.

Record TYPE := {
  wit : M Type;
  alg : is_alg wit;
}.

Definition El (A : TYPE) : Type := hlist A.(wit).

CoFixpoint bind {A B} (s : M A) (f : A -> M B) : M B :=
{| step :=
    match s.(step) with
    | inl x => (f x).(step)
    | inr s => inr (bind s f)
    end
|}.

Definition pointwise_alg {T} (f : is_alg T) (l : M (hlist T)) : hlist T :=
match T.(step) as T return is_alg (node T) -> M (hlist (node T)) -> hlist (node T) with
| inl A => fun f => f
| inr T => fun f _ => tt
end f l.

Definition Typeᶫ : TYPE.
Proof.
refine {|
  wit := ret TYPE;
  alg := fun T => {| wit := bind T wit; alg := _ |};
|}.
unfold is_alg, pointwise; cbn.
destruct (step T) as [A|]; [|exact tt].
destruct A as [wit alg]; cbn.
unfold is_alg, pointwise in *.
destruct (step wit) as [X|]; [|exact tt].
exact alg.
Defined.

Check Typeᶫ : El Typeᶫ.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := ret (forall x : El A, El (B x));
  alg := fun f x => pointwise_alg (B x).(alg) (map (fun f => f x) f)
|}.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition boolᶫ : TYPE := {| wit := ret (M bool); alg := fun b => bind b (fun b => b) |}.
Definition trueᶫ : El boolᶫ := ret true.
Definition falseᶫ : El boolᶫ := ret false.

Definition hbind {A B} (l : M A) (f : A -> El B) : El B :=
match l.(step) with
| inl x => f x
| inr s =>
  let later := cofix later (s : M A) : M (El B) := match s.(step) with
  | inl x => ret (f x)
  | inr s => {| step := inr (later s) |}
  end in
  pointwise_alg (B.(alg)) (later s)
end.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b).
Proof.
unfold bool_caseᶫ, hbind.
set (b0 := step b) in *; clearbody b0; clear b; rename b0 into b.
induction b as [[|]|b]; cbn in *.
+ exact Pt.
+ exact Pf.
+ unfold El; cbn.
  unfold hlist, pointwise, bind; cbn.
  set (b0 := step b) in *; clearbody b0; clear b; rename b0 into b.
  induction b as [[|]|b]; cbn in *; unfold El, hlist, pointwise in *.
  - exact Pt.
  - exact Pf.
  - exact tt.
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition Falseᶫ : TYPE := {|
  wit := ret (M False);
  alg := fun b => bind b (fun b => b);
|}.

Definition fixᶫ : El (Prodᶫ Typeᶫ (fun A => Prodᶫ (Prodᶫ A (fun _ => A)) (fun _ => A))).
Proof.
intros A f; cbn in *.
apply (pointwise_alg A.(alg)); cbn.
unfold El in f.
pose (bot := pointwise_alg A.(alg) (cofix bot := {| step := inr bot |})).
generalize bot; clear bot.
cofix F; intros x.
refine (F x).
Defined.

Definition fixᶫ : El (Prodᶫ Typeᶫ (fun A => Prodᶫ (Prodᶫ (laterᶫ A) (fun _ => A)) (fun _ => A))) :=
  fun A x => x tt.

Definition fail : El (Prodᶫ Eᶫ (fun _ => Prodᶫ Typeᶫ (fun A => A))) :=
  fun e A => pointwise_alg A.(alg) (Err _ e).

Goal El (Prodᶫ Typeᶫ (fun A => A)).
compute.