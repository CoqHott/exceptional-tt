Set Universe Polymorphism.
Set Primitive Projections.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Inductive sum A B :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {_ _} _.
Arguments inr {_ _} _.

Axiom E : Type.

Definition T A := sum A E.
Definition ret {A} (x : A) : T A := inl x.
Definition bnd {A B} (x : T A) (f : A -> T B) : T B :=
match x with
| inl x => f x
| inr e => inr e
end.

Definition TYPE := sig Type (fun A => T A -> A).
Definition mkTYPE (A : Type) (μ : T A -> A) : TYPE := exist _ _ A μ.
Definition mkFree (A : Type) : TYPE := mkTYPE (T A) (fun x => bnd x (fun x => x)).

Axiom Ω : E -> TYPE.

Definition El (A : T TYPE) : TYPE := match A with
| inl X => X
| inr e => Ω e
end.

Notation "[| A |]" := (El A).(wit).

Definition hbnd {A : Type} {B : T TYPE} (x : T A) (f : A -> [|B|]) : [|B|] :=
match x with
| inl x => f x
| inr e => (El B).(prf) (inr e)
end.

Definition Typeᶫ : T TYPE := ret (mkFree TYPE).

Check Typeᶫ : [| Typeᶫ |].

(*
Definition pbnd₀ (A : Type) (B : A -> T TYPE) (x : T A) (f : forall x, (El (B x)).(wit)) :
  (El (hbnd A Typeᶫ x B)).(wit) :=
match x return (El (hbnd A Typeᶫ x B)).(wit) with
| inl x => f x
| inr e => (Ω e).(prf) (inr e)
end.
*)

Definition Prodᶫ (A : T TYPE) (B : [|A|] -> T TYPE) : T TYPE :=
  ret (mkTYPE (forall x : [|A|], [|B x|]) (fun f x => hbnd f (fun f => f x))).

Notation "A →ᶫ B" := (Prodᶫ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶫ'  x .. y , P" := (Prodᶫ _ (fun x => .. (Prodᶫ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶫ {A B} (f : forall x : [|A|], [|B x|]) : [|Prodᶫ A B|] := f.
Definition Appᶫ {A B} (f : [|Prodᶫ A B|]) (x : [|A|]) : [|B x|] := f x.

Definition pbnd (A : Type) (R : T TYPE) (B : A -> [|R|] -> T TYPE) (x : T A)
  (r : [|R|]) (f : forall x, [|B x r|]) :
  [| @hbnd A (R →ᶫ Typeᶫ) x B r |] :=
match x return [| @hbnd A (R →ᶫ Typeᶫ) x B r |] with
| inl x => f x
| inr e => (Ω e).(prf) (inr e)
end.

Definition boolᶫ : [|Typeᶫ|] := ret (mkFree bool).
Definition trueᶫ : [|boolᶫ|] := ret true.
Definition falseᶫ : [|boolᶫ|] := ret false.

Definition bool_caseᶫ : [| Πᶫ (P : [|Typeᶫ|]) (Pt Pf : [|P|]), boolᶫ →ᶫ P |] :=
  fun P Pt Pf b => hbnd b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition θ_bool : [| boolᶫ →ᶫ (boolᶫ →ᶫ Typeᶫ) →ᶫ Typeᶫ |] :=
  fun b k =>
    bool_caseᶫ ((boolᶫ →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k trueᶫ) (fun k => k falseᶫ) b k.

Definition bool_recᶫ : [|
  Πᶫ (P : [|boolᶫ →ᶫ Typeᶫ|]) (Pt : [|P trueᶫ|]) (Pf : [|P falseᶫ|])
  (b : [|boolᶫ|]), θ_bool b P
|] := fun P Pt Pf b =>
  pbnd bool (boolᶫ →ᶫ Typeᶫ) (fun b P => θ_bool (ret b) P) b P
    (fun b => bool_rect (fun b => [| θ_bool (ret b) P |]) Pt Pf b).

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition Eᶫ : [| Typeᶫ |] :=
  ret (mkTYPE E (fun e => match e with inl e => e | inr e => e end)).

Definition fail : [| Πᶫ (e : [| Eᶫ |]) (A : [| Typeᶫ |]), A |] :=
  fun e A => (El A).(prf) (inr e).
