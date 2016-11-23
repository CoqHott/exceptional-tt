Set Universe Polymorphism.
Set Primitive Projections.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Inductive unit := tt.

(** Horrendous encoding of the delay monad because pattern-matching break
    the positivity condition. *)

Inductive option A :=
| None : option A
| Some : A -> option A.

Arguments None {_}.
Arguments Some {_} _.

CoInductive conat := build { hd : option conat }.

Definition coO := {| hd := None |}.

Inductive hoption {A} (N : Type) (S : A -> Type) : option A -> Type :=
| hNone : N -> hoption N S None
| hSome : forall x, S x -> hoption N S (Some x).

Arguments hNone {_ _ _} _.
Arguments hSome {_ _ _} _ _.

CoInductive Φ@{i} (A : Type@{i}) (i : option conat) : Type@{i} :=
  node { step : hoption@{i i i} A (fun n => Φ A n.(hd)) i }.

Arguments node {_ _} _.
Arguments step {_ _}.

Inductive poption {A N S} (fN : N -> Type) (fS : forall x, S x -> Type) : forall (o : option A), hoption N S o -> Type :=
| pNone : forall x, fN x -> poption fN fS None (hNone x)
| pSome : forall x s, fS x s -> poption fN fS (Some x) (hSome x s).

CoInductive hΦ {A : Type} (f : A -> Type) {i : option conat} (φ : hoption A (fun n => Φ A n.(hd)) i) : Type :=
  hnode { hstep : poption f (fun i ψ => hΦ _ f _ ψ.(step)) _ φ }.

CoFixpoint map {A B} (f : A -> B) (i : option conat) (φ : Φ A i) : Φ B i :=
match φ.(step) in hoption _ _ i return Φ B i with
| hNone x => node (hNone (f x))
| hSome _ n => node (hSome _ (map f _ n))
end.

(** At last reasonable stuff *)

Definition M@{i} (A : Type@{i}) : Type@{i} :=
  sig conat@{i} (fun n => Φ A n.(hd)).

Definition ret {A : Type} (x : A) : M A :=
  exist _ _ coO (@node _ _ (hNone x)).

Definition pointwise {A} (f : A -> Type) (s : M A) : Type.
Proof.
refine (match s.(wit).(hd) as n return Φ A n -> Type
with
| None => fun φ => _
| Some x => fun φ => _
end s.(prf)).
+ refine (
    match φ.(step) in hoption _ _ o return
      match o with
      | None => _
      | Some _ => unit
      end
    with
    | hNone x => f x
    | hSome _ n => tt
    end
  ).
+ refine (hΦ f φ.(step)).
Defined.

Definition TYPE := M (sig Type (fun A => M A -> A)).
Definition El (A : TYPE) := pointwise wit A.

CoFixpoint _bind {A B i} 
CoFixpoint bind {A B} (s : M A) (f : A -> M B) : M B.
{| step :=
    match s.(step) with
    | inl x => (f x).(step)
    | inr s => inr (bind s f)
    end
|}.

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