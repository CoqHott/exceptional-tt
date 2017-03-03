Set Universe Polymorphism.
Set Primitive Projections.

Axiom S : Type.

Inductive State (A : Type) : Type :=
| get : (S -> A) -> State A
| set : S -> A -> State A.

Arguments get {_} _.
Arguments set {_} _.

Inductive T (A : Type) :=
| ret : A -> T A
| op : State (T A) -> T A.

Arguments ret {_} _.
Arguments op {_} _.

Fixpoint bnd {A B} (m : T A) (f : A -> T B) {struct m} : T B :=
match m with
| ret x => f x
| op (get k) => op (get (fun s => bnd (k s) f))
| op (set s x) => op (set s (bnd x f))
end.

Record sig A (P : A -> Type) := exist { wit : A; prf : P wit }.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Definition TYPE := sig Type (fun A => T A -> A).
Definition mkTYPE (A : Type) (μ : T A -> A) : TYPE := exist _ _ A μ.
Definition Free (A : Type) : T TYPE :=
  ret (exist Type (fun A => T A -> A) (T A) (fun x => bnd x (fun x => x))).


Fixpoint El (A : T TYPE) : TYPE.
Proof.
destruct A as [X₀|[Xget|s Xset]].
+ exact X₀.
+ unshelve refine (exist _ _ (forall s, (El (Xget s)).(wit)) _).
  unshelve refine (fun X s => (El (Xget s)).(prf) (bnd X (fun f => ret (f s)))).
+ refine (El Xset).
Defined.

Definition hbnd {A} {B : T TYPE} (x : T A) (f : A -> (El B).(wit)) : (El B).(wit).
Proof.
refine ((fix hbnd (x : T A) := _) x).
destruct x as [x₀|[xget|s xset]].
+ apply (f x₀).
+ refine ((El B).(prf) (op (get (fun s => ret _)))).
  refine (hbnd (xget s)).
+ refine ((El B).(prf) (op (set s (ret _)))).
  refine (hbnd xset).
Defined.

(** More derived stuff *)

Definition Typeᵉ : T TYPE := Free TYPE.

Notation "[| A |]" := (El A).(wit).

Check Typeᵉ : [| Typeᵉ |].

Definition Prodᵉ (A : T TYPE) (B : [|A|] -> T TYPE) : T TYPE :=
  ret (mkTYPE (forall x : [|A|], [|B x|]) (fun f x => hbnd f (fun f => f x))).

Notation "A →ᵉ B" := (Prodᵉ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᵉ'  x .. y , P" := (Prodᵉ _ (fun x => .. (Prodᵉ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᵉ {A B} (f : forall x : [|A|], [|B x|]) : [|Prodᵉ A B|] := f.
Definition Appᵉ {A B} (f : [|Prodᵉ A B|]) (x : [|A|]) : [|B x|] := f x.

Definition pbnd (A : Type) (R : T TYPE) (B : A -> [|R|] -> T TYPE) (x : T A)
  (r : [|R|]) (f : forall x, [|B x r|]) :
  [| @hbnd A (R →ᵉ Typeᵉ) x B r |].
Proof.
refine ((fix pbnd (x : T A) := _) x).
destruct x as [x₀|[xget|s xset]]; cbn.
+ refine (f x₀).
+ refine (fun s => pbnd _).
+ refine (pbnd _).
Defined.

Definition boolᵉ : [|Typeᵉ|] := Free bool.
Definition trueᵉ : [|boolᵉ|] := ret true.
Definition falseᵉ : [|boolᵉ|] := ret false.

Definition bool_caseᵉ : [| Πᵉ (P : [|Typeᵉ|]) (Pt Pf : [|P|]), boolᵉ →ᵉ P |] :=
  fun P Pt Pf b => hbnd b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᵉ P Pt Pf trueᵉ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᵉ P Pt Pf falseᵉ) = (fun P Pt Pf => Pf)).

Definition θ_bool : [| boolᵉ →ᵉ (boolᵉ →ᵉ Typeᵉ) →ᵉ Typeᵉ |] :=
  fun b k =>
    bool_caseᵉ ((boolᵉ →ᵉ Typeᵉ) →ᵉ Typeᵉ) (fun k => k trueᵉ) (fun k => k falseᵉ) b k.

Definition bool_recᵉ : [|
  Πᵉ (P : [|boolᵉ →ᵉ Typeᵉ|]) (Pt : [|P trueᵉ|]) (Pf : [|P falseᵉ|])
  (b : [|boolᵉ|]), θ_bool b P
|] := fun P Pt Pf b =>
  pbnd bool (boolᵉ →ᵉ Typeᵉ) (fun b P => θ_bool (ret b) P) b P
    (fun b => bool_rect (fun b => [| θ_bool (ret b) P |]) Pt Pf b).

Check (eq_refl : (fun P Pt Pf => bool_recᵉ P Pt Pf trueᵉ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᵉ P Pt Pf falseᵉ) = (fun P Pt Pf => Pf)).

Inductive treeᵒ (A : T TYPE) :=
| leafᵒ : treeᵒ A
| nodeᵒ : [|A|] -> T (treeᵒ A) -> T (treeᵒ A) -> treeᵒ A.

Definition treeᵉ : [|Typeᵉ →ᵉ Typeᵉ|] := fun A => Free (treeᵒ A).
Definition leafᵉ : [|Πᵉ A, treeᵉ A|] := fun A => ret (leafᵒ A).
Definition nodeᵉ : [|Πᵉ (A : [|Typeᵉ|]), A →ᵉ treeᵉ A →ᵉ treeᵉ A →ᵉ treeᵉ A|] :=
  fun A x l r => ret (nodeᵒ A x l r).

Definition tree_caseᵉ : [| Πᵉ (A : [|Typeᵉ|]) (P : [|Typeᵉ|]), P →ᵉ (A →ᵉ treeᵉ A →ᵉ P →ᵉ treeᵉ A →ᵉ P →ᵉ P) →ᵉ treeᵉ A →ᵉ P |] :=
  fun A P Pl Pn t =>
    hbnd t (fix F t :=
      match t with
      | leafᵒ _ => Pl
      | nodeᵒ _ x l r => Pn x l (hbnd l F) r (hbnd r F)
      end).

Definition θ_tree : [| Πᵉ (A : [|Typeᵉ|]), treeᵉ A →ᵉ (treeᵉ A →ᵉ Typeᵉ) →ᵉ Typeᵉ |] :=
  fun A t k =>
    tree_caseᵉ A ((treeᵉ A →ᵉ Typeᵉ) →ᵉ Typeᵉ) (fun k => k (leafᵉ A)) (fun x _ kl _ kr k => kl (fun l => kr (fun r => k (nodeᵉ A x l r)))) t k.

Definition tree_rectᵉ : [| Πᵉ (A : [|Typeᵉ|]) (P : [|treeᵉ A →ᵉ Typeᵉ|]),
  P (leafᵉ A) →ᵉ
  (Πᵉ (x : [|A|])
      (l : [|treeᵉ A|]) (_ : [|θ_tree A l P|])
      (r : [|treeᵉ A|]) (_ : [|θ_tree A r P|]), θ_tree A (nodeᵉ A x l r) P) →ᵉ
  Πᵉ (t : [|treeᵉ A|]), θ_tree A t P
|].
Proof.
refine (
  fun A P Pl Pn t => @pbnd (treeᵒ A) (treeᵉ A →ᵉ Typeᵉ) _ t P _
).
refine (fix F t :=
      match t with
      | leafᵒ _ => _
      | nodeᵒ _ x l r => _
      end); cbn.
+ refine Pl.
+ refine (Pn x l (pbnd _ _ _ _ _ F) r (pbnd _ _ _ _ _ F)).
Defined.
