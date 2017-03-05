Require Import Effects.
Require Import list.Eff.

Set Universe Polymorphism.

Declare Effect list.Eff.

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using list.Eff.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using list.Eff.

Effect Definition amb : forall A, A -> A -> A using list.Eff.
Proof.
refine (fun A => @happ A).
Defined.

Definition quz := foo Type Type.

Effect Translate quz using list.Eff.

Effect Translate bool using list.Eff.
Effect Translate eq using list.Eff.
Effect Translate list using list.Eff.
Effect Translate sum using list.Eff.
Effect Translate False using list.Eff.
Effect Translate sigT using list.Eff.
Effect Translate Datatypes.prod using list.Eff.

Lemma eq_is_eqᵒ : forall A x y, eqᵒ A x y -> x = y.
Proof.
intros A x y e.
destruct e; reflexivity.
Qed.

Effect Definition non_standard_bool : {b : bool & Datatypes.prod (b = true -> False) (b = false -> False) } using list.Eff.
Proof.
refine (ret _).
exists (list.Eff.cons _ trueᵒ (list.Eff.nil _ falseᵒ)).
refine (ret _); constructor; intros e; destruct e as [e|e _]; apply eq_is_eqᵒ in e; discriminate.
Defined.

Inductive btree_ := bleaf_ : btree_ | bnode_ : (M boolᵒ -> M btree_) -> btree_.

Effect Definition btree : Type using list.Eff.
Proof.
refine (Free btree_).
Defined.

Effect Definition bleaf : btree using list.Eff.
Proof.
refine (ret bleaf_).
Defined.

Effect Definition bnode : (bool -> btree) -> btree using list.Eff.
Proof.
refine (fun f => ret (bnode_ f)).
Defined.

Effect Definition btree_case : forall P, P -> ((bool -> btree) -> (bool -> P) -> P) -> btree -> P using list.Eff.
Proof.
intros P pleaf pnode t.
refine (hbind t (fix btree_case t := match t with bleaf_ => pleaf | bnode_ f => pnode f (fun b => hbind (f b) btree_case) end)).
Defined.

Definition θ_btree : btree -> (btree -> Type) -> Type :=
  btree_case ((btree -> Type) -> Type) (fun k => k bleaf) (fun f _ k => k (bnode f)).

Effect Translate θ_btree using list.Eff.

Effect Definition btree_rect : forall (P : btree -> Type),
  (θ_btree bleaf P) ->
    (forall (f : bool -> btree), (forall b, θ_btree (f b) P) -> θ_btree (bnode f) P) ->
    forall t, θ_btree t P using list.Eff.
Proof.
intros P pleaf pnode t.
refine (pbind t P _).
refine (fix btree_rect t := _).
refine (
  match t with
  | bleaf_ => _
  | bnode_ f => _
  end
).
+ refine pleaf.
+ refine (pnode _ (fun b => _)).
  refine (pbind (f b) P _).
  refine (btree_rect).
Defined.
