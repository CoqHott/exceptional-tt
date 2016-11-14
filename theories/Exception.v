Require Import Effects.

Set Universe Polymorphism.
Set Primitive Projections.

Axiom E : Type.

Inductive M (A : Type) :=
| Ok : A -> M A
| Err : E -> M A.

Definition ret {A} (x : A) := Ok _ x.

Definition map {A B} (f : A -> B) (l : M A) : M B :=
match l with
| Ok _ x => Ok _ (f x)
| Err _ e => Err _ e
end.

Definition pointwise {A} (f : A -> Type) (l : M A) : Type :=
match l with
| Ok _ x => f x
| Err _ _ => unit
end.

Fixpoint bind {A B} (l : M A) (f : A -> M B) : M B :=
match l with
| Ok _ x => f x
| Err _ e => Err _ e
end.

(** Those are derived constructions. TODO: implement me automagically *)

Definition TYPE := M (sig Type (fun A => M A -> A)).

Definition El (A : TYPE) : Type := pointwise wit A.

(** To be defined *)

Definition hzero {A} : E -> El A :=
match A return E -> El A with
| Ok _ (exist _ _ A alg) => fun e => alg (Err _ e)
| Err _ _ => fun _ => tt
end.

Definition hbind {A} {B : TYPE} (x : M A) (f : A -> El B) : El B :=
match x with
| Ok _ x => f x
| Err _ e => hzero e
end.

(** More derived stuff *)

Definition Typeᵉ : TYPE.
Proof.
refine (ret (exist _ _ TYPE _)).
refine (fun T => bind T (fun A => A)).
Defined.

(* Check Typeᵉ : El Typeᵉ. *)

Definition Prodᵉ (A : TYPE) (B : El A -> TYPE) : TYPE.
Proof.
refine (ret (exist _ _ (forall x : El A, El (B x)) _)).
refine (fun f x => hbind f (fun f => f x)).
Defined.

Notation "⌈ A ⌉" := (El A).

Notation "x →ᵉ y" := (Prodᵉ _ (fun (_ : x) => y))
  (at level 99, y at level 200, right associativity).

Notation "'Πᵉ'  x .. y , P" := (Prodᵉ _ (fun x => .. (Prodᵉ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).
