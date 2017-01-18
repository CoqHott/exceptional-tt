Require Import Effects.

Set Universe Polymorphism.
Set Primitive Projections.

Module Type S.
Axiom E@{i} : Type@{i}.
End S.

Module Make(Import M : S).

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

Definition TYPE := sig Type (fun A => M A -> A).

Definition El (A : M TYPE) : TYPE :=
match A with
| Ok _ X => X
| Err _ e => exist Type (fun A => M A -> A) unit (fun _ => tt)
end.

(** To be defined *)

Definition hbind {A} {B : M TYPE} (x : M A) (f : A -> (El B).(wit)) : (El B).(wit) :=
match x with
| Ok _ x => f x
| Err _ e => (El B).(prf) (Err _ e)
end.

(** More derived stuff *)

Definition Free (A : Type) : M TYPE :=
  ret (exist Type (fun A => M A -> A) (M A) (fun x => bind x (fun x => x))).

Definition Typeᵉ : M TYPE := Free TYPE.

(* Check Typeᵉ : (El Typeᵉ).(wit). *)

Definition Prodᵉ (A : M TYPE) (B : (El A).(wit) -> M TYPE) : M TYPE.
Proof.
refine (ret (exist _ _ (forall x : (El A).(wit), (El (B x)).(wit)) _)).
refine (fun f x => hbind f (fun f => f x)).
Defined.

Notation "⌈ A ⌉" := (El A).(wit).

Notation "x →ᵉ y" := (Prodᵉ _ (fun (_ : x) => y))
  (at level 99, y at level 200, right associativity).

Notation "'Πᵉ'  x .. y , P" := (Prodᵉ _ (fun x => .. (Prodᵉ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

End Make.
