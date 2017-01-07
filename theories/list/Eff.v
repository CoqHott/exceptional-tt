Require Import Effects.

Set Universe Polymorphism.
Set Primitive Projections.

Module Type S.
Axiom E@{i} : Type@{i}.
End S.

Inductive M (A : Type) :=
| nil : A -> M A
| cons : A -> M A -> M A.

Definition ret {A} (x : A) : M A := nil _ x.

Fixpoint map {A B} (f : A -> B) (l : M A) : M B :=
match l with
| nil _ x => nil _ (f x)
| cons _ x l => cons _ (f x) (map f l)
end.

Fixpoint app {A} (l1 l2 : M A) :=
match l1 with
| nil _ x => cons _ x l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Fixpoint bind {A B} (l : M A) (f : A -> M B) : M B :=
match l with
| nil _ x => f x
| cons _ x l => app (f x) (bind l f)
end.

(** Those are derived constructions. TODO: implement me automagically *)

Definition TYPE := sig Type (fun A => M A -> A).

Fixpoint El (A : M TYPE) : TYPE :=
match A with
| nil _ X => X
| cons _ X A =>
  exist Type (fun A => M A -> A)
    (prod X.(wit) (El A).(wit))
      (fun p => pair (X.(prf) (map fst p)) ((El A).(prf) (map snd p)))
end.

(** To be defined *)

Fixpoint happ {A} : (El A).(wit) -> (El A).(wit) -> (El A).(wit) :=
match A return (El A).(wit) -> (El A).(wit) -> (El A).(wit) with
| nil _ A => fun x y => A.(prf) (cons _ x (nil _ y))
| cons _ A T => fun x y =>
  pair (A.(prf) (cons _ x.(fst) (nil _ y.(fst))))  (happ x.(snd) x.(snd))
end.

Definition hbind {A B} (l : M A) (f : A -> (El B).(wit)) : (El B).(wit) :=
(fix F l := match l with
| nil _ x => f x
| cons _ x l => happ (f x) (F l)
end) l.

(** More derived stuff *)

Definition Typeᵉ : M TYPE.
Proof.
refine (ret (exist _ _ (M TYPE) _)).
refine (fun T => bind T (fun A => A)).
Defined.

(* Check Typeᵉ : El Typeᵉ. *)

Definition Prodᵉ (A : M TYPE) (B : (El A).(wit) -> M TYPE) : M TYPE.
Proof.
refine (ret (exist _ _ (forall x : (El A).(wit), (El (B x)).(wit)) _)).
refine (fun f x => hbind f (fun f => f x)).
Defined.

Notation "⌈ A ⌉" := (El A).

Notation "x →ᵉ y" := (Prodᵉ _ (fun (_ : x) => y))
  (at level 99, y at level 200, right associativity).

Notation "'Πᵉ'  x .. y , P" := (Prodᵉ _ (fun x => .. (Prodᵉ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Free (A : Type) : M TYPE :=
  ret (exist Type (fun A => M A -> A) (M A) (fun x => bind x (fun x => x))).
