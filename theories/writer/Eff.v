Require Import Effects.

Set Universe Polymorphism.
Set Primitive Projections.

Module Type S.
Axiom Ω@{i} : Type@{i}.
End S.

Module Make(Import M : S).

Inductive list A :=
| nil : list A
| cons : A -> list A -> list A.

Fixpoint app {A} (l1 l2 : list A) : list A :=
match l1 with
| nil _ => l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Definition prod A B := sig A (fun _ => B).
Definition pair {A B} (x : A) (y : B) : prod A B := exist _ _ x y.

Definition M A := prod A (list Ω).

Definition ret {A} (x : A) : M A := pair x (nil Ω).

Definition pointwise {A} (f : A -> Type) (T : M A) : Type := f T.(wit).

Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  let r := f x.(wit) in
  pair r.(wit) (app x.(prf) r.(prf)).



Definition TYPE := sig Type (fun A => M A -> A).

Definition El (A : M TYPE) : TYPE := wit A.

(* Definition mkTYPE (A : Type) (alg : M A -> A) : M TYPE := pair (exist _ _ A alg) (nil Ω). *)

(* Definition El (A : M TYPE) : Type := pointwise wit A. *)

Definition hbind {A B} (x : M A) (f : A -> (El B).(wit)) : (El B).(wit) :=
match x.(prf) with
| nil _ => f x.(wit)
| _ => B.(wit).(prf) (pair (f x.(wit)) x.(prf))
end.

(** More derived stuff *)

Definition Free (A : Type) : M TYPE :=
  ret (exist Type (fun A => M A -> A) (M A) (fun x => bind x (fun x => x))).

Definition Typeᵉ : M TYPE := Free TYPE.

(* Check Typeᵉ : (El Typeᵉ).(wit). *)

Definition pbind {A} {B : A -> (El Typeᵉ).(wit)} (x : M A) (f : forall x : A, (El (B x)).(wit)) : (El (hbind x B)).(wit) :=
match x.(prf) as p return (El (hbind (pair x.(wit) p) B)).(wit) with
| nil _ => f x.(wit)
| _ => (B _).(wit).(prf) (pair (f x.(wit)) x.(prf))
end.

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


