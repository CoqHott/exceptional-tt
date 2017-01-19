Require Import Effects.

Set Universe Polymorphism.
Set Primitive Projections.

CoInductive M (A : Type) :=
   ret : A -> M A
|  step : M A -> M A.

Arguments step {_} _.
Arguments ret {_} _.

CoFixpoint map {A B} (f : A -> B) (s : M A) : M B :=
    match s with
    | ret x => ret (f x)
    | step s => step (map f s)
    end.

CoFixpoint bind {A B} (s : M A) (f : A -> M B) : M B :=
  match s with
  | ret x => f x
  | step s => step (bind s f)
  end.

Definition TYPE := sig Type (fun A => M A -> A).

Definition El (A : M TYPE) : TYPE :=
match A with
| ret X => X
| step A => exist Type (fun A => M A -> A) unit (fun _ => tt)
end.

Definition hbind {A B} (l : M A) (f : A -> (El B).(wit)) : (El B).(wit) :=
  match l with
  | ret x => f x
  | step s =>
    let later := cofix later (s : M A) : M (El B).(wit) :=
                   match s with
                   | ret x => ret (f x)
                   | step s => step (later s)
                   end in
    (El B).(prf) (later s)
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






