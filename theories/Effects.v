
Declare ML Module "exception".

Set Universe Polymorphism.
Set Primitive Projections.

Inductive any@{i} : Type@{i} := Any.

Cumulative Inductive type@{i j} (E : Type@{i}) : Type :=
| TypeVal : forall (A : Type@{j}), (E -> A) -> type E
| TypeErr : E -> type E.

Definition El@{i j} {E : Type@{i}} (A : type@{i j} E) : Type@{j} :=
match A with
| TypeVal _ A _ => A
| TypeErr _ e => any@{j}
end.

Definition Err@{i j} {E : Type@{i}} (A : type@{i j} E) : E -> El@{i j} A :=
match A return E -> El A with
| TypeVal _ _ e => e
| TypeErr _ _ => fun _ => Any
end.

Definition Typeᵉ@{i j k} (E : Type@{i}) : type@{i k} E :=
  TypeVal E (type@{i j} E) (TypeErr E).

Definition Propᵉ@{i j} (E: Type@{i}): type@{i j} E :=
  TypeVal E Prop (fun _ => True).

Arguments Typeᵉ {_}.

Definition Prodᵉ@{i j k l} (E : Type@{i}) (A : Type@{j})
  (B : A -> type@{i k} E) : type@{i l} E :=
  TypeVal E (forall x : A, El (B x)) (fun e x => Err (B x) e).

(** Special handling of the Prop sort *)

Cumulative Inductive prop@{i} (E : Type@{i}) : Type :=
| pTypeVal : forall (A : Prop), (E -> A) -> prop E
| pTypeErr : E -> prop E.

(*
Definition Propᵉ@{i k} (E : Type@{i}) := TypeVal@{i k} E (prop E) (pTypeErr E).
*)

Definition pEl@{i} {E : Type@{i}} (A : prop E) : Prop:=
match A with
| pTypeVal _ A _ => A
| pTypeErr _ e => True
end.

Axiom Exception: Type.
Definition Exceptionᵉ (E: Type): type E := TypeVal E E (fun e => e).
Axiom raise: forall (A: Type), Exception -> A. 
Definition raiseᵉ (E: Type) (A: @El E (@Typeᵉ E)) (e: @El E (Exceptionᵉ E)) := Err A e.

Inductive Falseᵉ: Prop :=.

Set Primitive Projections.
Class Param (A: Type) := {
  param: A -> Prop;
}.

Class Paramᵉ (E: Type) (A: @El E (@Typeᵉ E)) := {
  paramᵉ: @El E A -> Prop;
  (* param_correctᵉ: forall e, paramᵉ (raiseᵉ E A e) -> Falseᵉ *)
}.
Unset Primitive Projections.

(** 
    Providing Exception and raise construction to work on the source theory. 
    This terms only reify the underlying exceptinal Type 
*)

(******************************)
(*** Test handling of sorts ***)
(******************************)

(*
Module Test.
Set Universe Polymorphism.
Inductive sort@{i j} (E : Type@{i}) : Prop :=
| sortType : forall (A : Type@{j}), (E -> A) -> sort E
| sortProp : forall (A : Prop), (E -> A) -> sort E
| sortErr : E -> sort E.
Print sort.
Definition type@{i j} (E: Type@{i}) : Type@{j}.
Proof. exact (sort@{i j} E). Defined.

Definition sTypeVal@{i j} (E: Type@{i}) (A: Type@{j}) (f: E -> A): type@{i j} E :=
  sortType E A f. Print sTypeVal.
Definition sTypeErr@{i j} (E: Type@{i}) (e: E): type@{i j} E :=
  sortErr E e.

Definition prop@{i} (E: Type@{i}) : Prop :=
  sort@{i Set} E.
Definition sPropVal@{i} (E: Type@{i}) (A: Prop) (f: E -> A): type@{i Set} E :=
  sortType E A f. Print sPropVal.
Definition sPropErr@{i j} (E: Type@{i}) (e: E): type@{i Set} E :=
  sortErr E e.

Definition sEl@{i j} {E : Type@{i}} (A : type@{i j} E) : Type@{j} :=
match A with
| sortType _ A _ => A
| sortProp _ _ _ => any@{j}
| sortErr _ _ => any@{j}
end.

Definition sErr@{i j} {E : Type@{i}} (A : sort@{i j} E) : E -> sEl@{i j} A :=
match A return E -> sEl A with
| sTypeVal _ _ e => e
| sPropVal _ _ _ => fun _ => Any
| sSortErr _ _ => fun _ => Any
end.

Definition sType@{i j k} {E : Type@{i}} : sort@{i k} E :=
  sTypeVal E (sort@{i j} E) (sSortErr E).

(** Prop related *)
Definition spEl@{i} {E : Type@{i}} (A: sort@{i Set} E) : Prop:=
match A with
| sTypeVal _ _ _ => True
| sPropVal _ A _ => A
| sSortErr _ _ => True
end.

Definition spErr@{i j} {E : Type@{i}} (A : sort@{i Set} E) : E -> spEl@{i} A :=
match A return E -> spEl A with
| sTypeVal _ _ e => fun _ => I
| sPropVal _ _ e => e
| sSortErr _ _ => fun _ => I
end.

Definition sProp@{i j} {E : Type@{i}} : sort@{i j} E :=
  sTypeVal E (sort@{i Set} E) (PropErr E). 

End Test.
*)

(***************************)
(** New handling of sorts **)
(***************************)

Module NewExc.
Set Universe Polymorphism.
Cumulative Inductive sort@{i j} (E : Type@{i}) : Type :=
| sortType : forall (A : Type@{j}), (E -> A) -> sort E
| sortProp : forall (A : Prop), (E -> A) -> sort E
| sortErr : E -> sort E.

Definition type@{i j} (E: Type@{i}) :=
  sort@{i j} E.
Definition sTypeVal@{i j} (E: Type@{i}) (A: Type@{j}) (f: E -> A): type@{i j} E :=
  sortType E A f.
Definition sTypeErr@{i j} (E: Type@{i}) (e: E): type@{i j} E :=
  sortErr@{i j} E e.

Definition prop@{i} (E: Type@{i}) :=
  sort@{i Set} E.
Definition sPropVal@{i} (E: Type@{i}) (A: Prop) (f: E -> A): prop@{i} E :=
  sortProp E A f.
Definition sPropErr@{i} (E: Type@{i}) (e: E): prop@{i} E :=
  sortErr E e.

(** Type related *)
Definition sEl@{i j} {E : Type@{i}} (A : type@{i j} E) : Type@{j} :=
match A with
| sortType _ A _ => A
| sortProp _ _ _ => any@{j}
| sortErr  _ _ => any@{j}
end.

Definition sErr@{i j} {E : Type@{i}} (A : type@{i j} E) : E -> sEl@{i j} A :=
match A return E -> sEl A with
| sortType _ _ e => e
| sortProp _ _ _ => fun _ => Any
| sortErr  _ _ => fun _ => Any
end.

Definition sType@{i j k} {E : Type@{i}} : type@{i k} E :=
  sTypeVal E (type@{i j} E) (sTypeErr E).

(** Prop related *)
Definition spEl@{i} {E : Type@{i}} (A: prop@{i} E) : Prop:=
match A with
| sortType _ _ _ => True
| sortProp _ A _ => A
| sortErr  _ _ => True
end.

Definition spErr@{i j} {E : Type@{i}} (A : sort@{i Set} E) : E -> spEl@{i} A :=
match A return E -> spEl A with
| sortType _ _ e => fun _ => I
| sortProp _ _ e => e
| sortErr  _ _ => fun _ => I
end.

Definition sProp@{i j} {E : Type@{i}} : type@{i j} E :=
  sTypeVal E (prop@{i} E) (sPropErr E).

End NewExc.
