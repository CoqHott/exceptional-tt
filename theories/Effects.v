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

Arguments Typeᵉ {_}.

Definition Prodᵉ@{i j k l} (E : Type@{i}) (A : type@{i j} E)
  (B : El A -> type@{i k} E) : type@{i l} E :=
  TypeVal E (forall x : El A, El (B x)) (fun e x => Err (B x) e).

(** Special handling of the Prop sort *)

Cumulative Inductive prop@{i} (E : Type@{i}) : Type :=
| pTypeVal : forall (A : Prop), (E -> A) -> prop E
| pTypeErr : E -> prop E.

Definition Propᵉ@{i k} (E : Type@{i}) := TypeVal@{i k} E (prop E) (pTypeErr E).

Definition pEl@{i} {E : Type@{i}} (A : prop E) : Prop:=
match A with
| pTypeVal _ A _ => A
| pTypeErr _ e => True
end.
