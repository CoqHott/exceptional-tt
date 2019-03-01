Inductive nat@{i} : Type@{i} :=
  O : nat | S : nat -> nat.

Notation "0" := O.

Inductive le : nat -> nat -> Prop :=
    le_0 : forall n, le 0 n
  | le_S : forall n m : nat, le n m -> le (S n) (S m).

Infix "<=" := le.

Definition lt n m := S n <= m.

Infix "<" := lt.

Definition gt (n m:nat) := m < n.

Infix ">" := gt.

Definition le_S_n : forall n m : nat, S n <= S m -> n <= m.
Proof.
  intros n m e. inversion e. assumption.
Defined. 