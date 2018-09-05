Require Import Weakly.Effects.

Arguments id {_}. (* Maximally implicit inserted id *)

Effect List Translate nat le lt gt False eq ex.
Weakly List Translate nat le lt gt False eq ex.
Parametricity List Translate nat le lt gt False eq ex.

Effect Definition Exception: Type.
Proof. exact (fun E: Type => TypeVal E E id). Defined.

Effect Definition raise: forall A: Type, A using unit.
Proof. intros E A; exact (Err A tt). Defined.

Theorem realExist: exists (n: nat), n = raise nat.
Proof. exists (raise nat). reflexivity. Defined.
Theorem fakeExist: exists (n: nat), n = raise nat.
Proof. exact (raise _). Defined.

Effect List Translate realExist fakeExist using unit.
Weakly Translate realExist using unit.
Fail Weakly Translate fakeExist using unit.

Set Printing Universes.
Inductive test@{i j k} (A: Type@{i}): Type@{j} -> Type@{k} := ctest: test A bool.

Monomorphic Universes k k'.
Monomorphic Constraint k < k'.

Lemma test_lemma  {A} (H: test@{k} A): test@{k'} A.
Proof. exact H. Defined. Print test_lemma.


Effect Definition O_fail: 0 = raise nat -> False using unit.
Proof. intros E H. inversion H. exact (Falseᴱ E X0). Qed.

Weakly Definition O_fail using unit.
Proof. intros E H H'. simpl in *. inversion H'. Qed.

Effect Definition S_fail: forall n, S n = raise nat -> False using unit.
Proof. intros E n H. inversion H. exact (Falseᴱ E X0). Qed.

Weakly Definition S_fail using unit.
Proof. intros E n H H'. inversion H'. Qed.

Definition nat_fail: forall (n: nat), n = raise nat -> False := fun n H =>
  match n as m return (m = raise nat -> False) with
  | O => fun H => O_fail H
  | S n => fun H => S_fail n H
  end H.
Effect Translate nat_fail using unit.
Weakly Definition nat_fail using unit.
Proof.
  intros E n H H'.
  destruct n; simpl in *.
  - exact (O_failᵂ H H').
  - exact (S_failᵂ n H H').
  - destruct H.
    + Show Proof.

Proof. 
  intros E n H H'. destruct H'.
  destruct n.
  - exact (O_failᵂ H H').
  - exact (S_failᵂ n H H').
  - simpl in *.
Defined.
Fail Weakly Translate nat_fail using unit.

Definition pred (n: nat): nat :=
  match n with 
  | 0 => raise nat
  | S n => n
  end.

Effect Translate pred using unit.

Theorem O_le_n: forall n, 0 <= n.
Proof. induction 0; auto. Qed.

Theorem le_drop_S_left: forall n m, S n <= m -> n <= m.
Proof. intros n m H. induction H; auto. Qed.

Theorem le_trans: forall n m k, n <= m -> m <= k -> n <= k.
Proof.
  intros n m k H1 H2. 
  induction H1.
  - assumption.
  - apply IHle. apply le_drop_S_left in H2. assumption.
Qed.

Theorem le_S_n: forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H; auto; subst.
  - apply le_drop_S_left in H1. assumption.
Qed.

Theorem not_S_le_n: forall n, S n <= n -> False.
Proof.
  intros n; induction n; intros H.
  - inversion H.
  - apply le_S_n in H. apply IHn. apply H.
Qed.

Effect Translate nat_ind.
Effect Translate eq_ind.
Effect Translate True.
Effect Translate False_ind.
Effect Translate f_equal.
Effect Translate eq_sym.
Effect Translate eq_ind_r.
Effect Translate le_ind.
Effect Translate le_drop_S_left.
Effect Translate le_S_n.
Effect Translate not_S_le_n.
Scheme natᵒ_rect := Induction for natᵒ Sort Type.

Theorem existR: exists (n: nat), raise nat = n.
Proof. exists (raise nat). reflexivity. Qed.
Effect Translate ex.
Weakly Translate ex.
Effect Translate existR using unit.
Weakly Translate existR using unit.

Theorem existR_fail: exists (n: nat), raise nat = n.
Proof. exact (raise _). Qed.
Effect Translate existR_fail using unit.
Weakly Definition raise using unit.
Proof. simpl. intros A A'.

Effect Definition nat_fail: forall (n: nat), n = raise nat -> False using unit.
Proof.
  simpl; intros n H.
  destruct n.
  - exact (O_failᵉ H).
  - exact (S_failᵉ n H).
  
Show Proof. Focus 2.
  induction n.
  - inversion H. exact (Falseᴱ _ H0).
  - inversion H. exact (Falseᴱ _ H0).
  - exact (Falseᴱ _ e).
Qed.
Weakly Definition nat_fail using unit.
Proof.
  simpl; intros n H.
  induction H. 

Theorem valid_prove: forall n, n > 0 -> pred n = raise nat -> False.
Proof.
  intros n; induction n; intros H Hpred; simpl in *.
  - inversion H.
  - inversion H.
    +  unfinversion H1.

Effect Definition valid_prove: forall n, n > 0 -> pred n = raise nat -> False using unit.
Proof.
  intros E n Hn Hpred. simpl in Hn.
  induction n; simpl in *.
  - inversion Hn. apply not_S_le_nᵉ in Hn. assumption.
  - inversion Hn; subst. 
    + destruct Hpred. inversion Hpred; subst.
apply IHn. inversion Hpred; subst.
    + Print leᵒ. apply (leᴱ E _ _). apply tt.
    + 