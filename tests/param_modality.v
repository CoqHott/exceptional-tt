
Require Import Weakly.Effects.

Effect List Translate nat eq True False eq_ind False_ind le lt.
Weakly List Translate nat eq True False eq_ind False_ind le lt.

Effect Definition raise: forall A, A using unit.
Proof. exact (fun A => Err A tt). Defined.

Definition pred (n: nat) : nat :=
  match n with
  | 0 => raise nat
  | S n => n
  end.

Effect Translate pred using unit.

Definition param_nat: nat -> Prop := fun _ => True.
Effect Translate param_nat.
(* Proof. intros E n. exact (TypeVal E (Trueᵒ E) (Trueᴱ E)). Defined. *)
Weakly Definition param_nat.
Proof. intros E n Hn. exact (natᵂ E n). Defined.

Definition param_fun_nat: nat -> (nat -> nat) -> Prop := fun _ _ => True.
Effect Translate param_fun_nat.
(* Proof. intros E n. exact (TypeVal E (Trueᵒ E) (Trueᴱ E)). Defined. *)
Weakly Definition param_fun_nat.
Proof. intros E n f Hn. exact (natᵂ E (f n)). Defined.

Effect Definition O_f: 0 = raise nat -> False using unit.
Proof. simpl. intros H. inversion H. exact (Falseᴱ unit H0). Defined.
Weakly Definition O_f using unit.
Proof. simpl. intros H Hᵂ. inversion Hᵂ. Defined.

Effect Definition S_f: forall n, S n = raise nat -> False using unit.
Proof. simpl. intros n H. inversion H. exact (Falseᴱ unit H0). Defined.
Weakly Definition S_f using unit.
Proof. simpl. intros n H Hᵂ. inversion Hᵂ. Defined.

Theorem what: forall n f, param_fun_nat n f -> f n = raise nat -> False.
Proof. 
  intros n f _ H. destruct (f n).
  - exact (O_f H).
  - exact (S_f n0 H).
Defined.
Effect Translate what using unit.
Weakly Definition what using unit.
Proof.
  simpl.
  intros n f H Hᵂ Heq Heqᵂ. inversion Hᵂ.
  - inversion Heqᵂ. rewrite H2 in H1. inversion H1.
  - inversion Heqᵂ. rewrite H2 in H1. inversion H1.
Defined.

Theorem valid_pred: forall n, param_nat n ->  0 < n -> (pred n = raise nat -> False).
Proof.
  intros n Hp Hltn Heq.
  destruct n.
  - inversion Hltn.
  - simpl in Heq. destruct n; [exact (O_f Heq) | exact (S_f n Heq)].
Defined.

Effect Translate valid_pred using unit.
Fail Weakly Translate valid_pred using unit.
Weakly Definition valid_pred using unit.
Proof.
  intros E n Hparam Hparamᵂ Hlt Hltᵂ Heq Heqᵂ.
  destruct n.
  - unfold ltᵉ in Hlt. simpl in Hlt. unfold ltᵂ in Hltᵂ. inversion Hltᵂ.
  - admit.
  - inversion Hparamᵂ.
  Admitted.

(** See parametric modality **)