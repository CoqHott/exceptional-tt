
Require Import Weakly.Effects.

Effect Translate True. Print Trueᵒ.

Definition g := True.
Effect Translate g. Translate gᵉ.

Effect Translate nat. Print natᵒ.
Effect Translate eq. Print eqᵒ.

Theorem test: forall (n: nat), Prop. Proof. intros; exact (n = n). Defined.
Effect Translate test. Print testᵉ.


Inductive eq_e (E: Type) (A: @El E (@Typeᵉ E)) (a: @El E A): @El E A -> Prop :=
eq_refl_e : eq_e E A a a.

Check fun (E: Type) (A: @El E (@Typeᵉ E)) (a b: @El E A) => eq_e E A a b.

Inductive list_E (E: Type) (A: @El E Typeᵉ): Type :=
| nil_E: list_E E A
| cons_E: forall (a: El A), list_E E A -> list_E E A.

Inductive list_param (E: Type) (A: @El E Typeᵉ): list_E E A -> Prop :=
| nil_param : list_param E A (nil_E E A)
| cons_param : forall (a: El A) (l: list_E E A), list_param E A l -> list_param E A (cons_E E A a l).

Definition gg := forall (A: Type), Prop.
Effect Translate gg. Print ggᵉ.

Inductive p : nat -> Type := d: p 0 | l: p 1 -> p 2.

Inductive k (E: Type): Type -> nat -> Type := kk: k E bool 0. Check kk unit.

Inductive even: nat -> Type :=
| evenZ: even 0
| evenS: forall n, odd n -> even (S n)
with
odd: nat -> Type :=
| oddS: forall n, even n -> odd (S n).

Effect List Translate nat bool unit list p k eq True False eq_ind False_ind le lt even.
Parametricity List Translate nat bool unit p k eq True. Print eqᴿ. Print kᴿ.

(* ᵒ ᵉ ᴱ ᴿ *)
Check @eq_refl.

Print eqᵒ. Print eqᴿ.

Inductive param_eq' (E: Type) (A: @El E Typeᵉ) (x: @El E A): 
                   forall (H:@El E A), eqᵒ E A x H -> Type :=
param_eq_refl': param_eq' _ _ _ _ (eq_reflᵉ E A x). Print param_eq'.

Inductive dd: nat -> Set := ddd: dd 1.


Weakly List Translate nat. Print param_nat.
Weakly List Translate eq. Print param_eq.

Check param (@eq).

Definition param_eq'': forall (A: Type) (x y: A), x = y -> Prop. 
Proof. intros. exact True. Defined.
Effect Translate param_eq''. Print param_eq''ᵉ.
Parametricity Translate param_eq''. Print param_eq''ᴿ.

Definition hh: forall (x: nat), param x -> x = x := fun _ _ => eq_refl.
Definition gg: forall (x: dd 0), param x -> x = x := fun _ _ => eq_refl.
Print gg. (* forall x : dd 4, @param (dd 4) x -> x = x *)
Effect List Translate dd hh gg. Print ggᵉ.
Parametricity List Translate dd hh gg. Print ggᴿ. Check paramᵉ.
Weakly Translate dd. Print param_ind_nat.
Weakly Translate hh. Print hhᵂ.

Weakly List Translate even.
Weakly List Translate unit.
Weakly List Translate list. 

Weakly List Translate p.

Weakly List Translate True.
Weakly List Translate False.
Weakly List Translate eq_ind.
Weakly List Translate False_ind.
Weakly List Translate le.
Weakly List Translate lt.

Effect Definition raise: forall A, A using unit.
Proof. exact (fun A => Err A tt). Defined.


Definition test: forall (n:nat), param n -> n = raise nat -> False := raise _.
Effect Translate test using unit.
Weakly Definition test using unit.
Proof.
  intros. 
  destruct n.
  - inversion X2.
  - inversion X2.
  - inversion X0.
Defined. Print testᵂ.

Effect Definition test: forall (n:nat), param n -> n = raise nat -> False using unit.
Proof. exact (raise _). Defined.
Weakly Translate test using unit.
Proof. 

Definition pred (n: nat) : nat :=
  match n with
  | 0 => raise nat
  | S n => n
  end.

Effect Translate pred using unit.

(*
Definition param_nat: nat -> Prop := fun _ => True.
Effect Translate param_nat.
(* Proof. intros E n. exact (TypeVal E (Trueᵒ E) (Trueᴱ E)). Defined. *)
Weakly Definition param_nat.
Proof. intros E n Hn. exact (natᵂ E n). Defined.
*)
Definition param_fun_nat: (nat -> nat) -> Prop := fun f => forall n, param_nat (f n).
Effect Translate param_fun_nat.
(* Proof. intros E n. exact (TypeVal E (Trueᵒ E) (Trueᴱ E)). Defined. *)
Weakly Translate param_fun_nat. Print param_fun_natᵂ.

Effect Definition O_f: 0 = raise nat -> False using unit.
Proof. simpl. intros H. inversion H. exact (Falseᴱ unit H0). Defined.
Weakly Definition O_f using unit.
Proof. simpl. intros H Hᵂ. inversion Hᵂ. Defined.

Effect Definition S_f: forall n, S n = raise nat -> False using unit.
Proof. simpl. intros n H. inversion H. exact (Falseᴱ unit H0). Defined.
Weakly Definition S_f using unit.
Proof. simpl. intros n H Hᵂ. inversion Hᵂ. Defined.

Theorem what: forall n f, param_fun_nat f -> f n = raise nat -> False.
Proof. 
  intros n f _ H. destruct (f n).
  - exact (O_f H).
  - exact (S_f n0 H).
Defined.
Effect Translate what using unit.
Weakly Definition what using unit.
Proof.
  simpl.
  intros n f H Hᵂ Heq Heqᵂ. unfold param_fun_natᵂ in Hᵂ.
  assert (Q: param_natᵂ unit (f n) (H n)) by (apply Hᵂ).
  inversion Q.
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



Module ClassParamMod.

Generalizable All Variables.

Class ParamMod (A: Type) := {
  param: A -> Prop
}.

Instance NatParamMod: ParamMod nat := {
  param := fun _ => True
}.
(*
Effect Translate NatParamMod.
Weakly Definition NatParamMod.
Proof.
  intros E.
  constructor.
  simpl.
  intros n _.
  exact (natᵂ E n).
Defined.  
*)
Instance ProductParamMod {A: Type} {B: A -> Type}
                        `{forall a, ParamMod (B a)}: ParamMod (forall (a: A), (B a)) := {
  param := fun f => forall (a: A), param (f a)
}.

Theorem what: forall (n: nat) (f: nat -> nat), param f -> f n = raise nat -> False.
Proof. 
  intros n f _ H. destruct (f n).
  - exact (O_f H).
  - exact (S_f n0 H).
Defined.
(*
Effect Translate what using unit.
Weakly Definition what using unit.
Proof.
  simpl.
  intros n f H Hᵂ Heq Heqᵂ. unfold param_fun_natᵂ in Hᵂ.
  assert (Q: param_natᵂ unit (f n) (H n)) by (apply Hᵂ).
  inversion Q.
  - inversion Heqᵂ. rewrite H2 in H1. inversion H1.
  - inversion Heqᵂ. rewrite H2 in H1. inversion H1.
Defined.
*)

End ClassParamMod.


(** See parametric modality **)