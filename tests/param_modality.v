
Require Import Weakly.Effects.

Effect Translate nat.  Effect Translate list.


Effect List Translate nat bool. Parametricity List Translate nat bool.

Inductive h : Type :=
kk: forall (f: Type -> Type), f h -> h.


Inductive t (A:Type): Type :=
| dd: (fun _ => t A) nat
| gg: nat -> (nat -> (bool -> (bool -> nat -> t A))) -> t A
| ff: t A -> t A. 

Effect Translate t. Parametricity Translate t. Print t\u1d3f.


Effect Translate True. Print True\u1d52.

Definition g := True. 
Effect Translate g. Print g\u1d49.

Effect Translate nat. Print nat\u1d52.
Effect Translate eq. Print eq\u1d52.

Theorem test: forall (n: nat), Prop. Proof. intros; exact (n = n). Defined.
Effect Translate test. Print test\u1d49. 


Inductive eq_e (E: Type) (A: @El E (@Type\u1d49 E)) (a: @El E A): @El E A -> Prop :=
eq_refl_e : eq_e E A a a.

Check fun (E: Type) (A: @El E (@Type\u1d49 E)) (a b: @El E A) => eq_e E A a b.

Inductive list_E (E: Type) (A: @El E Type\u1d49): Type :=
| nil_E: list_E E A
| cons_E: forall (a: El A), list_E E A -> list_E E A.

Inductive list_param (E: Type) (A: @El E Type\u1d49): list_E E A -> Prop :=
| nil_param : list_param E A (nil_E E A)
| cons_param : forall (a: El A) (l: list_E E A), list_param E A l -> list_param E A (cons_E E A a l).

Definition gg := forall (A: Type), Prop.
Effect Translate gg. Print gg\u1d49.

Inductive p : nat -> Type := d: p 0 | l: p 1 -> p 2.

Inductive k (E: Type): Type -> nat -> Type := kk: k E bool 0. Check kk unit.

Inductive even: nat -> Type :=
| evenZ: even 0
| evenS: forall n, odd n -> even (S n)
with
odd: nat -> Type :=
| oddS: forall n, even n -> odd (S n).

Effect List Translate nat bool unit list p k eq True False eq_ind False_ind le lt even.
Parametricity List Translate nat bool unit p k eq True. Print eq\u1d3f. Print k\u1d3f.

(* \u1d52 \u1d49 \u1d31 \u1d3f *)
Check @eq_refl.

Print eq\u1d52. Print eq\u1d3f.

Inductive param_eq' (E: Type) (A: @El E Type\u1d49) (x: @El E A): 
                   forall (H:@El E A), eq\u1d52 E A x H -> Type :=
param_eq_refl': param_eq' _ _ _ _ (eq_refl\u1d49 E A x). Print param_eq'.

Inductive dd: nat -> Set := ddd: dd 1.


Weakly List Translate nat. Print param_nat.
Weakly List Translate eq. Print param_eq.

Check param (@eq).

Definition param_eq'': forall (A: Type) (x y: A), x = y -> Prop. 
Proof. intros. exact True. Defined.
Effect Translate param_eq''. Print param_eq''\u1d49.
Parametricity Translate param_eq''. Print param_eq''\u1d3f.

Definition hh: forall (x: nat), param x -> x = x := fun _ _ => eq_refl.
Definition gg: forall (x: dd 0), param x -> x = x := fun _ _ => eq_refl.
Print gg. (* forall x : dd 4, @param (dd 4) x -> x = x *)
Effect List Translate dd hh gg. Print gg\u1d49.
Parametricity List Translate dd hh gg. Print gg\u1d3f. Check param\u1d49.
Weakly Translate dd. Print param_ind_nat.
Weakly Translate hh. Print hh\u1d42.

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
Defined. Print test\u1d42.

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
(* Proof. intros E n. exact (TypeVal E (True\u1d52 E) (True\u1d31 E)). Defined. *)
Weakly Definition param_nat.
Proof. intros E n Hn. exact (nat\u1d42 E n). Defined.
*)
Definition param_fun_nat: (nat -> nat) -> Prop := fun f => forall n, param_nat (f n).
Effect Translate param_fun_nat.
(* Proof. intros E n. exact (TypeVal E (True\u1d52 E) (True\u1d31 E)). Defined. *)
Weakly Translate param_fun_nat. Print param_fun_nat\u1d42.

Effect Definition O_f: 0 = raise nat -> False using unit.
Proof. simpl. intros H. inversion H. exact (False\u1d31 unit H0). Defined.
Weakly Definition O_f using unit.
Proof. simpl. intros H H\u1d42. inversion H\u1d42. Defined.

Effect Definition S_f: forall n, S n = raise nat -> False using unit.
Proof. simpl. intros n H. inversion H. exact (False\u1d31 unit H0). Defined.
Weakly Definition S_f using unit.
Proof. simpl. intros n H H\u1d42. inversion H\u1d42. Defined.

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
  intros n f H H\u1d42 Heq Heq\u1d42. unfold param_fun_nat\u1d42 in H\u1d42.
  assert (Q: param_nat\u1d42 unit (f n) (H n)) by (apply H\u1d42).
  inversion Q.
  - inversion Heq\u1d42. rewrite H2 in H1. inversion H1.
  - inversion Heq\u1d42. rewrite H2 in H1. inversion H1.
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
  intros E n Hparam Hparam\u1d42 Hlt Hlt\u1d42 Heq Heq\u1d42.
  destruct n.
  - unfold lt\u1d49 in Hlt. simpl in Hlt. unfold lt\u1d42 in Hlt\u1d42. inversion Hlt\u1d42.
  - admit.
  - inversion Hparam\u1d42.
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
  exact (nat\u1d42 E n).
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
  intros n f H H\u1d42 Heq Heq\u1d42. unfold param_fun_nat\u1d42 in H\u1d42.
  assert (Q: param_nat\u1d42 unit (f n) (H n)) by (apply H\u1d42).
  inversion Q.
  - inversion Heq\u1d42. rewrite H2 in H1. inversion H1.
  - inversion Heq\u1d42. rewrite H2 in H1. inversion H1.
Defined.
*)

End ClassParamMod.


(** See parametric modality **)