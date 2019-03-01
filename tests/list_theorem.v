Require Import Weakly.Effects.

Require Import utils.

Open Scope list. 

(* Define the translation of inductive types and some definitions *)

Effect List Translate nat list False le lt gt eq not and or.

Scheme eqᵒ_rect := Induction for eqᵒ Sort Type.
Scheme eqᵒ_ind := Induction for eqᵒ Sort Prop.
Scheme listᵒ_rect := Induction for listᵒ Sort Type.
Scheme listᵒ_ind := Induction for listᵒ Sort Prop.
Scheme natᵒ_rect := Induction for natᵒ Sort Type.
Scheme natᵒ_ind := Induction for natᵒ Sort Prop.

Scheme leᵒ_ind := Induction for leᵒ Sort Prop.

Effect List Translate list_rect nat_rect.

(* Define catch eliminators and parametric elimnators *)

Effect Definition list_catch : forall A (P : list A -> Type),
       P nil -> (forall (a : A) (l : list A), P l -> P (a :: l)) -> (forall e, P (raise _ e)) -> forall l : list A, P l.
Proof.
  cbn; intros; induction l; auto.
Defined.

Effect Definition list_catch_prop : forall A (P : list A -> Prop),
       P nil -> (forall (a : A) (l : list A), P l -> P (a :: l)) -> (forall e, P (raise _ e)) -> forall l : list A, P l.
Proof.
  cbn; intros; induction l; auto.
Defined.

Effect Definition param_list_cons : forall A a (l:list A), param (cons a l) -> param l.
Proof.
  cbn. intros. inversion H. auto.
Defined.

Definition list_ind : forall A (P : list A -> Prop),
       P nil -> (forall (a : A) (l : list A), P l -> P (a :: l)) -> forall l : list A, param l -> P l.
Proof.
  intros A P Pnil Pcons l; induction l using list_catch_prop.
  - intro. exact Pnil.
  - intros param_al. exact (Pcons a l (IHl (param_list_cons _ _ _ param_al))). 
  - intros param_e. destruct (param_correct e param_e). 
Defined. 

Effect Definition nat_catch : forall (P : nat -> Type),
       P 0 -> (forall n, P n -> P (S n)) -> (forall e, P (raise _ e)) -> forall n, P n.
Proof.
  cbn; intros; induction n; auto.
Defined.

(* Define propositional laws on eliminators *)

Effect Definition list_catch_nil_eq : forall A (P : list A -> Type) Pnil Pcons Praise,
  list_catch A P Pnil Pcons Praise nil = Pnil. 
Proof.
  reflexivity.
Defined. 

Effect Definition list_catch_cons_eq : forall A (P : list A -> Type) Pnil Pcons Praise a l,
  list_catch A P Pnil Pcons Praise (cons a l) = Pcons a l (list_catch A P Pnil Pcons Praise l). 
Proof.
  reflexivity.
Defined. 

Effect Definition list_catch_raise_eq : forall A (P : list A -> Type) Pnil Pcons Praise e,
  list_catch A P Pnil Pcons Praise (raise _ e) = Praise e. 
Proof.
  reflexivity.
Defined. 

Effect Definition list_rect_raise_eq : forall A (P : list A -> Type) Pnil Pcons e,
  list_rect P Pnil Pcons (raise _ e) = raise _ e. 
Proof.
  reflexivity.
Defined.

Effect Definition nat_catch_0_eq : forall (P : nat -> Type) P0 PS Praise,
  nat_catch P P0 PS Praise 0 = P0. 
Proof.
  reflexivity.
Defined. 

Effect Definition nat_catch_S_eq : forall (P : nat -> Type) P0 PS Praise n,
  nat_catch P P0 PS Praise (S n) = PS n (nat_catch P P0 PS Praise n). 
Proof.
  reflexivity.
Defined. 

Effect Definition nat_catch_raise_eq : forall (P : nat -> Type) P0 PS Praise e,
  nat_catch P P0 PS Praise (raise _ e) = Praise e. 
Proof.
  reflexivity.
Defined. 


(* Now comes the real work in the coq/rett*)

Definition length {A} (l: list A) : nat := list_rect (fun _ => nat) 0 (fun _ _ n => S n) l.

(* Note that contrarily to the example in the paper, we define head and tail functions parametric in the error they raise *)

Definition head {A} (l: list A) e : A := list_rect (fun _ => A) (raise _ e) (fun a _ _ => a) l.

Definition tail {A} (l: list A) e : list A := list_rect (fun _ => list A) (raise _ e) (fun _ l _ => l) l.

Hint Unfold length.

Effect List Translate length tail head.

(* Expected theorem *)

Definition nil_not_raise: forall A e, @nil A <> raise _ e.
Proof.
  intros A e. 
  assert (forall l', @nil A = l' -> (list_catch _ (fun _ => Prop) True (fun _ _ _ => False) (fun  _ => False) l')).
  - intros l' eq. destruct eq. rewrite list_catch_nil_eq. exact I.
  - intro eq. specialize  (H (raise _ e) eq).
    rewrite list_catch_raise_eq in H. exact H. 
Defined. 

Effect List Translate eq_ind.

(* Effect Translate nil_not_raise. *)

Definition cons_not_raise: forall A (l: list A) a e,
    (cons a l) <> raise _ e.
Proof.
  intros A l a e. 
  assert (forall l', (cons a l) = l' -> (list_catch _ (fun _ => Prop) False (fun _ _ _ => True) (fun  _ => False) l')).
  - intros l' eq. destruct eq. rewrite list_catch_cons_eq. exact I.
  - intro eq. specialize  (H (raise _ e) eq). rewrite list_catch_raise_eq in H. exact H. 
Defined. 

(* Effect Translate cons_not_raise. *)

Definition raise_not_leq : forall (n:nat) e,
    n <= raise nat e -> False.
Proof.
  intros n e leq. 
  assert (forall n', n <= n' -> (nat_catch (fun _ => Prop) True (fun _ _ => True) (fun  _ => False) n')).
  - clear leq e. intros l' leq. destruct leq. destruct n. rewrite nat_catch_0_eq. exact I.
    rewrite nat_catch_S_eq. exact I. rewrite nat_catch_S_eq. exact I.
  - specialize  (H (raise _ e) leq).
    rewrite nat_catch_raise_eq in H. exact H. 
Defined. 

(* Effect Translate raise_not_leq. *)

Definition non_empty_list_distinct_error: forall A n e (l: list A),
    n <= length l -> l <> raise _ e.
Proof.
  intros A n e l. induction l using list_catch; cbn. 
  - intros. apply nil_not_raise.
  - intros. apply cons_not_raise.
  - intros H. unfold length in H. rewrite list_rect_raise_eq in H.
    compute in H. destruct (raise_not_leq  _ _ H).
Defined.


Definition non_empty_list_distinct_tail_error: forall A e (l: list A),
    length l > 0 -> tail l e <> raise _ e.
Proof.
  intros A e l; induction l using list_catch_prop; cbn. 
  - inversion 1.
  - intros Hlength eq. apply le_S_n in Hlength. eapply raise_not_leq. rewrite eq in Hlength.
    rewrite list_rect_raise_eq in Hlength. exact Hlength.
  - intros Hlength. unfold length in Hlength. rewrite list_rect_raise_eq in Hlength. 
    destruct (raise_not_leq _ _ Hlength). 
Defined. 

(* Check that proving with raise is not allowed *)
Definition non_valid_theorem: forall A e (l: list A),
    length l > 0 -> tail l e = raise _ e := fun A e => raise _ e.
Fail Effect Translate non_valid_theorem.

Definition list_param_deep: forall {A} {H: ParamMod A} (l: list A), Prop :=
  fun A H => list_catch A (fun _ : list A => Prop)
                        True
                        (fun (a : A) (_ : list A) (lind : Prop) => param a /\ lind)
                        (fun _ : Exception => False).

Definition head_empty_list_no_error: forall A {H: ParamMod A } e (l: list A),
    length l > 0 -> list_param_deep l -> head l e <> raise _ e.
Proof.
  intros A A_param e l. induction l using list_catch_prop. 
  - inversion 1.
  - intros Hlength Hl. unfold list_param_deep in Hl.
    rewrite list_catch_cons_eq in Hl. cbn in *.
    destruct Hl as [Ha _]. intro eq. rewrite eq in Ha. apply (param_correct e Ha).
  - intros. unfold length in H. rewrite list_rect_raise_eq in H. compute in H.
    destruct (raise_not_leq _ _ H). 
Defined. 