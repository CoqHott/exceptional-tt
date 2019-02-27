Require Import Weakly.Effects.

Effect Definition e: Exception. Admitted. 

Inductive nat' (E: Type): Type :=
| O': nat' E
| S': nat' E -> nat' E
| nat_exc: E -> nat' E.

Inductive nat_param' (E: Type): nat' E -> Prop :=
| O'_param: nat_param' E (O' E)
| S'_param: forall n, nat_param' E n -> nat_param' E (S' E n). 


Effect List Translate nat bool list.
Effect List Translate False le lt gt eq not and or.

Definition g: forall e, nat := fun e => raise nat e.
Effect Translate g. Print gᵉ.

Scheme eqᵒ_rect := Induction for eqᵒ Sort Type.
Scheme eqᵒ_ind := Induction for eqᵒ Sort Prop.
Scheme listᵒ_rect := Induction for listᵒ Sort Type.
Scheme listᵒ_ind := Induction for listᵒ Sort Prop.

Scheme leᵒ_ind := Induction for leᵒ Sort Prop.

Fixpoint length {A: Type} (l: list A): nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Definition head {A: Type} (l: list A): A :=
  match l with
  | nil => raise A e
  | cons a _ => a
  end.

Definition tail {A: Type} (l: list A): list A := 
  match l with
  | nil => raise (list A) e
  | cons _ l' => l'
  end.

Effect List Translate length head tail.

(* Expected theorem *)
Effect Definition non_empty_list_distinct_error: forall (A: Type) (l: list A),
    length l > 0 -> tail l <> raise _ e.
Proof.
  simpl; intros E A l Hl Htail.
  induction l; simpl in *.
  - inversion Hl.
  - destruct l; try inversion Htail.
    + inversion Hl. inversion H1.
  - inversion Hl.
Defined.

(* Under this translation is not allowed *)
Definition non_valid_theorem: forall (A: Type) (l: list A),
    length l > 0 -> tail l = raise _ e := raise _ e.
Fail Effect Translate non_valid_theorem.

Effect Definition non_empty_list_distinct_error_param: forall (A: Type) (l: list A),
    length l > 0 -> param l -> tail l <> raise _ e.
Proof.
  simpl; intros E A l Hl Hparam Htail.
  induction Hparam.
  - inversion Hl.
  - destruct l; inversion Htail.
    +  inversion Hl. inversion H1. 
Defined.

(* Not true for head *)
Effect Definition non_empty_list_distinct_error_param: forall (A: Type) (l: list A),
    length l > 0 -> param l -> head l = raise _ e \/ head l <> raise _ e.
Proof.
  simpl; intros E A l Hl Hparam.
  destruct l eqn: Hlist.
  - inversion Hl.
  - simpl in *. subst.
Abort.

Effect Definition length_implies_param_list: forall (A: Type) (l: list A),
    length l > 0 -> param l.
Proof.
  intros E A l H.
  induction l. 
  - constructor. 
  - destruct l.
    + constructor. constructor.
    + simpl in *. constructor. apply IHl.
      inversion H.
      apply H1.
    + simpl in H. inversion H; subst. inversion H1.
  - inversion H.
Defined.

Effect Definition param_error_false: forall A, param (raise (list A) e) -> False.
Proof.
  simpl. intros E A Hp.
  inversion Hp.
Defined.

Effect Definition list_param_deep: forall {A: Type} {H: ParamMod A} (l: list A), Prop.
Proof.
  intros E A H l.
  destruct l.
  - exact (list_param E A (nilᵉ E A)).
  - exact (paramᵉ e0 /\ (list_param E A (consᵉ E A e0 l))).
  - exact (Falseᵒ E).
Defined. Print list_param_deepᵉ.

Effect Definition param_correctnes: forall (A: Type) (H: ParamMod A) e, param (raise A e) -> False.
Proof. Admitted.

Effect Definition head_empty_list_no_error: forall A {H: ParamMod A } (l: list A),
    length l > 0 -> list_param_deep A H l -> head l <> raise _ e.
Proof.
  intros E A A_param l Hlength list_deep_param Hhead.
  destruct l.
  - inversion Hlength.
  - inversion list_deep_param.
    inversion Hhead. simpl in *; subst. exact (param_correctnesᵉ E A A_param (eᵉ E) H).
  - inversion Hlength.
Defined.