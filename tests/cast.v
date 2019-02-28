Require Import Weakly.Effects.

Effect Definition e: Exception. Admitted.

Inductive sum (A B : Prop) : Type :=  inl : A -> sum A B | inr : B -> sum A B.

Notation "A + B" := (sum A B) : type_scope.
Arguments inl {_ _} _.
Arguments inr {_ _} _.

Effect List Translate sum sum_rect sum_rec. 
Effect List Translate True True_ind True_rect False False_ind False_rect not.
Effect List Translate eq eq_ind eq_rect eq_rec.
Effect List Translate nat nat_rect nat_rec. 
Effect List Translate list list_rect.
Effect List Translate length eq_sym eq_trans f_equal.
Effect List Translate sig sig_rect sig_rec proj1_sig.
Effect List Translate prod prod_rect.

(* basic inversion lemmas for nat *)

Effect Definition S_not0 : forall n, 0 <> S n.
Proof.
  compute; intros. inversion H.
Defined.

Effect Definition inj_S : forall n m, S n = S m -> n = m. 
intros E n m e. inversion e; econstructor.
Defined.

(* Decidable type class *)

Class Decidable (A : Prop) : Type := dec : A + (not A).
Effect Translate Decidable.
Effect Translate dec.
  
Arguments dec A {_}.

Class EqDecidable (A : Type) := { eq_dec : forall a b : A, Decidable (a = b) }.
Effect Translate EqDecidable.

Instance Decidable_eq_nat : forall (x y : nat), Decidable (x = y).
induction x.
- induction y.
  + left. apply eq_refl.
  + right. apply S_not0. 
- induction y.
  + right. intro H. symmetry in H. destruct (S_not0 _ H).
  + induction (IHx y). left. f_equal; auto. 
    right. intro e. apply inj_S in e. apply (b e).
Defined.
Effect List Translate Decidable_eq_nat.

Instance EqDecidable_nat : EqDecidable nat := { eq_dec := Decidable_eq_nat }.
Effect List Translate EqDecidable_nat.

Instance FalseDecidable : Decidable False.
Proof. right; intros a; assumption. Defined.
Effect Translate FalseDecidable.
  
Notation " ( x ; p ) " := (exist _ x p).

Definition cast (A:Type) (P : A -> Prop)
           (a:A) {Hdec : Decidable (P a)} : {a : A | P a}.
  induction (dec (P a)) using sum_rect. 
  - exact (a ; a0).
  - exact (raise _ e).
Defined. 
Effect Translate cast.

Definition forbidden_cast: False := proj2_sig (cast nat (fun _ => False) 0).
Fail Effect Translate proj2_sig. 
(* Due to elimination from Prop to Type *)
(* ==> Fail Effect Translate forbidden_cast. *)

Definition list2_to_pair {A} : {l : list A | length l = 2} -> A * A.
Proof.
  induction 1. induction x.
  - induction (S_not0 _ p) using False_rect.
  - induction x.
    + apply inj_S in p. induction (S_not0 _ p) using False_rect.
    + exact (a , a0).
Defined.
Effect Translate list2_to_pair.

Definition list_to_pair {A} : list A -> A * A.
Proof.
  exact (fun l => list2_to_pair (cast (list A) (fun l => length l = 2) l)).  
Defined.
Effect Translate list_to_pair.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (compat "8.4") : list_scope.

Definition list_to_pair_prop A (x : A) e : list_to_pair [x ; raise _ e] = (x, raise _ e).
Proof.
  reflexivity.
Defined.

Effect Translate list_to_pair_prop.

(* sanity check *)

Definition list_to_pair_prop_soundness E A x y :
  list_to_pair_propᵉ E A x y = eq_reflᵉ  _ _ _ := eq_refl. 

(* those two examples should be forbidden, because of non cummulativity *)

Effect Definition list_to_pair_prop_fake : forall A (x y : A) e,
    list_to_pair (raise _ e) = (x,y) -> False.
Proof.
  intros E A x y e H.
  inversion H.
Defined.  

Effect Definition list_to_pair_prop_fake2 : forall A (x y : A),
    list_to_pair [x;y;y] = (x,y) -> False.
Proof.
  intros E A x y H.
  inversion H.
Defined.
