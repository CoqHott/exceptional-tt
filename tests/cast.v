Require Import Weakly.Effects.

Effect Translate False.

Effect Translate False_ind.
Effect Translate False_rect.

Effect Definition Exception : Type.
Proof.
  exact (fun E : Type => TypeVal E E (@id E)).
Defined. 

Effect Definition raise : forall A, Exception -> A.
Proof.
  exact (fun (E:Type) (A : type E) => Err A).
Defined. 

Arguments raise [A] _.

(* Define specific eliminations: parametric for Prop, default raise for Type *)

Inductive sum (A B : Prop) : Type :=  inl : A -> sum A B | inr : B -> sum A B.

Notation "A + B" := (sum A B) : type_scope.
Arguments inl {_ _} _.
Arguments inr {_ _} _.

Effect Translate sum.
Effect Translate sum_rect. 
Effect Translate sum_rec. 

(* basic inversion lemmas for nat *)

Effect Translate not.
Effect Translate nat.
Effect Translate eq.

Effect Translate eq_ind.
Effect Translate eq_rect.
Effect Translate eq_rec.


Effect Translate nat_rect.
Effect Translate nat_rec. 

Effect Definition S_not0 : forall n, 0 <> S n.
Proof.
  compute; intros. inversion H.
Defined.

Effect Definition inj_S : forall n m, S n = S m -> n = m. 
intros E n m e. inversion e; econstructor.
Defined.

(* boilerplate for eq, can be removed if pattern mathcing on eq is correctly translated*)

(* Decidable type class *)

Class Decidable (A : Prop) : Type := dec : A + (not A).
  
Arguments dec A {_}.

Class EqDecidable (A : Type) :=
  { eq_dec : forall a b : A, Decidable (a = b) }.

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

Instance EqDecidable_nat : EqDecidable nat := 
  { eq_dec := Decidable_eq_nat }.

Effect List Translate list prod Decidable dec length True
       eq_sym eq_trans f_equal Decidable_eq_nat.

Notation " ( x ; p ) " := (exist _ x p).

Effect List Translate sig sig_rect sig_rec list_rect.

Effect Definition cast_fail : Exception.
Admitted. 

Definition cast (A:Type) (P : A -> Prop)
           (a:A) {Hdec : Decidable (P a)} : {a : A | P a}.
  induction (dec (P a)) using sum_rect. 
  - exact (a ; a0).
  - exact (raise cast_fail).
Defined. 

Effect Translate cast.

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

Definition list_to_pair_prop A (x : A) e : list_to_pair [x ; raise e] = (x, raise e).
Proof.
  reflexivity.
Defined.

Effect Translate list_to_pair_prop.

(* sanity check *)

Definition list_to_pair_prop_soundness E A x y :
  list_to_pair_propᵉ E A x y = eq_reflᵉ  _ _ _ := eq_refl. 

(* this one should be forbidden, because of non cummulativity *)

Definition list_to_pair_prop_fake : forall A (x y : A) e,
    list_to_pair (raise e) = (x,y).

Fail Effect Translate list_to_pair_prop_fake.

Definition list_to_pair_prop_fake2 : forall A (x y : A),
    list_to_pair [x;y;y] = (x,y).

Fail Effect Translate list_to_pair_prop_fake2.


