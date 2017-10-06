Require Import Effects.Effects.

Inductive empty : Type := .

Definition not (T:Type) : Type := T -> empty.

Class Decidable (A : Type) := dec : A + (not A).

Arguments dec A {_}.

Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y).
induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (f_equal S H).
    intro H; right. intro e. inversion e. apply (H H1).
Defined.

Class EqDecidable (A : Type) := { 
  eq_dec : forall a b : A, Decidable (a = b) 
                               }.

Instance EqDecidable_nat : EqDecidable nat := 
  { eq_dec := Decidable_eq_nat }.


Effect Translate empty.
Effect Translate not.
Effect Translate sum.
Effect Translate Decidable.
Effect Translate dec.

Effect Translate list.
Effect Translate prod.
Effect Translate eq.
Effect Translate eq_ind.
Effect Translate nat.
Effect Translate nat_rect.
Effect Translate Datatypes.length.
Effect Translate True.
Effect Translate False.
Effect Translate False_ind. 
Effect Translate False_rect. 
Effect Translate f_equal.
Effect Translate eq_sym.
Effect Translate eq_ind_r.
Effect Translate Decidable_eq_nat.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Effect Translate sigT.
Effect Translate projT1.
Effect Translate projT2.

Require Import String. 

Definition Exception : Type := string. 

Effect Translate bool.  
Effect Translate Ascii.ascii.  
Effect Translate string.  
Effect Translate Exception. 

Definition lift_bool : boolᵒ Exception -> bool + Exception.
  destruct 1. exact (inl true). exact (inl false).
  exact (inr e).
Defined.
                
Definition lift_ascii : asciiᵒ Exception -> Ascii.ascii + Exception.
  destruct 1.
  destruct (lift_bool b) as [b'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b0) as [b0'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b1) as [b1'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b2) as [b2'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b3) as [b3'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b4) as [b4'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b5) as [b5'| e]; [idtac | exact (inr e)].
  destruct (lift_bool b6) as [b6'| e]; [idtac | exact (inr e)].
  exact (inl (Ascii.Ascii b' b0' b1' b2' b3' b4' b5' b6')).
  exact (inr e).
Defined. 
  
Fixpoint lift_Exception (s:stringᵒ Exception) : Exception.
Proof.
  destruct s.
  - exact EmptyString.
  - apply lift_ascii in a. destruct a. 
    + apply String. exact a. apply (lift_Exception s).
    + exact e. 
  - exact e.
Defined. 

Effect Definition raise : forall A, Exception -> A using Exception. 
Proof.
  intros exception A e. cbn in *. 
  unshelve refine (@Effects.Err Exception A _).
  exact (lift_Exception e).
Defined. 

Arguments raise [A] _.

Local Open Scope string_scope.

Definition cast (A:Type) (P : A -> Type)
  (a:A) {Hdec : Decidable (P a)} : {a : A & P a} :=
  match dec (P a) with
  | inl p => (a ; p)
  | inr _ => raise "not castable"
  end.

Effect Translate cast using Exception.

Definition list_to_pair {A} : list A -> A * A.
Proof.
  intro l. pose (cast (list A) (fun l => List.length l = 2) l). 
  destruct s. destruct x.
  inversion e.
  destruct x. inversion e.
  exact (a,a0).
Defined.

Effect Translate list_to_pair using Exception.

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (compat "8.4") : list_scope.

Definition list_to_pair_prop A (x y : A) : list_to_pair [x ; y] = (x,y).
Proof.
  reflexivity.
Defined.

Effect Translate list_to_pair_prop using Exception.

Definition list_to_pair_prop_fake A (x y : A) : list_to_pair [x ; y] = (x,y) :=
  match raise "Fake Proof" : empty with end. 

Effect Translate list_to_pair_prop_fake using Exception.

Goal forall A x y , list_to_pair_prop_fakeᵉ A x y = list_to_pair_propᵉ A x y.
  intros A x y. 
  compute.
Abort.
