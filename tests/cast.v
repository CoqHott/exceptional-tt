Require Import Effects.Effects.

Inductive empty : Type := .

Definition not (T:Type) : Type := T -> empty.

Class Decidable (A : Type) := dec : A + (not A).

Arguments dec A {_}.

Effect Translate empty.
Effect Translate not.
Effect Translate sum.
Effect Translate Decidable.
Effect Translate dec.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Effect Translate sigT.
Effect Translate projT1.
Effect Translate projT2.
(* Effect Translate existT. *)

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
  

