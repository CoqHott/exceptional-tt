Require Import Effects.
Require Import writer.Eff.

Set Universe Polymorphism.

Parameter Ω_:Type. 

Module S.
Definition Ω := Ω_.
End S.

Module Import Writer := Make(S).

Declare Effect Writer.

Effect Definition Ω : Type using Writer.
Proof.
  simpl. 
  refine (ret (exist _ _ (list S.Ω) _)).
  refine (fun w => app w.(wit) w.(prf)).
Defined.

(* Effect Translate unit using Writer. *)

Effect Definition unit : Type using Writer.
Proof. 
  refine (ret (exist _ _ (M unit) _)).
  refine (fun b => bind b (fun b => b)).
Defined.
  
Effect Definition tell : Ω -> unit using Writer. 
Proof.
  refine (fun w => pair tt w). 
Defined.

Effect Definition listen : unit -> Ω using Writer. 
Proof.
  refine (fun i => i.(prf)).
Defined. 

(* some definitions to play with the plugin *)

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using Writer.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using Writer.

Definition quz := foo Type Type.

Effect Translate quz using Writer.

Effect Translate bool using Writer.
Effect Translate eq using Writer.
(* Effect Translate list using Writer. *)
