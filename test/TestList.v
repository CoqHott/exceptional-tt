Require Import Effects.
Require Import list.Eff.

Set Universe Polymorphism.

Declare Effect list.Eff.

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo using list.Eff.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar using list.Eff.

Effect Definition amb : forall A, A -> A -> A using list.Eff.
Proof.
refine (fun A => @happ A).
Defined.

Definition quz := foo Type Type.

Effect Translate quz using list.Eff.

Effect Translate bool using list.Eff.
Effect Translate eq using list.Eff.
Effect Translate list using list.Eff.
Effect Translate sum using list.Eff.
Effect Translate False using list.Eff.
Effect Translate sigT using list.Eff.
Effect Translate Datatypes.prod using list.Eff.

Lemma eq_is_eqᵒ : forall A x y, eqᵒ A x y -> x = y.
Proof.
intros A x y e.
destruct e; reflexivity.
Qed.

Effect Definition non_standard_bool : {b : bool & Datatypes.prod (b = true -> False) (b = false -> False) } using list.Eff.
Proof.
refine (ret _).
exists (list.Eff.cons _ trueᵒ (list.Eff.nil _ falseᵒ)).
refine (ret _); constructor; intros e; destruct e as [e|e _]; apply eq_is_eqᵒ in e; discriminate.
Defined.
