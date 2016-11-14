Require Import Exception.

Module TestSuite.

Definition foo := fun (A : Type) (x : A) => x.

Effect Translate foo.

Definition bar := fun (A B : Type) (f : A -> A -> B) (x : A) => f x x.

Effect Translate bar.

End TestSuite.

Ltac val := refine (mkPack _ true _).

Effect Definition abort : forall A, A.
Proof.
refine (mkPack _ false tt).
Defined.

Effect Definition pure : forall A, A -> Type.
Proof.
val; intros A.
val; intros a.
val; cbn.
destruct A as [[|] A]; cbn in *.
+ destruct a as [[|] a].
  - exact True.
  - exact False.
+ exact False.
Defined.

Effect Definition foo : (forall A B : Type, A -> B -> A).
Proof.
val; intros A.
val; intros B.
val; intros a.
val; intros b.
Abort.
