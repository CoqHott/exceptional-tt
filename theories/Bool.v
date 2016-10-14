Require Import Exception.

Definition boolᵉ : TYPE := mkTYPE bool.

Definition trueᵉ : El boolᵉ := mkPack _ true true.
Definition falseᵉ : El boolᵉ := mkPack _ true false.

Ltac val := refine (mkPack _ true _).

Definition bool_caseᵉ : El (Πᵉ (P : El Typeᵉ) (p0 : El P) (p1 : El P) (b : El boolᵉ), P).
Proof.
val; intros P.
val; intros p0.
val; intros p1.
val; intros b.
destruct b as [[|] b].
+ destruct b as [|]; [exact p0|exact p1].
+ apply empty.
Defined.

Check eq_refl : (fun P p0 p1 => Appᵉ (Appᵉ (Appᵉ (Appᵉ bool_caseᵉ P) p0) p1) trueᵉ) = fun P p0 p1 => p0.
Check eq_refl : (fun P p0 p1 => Appᵉ (Appᵉ (Appᵉ (Appᵉ bool_caseᵉ P) p0) p1) falseᵉ) = fun P p0 p1 => p1.

Definition bool_rectᵉ : El (Πᵉ (P : El (Πᵉ (b : El boolᵉ), Typeᵉ))
  (p0 : El (Appᵉ P trueᵉ)) (p1 : El (Appᵉ P falseᵉ)) (b : El boolᵉ), Appᵉ P b).
Proof.
val; intros P.
val; intros p0.
val; intros p1.
val; intros b.
destruct b as [[|] b].
+ destruct b as [|]; [exact p0|exact p1].
+ apply empty.
Defined.

Check eq_refl : (fun P p0 p1 => Appᵉ (Appᵉ (Appᵉ (Appᵉ bool_rectᵉ P) p0) p1) trueᵉ) = fun P p0 p1 => p0.
Check eq_refl : (fun P p0 p1 => Appᵉ (Appᵉ (Appᵉ (Appᵉ bool_rectᵉ P) p0) p1) falseᵉ) = fun P p0 p1 => p1.
