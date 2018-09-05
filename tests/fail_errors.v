Require Import Weakly.Effects.

Module FailCoercible.
Effect Translate nat.
Weakly Translate nat.
Definition fail n := S n.
Effect Translate fail.
Weakly Definition fail.
Proof. exact (fun E n n' => (Sᵂ E n n')). Fail Defined. Abort.
End FailCoercible.