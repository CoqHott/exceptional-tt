Require Import Effects.Effects.

Effect Translate unit.
Parametricity Translate unit.
Effect Translate False.
Parametricity Translate False.
Effect Translate eq.
Parametricity Translate eq.

Effect Definition not_id : unit -> unit using unit.
Proof.
intros E _; apply ttᵉ.
Defined.

Parametricity Definition not_id using unit.
Proof.
intros; constructor.
Defined.

Effect Definition ext_eq : forall u, not_id u = u using unit.
Proof.
intros E [|].
+ constructor.
+ refine (eqᴱ _ _ _ _ e).
Defined.

Parametricity Definition ext_eq using unit.
Proof.
intros E u uᴿ.
refine (match uᴿ with ttᴿ _ => _ end).
constructor.
Defined.

Effect Definition not_int_eq : not_id = (fun u => u) -> False using unit.
Proof.
intros E rw.
assert (H : E + (not_idᵉ = (fun u => u))).
refine (match rw with eq_reflᵉ _ _ _ => inr eq_refl | eqᴱ _ _ _ _ e => inl e end).
clear rw; destruct H as [e|H].
+ apply (Falseᴱ _ e).
+ absurd (unitᴱ E tt = ttᵉ E); [discriminate|].
  change (ttᵉ E) with (not_idᵉ (unitᴱ E tt)).
  rewrite H; reflexivity.
Defined.

Parametricity Definition not_int_eq using unit.
Proof.
intros E u uᴿ.
exfalso.
unfold not_idᵉ in *; cbn in *.
assert (Hrw : (fun _ : unitᵒ unit => ttᵉ unit) = (fun u : unitᵒ E => u)).
{ destruct uᴿ; reflexivity. }
+ absurd (unitᴱ E tt = ttᵉ E); [discriminate|].
  change (ttᵉ E) with ((fun _ : unitᵒ unit => ttᵉ unit) (unitᴱ E tt)).
  rewrite Hrw; reflexivity.
Defined.
