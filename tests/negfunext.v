Require Import Effects.Effects.

Effect Translate unit.
Parametricity Translate unit.
Effect Translate False.
Parametricity Translate False.
Effect Translate eq.
Parametricity Translate eq.
Effect Translate prod.
Parametricity Translate prod.
Effect Translate sigT.
Parametricity Translate sigT.

Definition id_top (_ : unit) := tt.
Definition id_bot (u : unit) := u.

Effect Translate id_top.
Effect Translate id_bot.
Parametricity Translate id_top.
Parametricity Translate id_bot.

Lemma ext_eq : forall u, id_top u = id_bot u.
Proof.
intros []; reflexivity.
Qed.

Effect Translate ext_eq.
Parametricity Translate ext_eq.

Effect Definition not_int_eq : id_top = id_bot -> False using unit.
Proof.
intros E rw.
assert (H : E + (id_topᵉ E = id_botᵉ E)).
refine (match rw with eq_reflᵉ _ _ _ => inr eq_refl | eqᴱ _ _ _ _ e => inl e end).
clear rw; destruct H as [e|H].
+ apply (Falseᴱ _ e).
+ absurd (unitᴱ E tt = ttᵉ E); [discriminate|].
  change (ttᵉ E) with (id_topᵉ _ (unitᴱ E tt)).
  rewrite H; reflexivity.
Defined.

Parametricity Definition not_int_eq using unit.
Proof.
intros E u uᴿ.
exfalso.
unfold id_topᵉ in *; cbn in *.
assert (Hrw : id_topᵉ E = id_botᵉ E).
{ destruct uᴿ; reflexivity. }
+ absurd (unitᴱ E tt = ttᵉ E); [discriminate|].
  change (ttᵉ E) with (id_topᵉ E (unitᴱ E tt)).
  rewrite Hrw; reflexivity.
Defined.

Definition negfunext : {f : unit -> unit & {g : unit -> unit & prod (f = g -> False) (forall u, f u = g u) }} :=
  existT _ id_top (existT _ id_bot (pair not_int_eq ext_eq)).

Effect Translate negfunext using unit.
Parametricity Translate negfunext using unit.
