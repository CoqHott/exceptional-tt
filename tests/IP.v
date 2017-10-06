Require Import Effects.Effects.

Definition IP :=
  forall A B, ((A -> False) -> { n : nat & B n }) ->
  { n : nat & (A -> False) -> B n }.

Effect Translate nat.
Parametricity Translate nat.
Effect Translate False.
Parametricity Translate False.
Effect Translate sigT.
Parametricity Translate sigT.

Effect Translate IP.
Parametricity Translate IP.

Fixpoint nat_valid {E} (n : natᵒ E) := match n with
| Oᵉ _ => true
| Sᵉ _ n => nat_valid n
| natᴱ _ _ => false
end.

Effect Definition ip : IP using unit.
Proof.
intros E.
cbn in *.
refine (fun A B f => _).
pose (ans := f (fun _ => Falseᴱ _ tt)).
destruct ans as [n b| e].
+ refine (existTᵉ _ _ _ (if nat_valid n then n else Oᵉ _) _).
  refine (fun _ => _).
  destruct nat_valid; [exact b|].
  refine (@Err unit (B (Oᵉ _)) tt).
+ unshelve refine (existTᵉ _ _ _ _ _); cbn.
  - apply Oᵉ.
  - refine (fun f => Err _ tt).
Defined.

Scheme natᵒ_ind := Induction for natᵒ Sort Prop.
Scheme natᵒ_rect := Induction for natᵒ Sort Type.
Scheme natᴿ_ind := Induction for natᴿ Sort Prop.
Scheme natᴿ_rect := Induction for natᴿ Sort Type.

Lemma nat_valid_natᴿ : forall E n,
  nat_valid n = true -> @natᴿ E n.
Proof.
induction n; cbn in *; first [constructor|discriminate]; intuition.
Qed.

Lemma natᴿ_nat_valid : forall E n,
  @natᴿ E n -> nat_valid n = true.
Proof.
induction 1; cbn in *; intuition.
Qed.

Lemma natᴿ_hprop : forall E n (nε₀ nε₁ : @natᴿ E n), nε₀ = nε₁.
Proof.
induction nε₀; intros nε₁.
+ refine (
    match nε₁ in natᴿ _ n return
      match n return natᴿ _ n -> Prop with
      | Oᵉ _ => fun nε₁ => Oε _ = nε₁
      | Sᵉ _ _ => fun _ => True
      | natᴱ _ _ => fun _ => True
      end nε₁
    with
    | Oε _ => eq_refl
    | Sε _ _ nε => I
    end
  ).
+ refine (
    match nε₁ in natᴿ _ n return
      match n return
        natᴿ _ n -> Prop
      with
      | Oᵉ _ => fun _ => True
      | Sᵉ _ n' => fun nε₁ => forall nε₀, (forall nε₁ : natᴿ _ n', nε₀ = nε₁) -> Sε _ n' nε₀ = nε₁
      | natᴱ _ _ => fun _ => True
      end
        nε₁
    with
    | Oε _ => I
    | Sε _ _ nε => _
    end _ IHnε₀
  ).
  clear; intros nε₀ IH.
  f_equal.
  apply IH.
Qed.

Effect Translate projT1.
Effect Translate projT2.

Definition projT1ε {E A Aε B Bε} (p : @sigTᵒ E A B) (pε : @sigTᴿ E A Aε B Bε p) :
  Aε (projT1ᵉ E A B p) :=
  match pε in sigTᴿ _ _ _ _ _ p return Aε (projT1ᵉ E A B p)
  with
  | existTε _ _ _ _ _ _ xε _ _ => xε
  end.

Definition projT2ε {E A Aε B Bε} (p : @sigTᵒ E A B) (pε : @sigTᴿ E A Aε B Bε p) :
  Bε _ (@projT1ε E A Aε B Bε p pε) (projT2ᵉ E A B p) :=
  match pε in sigTᴿ _ _ _ _ _ p return Bε _ (@projT1ε E A Aε B Bε p pε) (projT2ᵉ E A B p)
  with
  | existTε _ _ _ _ _ _ _ _ yε => yε
  end.

Arguments sigTᴿ {E} {A} _ {B} _ _ : rename.

Parametricity Definition ip using unit.
Proof.
intros E A Aε B Bε p pε; cbn in *.
unfold ipᵉ.
specialize (pε (fun _ : El A => Falseᴱ unit tt)).
set (p₀ := p (fun _ : El A => Falseᴱ unit tt)) in *.
change (p (fun _ : El A => Falseᴱ unit tt)) with p₀.
clearbody p₀; clear p.
destruct p₀ as [n b|e]; cbn.
+ unshelve refine (existTε _ _ _ _ _ _ _ _ _).
  - refine (match nat_valid n as b return
      nat_valid n = b ->
      natᴿ _ (if b then n else Oᵉ unit)
    with
    | true => nat_valid_natᴿ _ _
    | false => fun _ => Oε _
    end eq_refl).
  - intros u uε.
    set (b0 := nat_valid n).
    refine (
      match b0 return
        forall e : b0 = nat_valid n,
        forall p : b0 = true -> natᴿ _ n,
        Bε (if b0 then n else Oᵉ unit)
          ((if b0 as b1 return (b0 = b1 -> natᴿ _ (if b1 then n else Oᵉ unit))
            then p
            else fun _ : b0 = false => Oε _) eq_refl)
          (if b0 return (El (B (if b0 then n else Oᵉ unit)))
           then b
           else Err (B (Oᵉ unit)) tt)
      with
      | true => _
      | false => _
      end eq_refl (nat_valid_natᴿ unit n)
    ).
    * intros _ p; assert (HnA : forall x : El A, Aε x -> Falseᴿ E (Falseᴱ unit tt)).
      { intros x xε; destruct (uε x xε). }
      specialize (pε HnA).
      pose (bε := projT2ε _ pε); cbn in *.
      match goal with [ |- Bε n ?p b ] => replace p with (projT1ε _ pε) by apply natᴿ_hprop end.
      apply bε.
    * intros Hn; exfalso.
      assert (HnA : forall x : El A, Aε x -> Falseᴿ E (Falseᴱ unit tt)).
      { intros x xε; destruct (uε x xε). }
      specialize (pε HnA).
      assert (Hn' := projT1ε _ pε); cbn in Hn'.
      apply natᴿ_nat_valid in Hn'; clear - Hn Hn'; congruence.
+ unshelve refine (existTε _ _ _ _ _ _ _ _ _).
  - constructor.
  - intros u uε; exfalso.
    assert (HnA : forall x : El A, Aε x -> Falseᴿ E (Falseᴱ unit tt)).
    { intros x xε; destruct (uε x xε). }
    specialize (pε HnA).
    inversion pε.
Qed.
