Require Import Effects.Effects.

Definition IP :=
  forall A B, ((A -> False) -> { n : nat & B n }) ->
  { n : nat & (A -> False) -> B n }.

Effect Translate nat.
Effect Translate False.
Effect Translate sigT.

Effect Translate IP.

Fixpoint nat_valid {E} (n : natᵒ E) := match n with
| Oᵉ _ => true
| Sᵉ _ n => nat_valid n
| natᴱ _ _ => false
end.

Definition ip : El (IPᵉ unit).
Proof.
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

Set Universe Polymorphism.

Definition Typeε {E} (A : type E) : Type := El A -> Type.

Definition Prodε {E}
  (A : Type) (Aε : A -> Type)
  (B : A -> type E) (Bε : forall x : A, Aε x -> El (B x) -> Type)
  (f : El (Prodᵉ E A B)) : Type :=
  forall (x : A) (xε : Aε x), Bε x xε (f x).

Arguments Prodε {E} {A} _ {B} _ _.

Definition Impε {E}
  (A : Type) (Aε : A -> Type)
  (B : type E) (Bε : El B -> Type)
  (f : A -> El B) : Type :=
  forall (x : A) (xε : Aε x), Bε (f x).

Inductive natε {E} : natᵒ E -> Type :=
| Oε : natε (Oᵉ E)
| Sε : forall n, natε n -> natε (Sᵉ E n).

Inductive Falseε {E} : Falseᵒ E -> Type :=.

Definition negε {E} (A : type E) (Aε : El A -> Type) f :=
  Impε (El A) Aε (TypeVal E (Falseᵒ E) (Falseᴱ E)) Falseε f.

Definition Falseᵉ {E} : El Typeᵉ := TypeVal E (Falseᵒ E) (Falseᴱ E).

Definition natᵉ {E} : El Typeᵉ := TypeVal E (natᵒ E) (natᴱ E).

Scheme natᵒ_ind := Induction for natᵒ Sort Prop.
Scheme natᵒ_rect := Induction for natᵒ Sort Type.

Definition sigTᵉ {E} (A : type E) (B : El (Prodᵉ E (El A) (fun _ => Typeᵉ))) : El Typeᵉ :=
  TypeVal E (sigTᵒ E A B) (sigTᴱ E A B).

Inductive sigTε {E}
  (A : type E) (Aε : El A -> Type)
  (B : El A -> type E) (Bε : forall x : El A, Aε x -> El (B x) -> Type)
  : sigTᵒ E A B -> Type :=
  existTε : forall
    (x : El A) (xε : Aε x)
    (y : El (B x)) (yε : Bε x xε y),
    sigTε A Aε B Bε (existTᵉ E A B x y).

Arguments sigTε {E} {A} _ {B} _ _.

Definition ip_param {E} (f : El (IPᵉ E)) : Type :=
  forall (A : type E) (Aε : El A -> Type),
  forall (B : natᵒ E -> type E) (Bε : forall n, natε n -> El (B n) -> Type),
  forall
    (p : (El A -> Falseᵒ E) -> sigTᵒ E _ _)
    (pε : Impε _ (negε A Aε) (sigTᵉ _ _) (@sigTε _ natᵉ natε _ Bε) p),
  @sigTε _ natᵉ natε
    (fun n => Prodᵉ E (El A -> Falseᵒ E) (fun _ => B n))
    (fun n nε => Impε _ (negε A Aε) _ (Bε n nε))
  (f A B p).

Lemma nat_valid_natε : forall E n,
  nat_valid n = true -> @natε E n.
Proof.
induction n; cbn in *; first [constructor|discriminate]; intuition.
Qed.

Lemma natε_nat_valid : forall E n,
  @natε E n -> nat_valid n = true.
Proof.
induction 1; cbn in *; intuition.
Qed.

Lemma natε_hprop : forall E n (nε₀ nε₁ : @natε E n), nε₀ = nε₁.
Proof.
induction nε₀; intros nε₁.
+ refine (
    match nε₁ in natε n return
      match n return natε n -> Prop with
      | Oᵉ _ => fun nε₁ => Oε = nε₁
      | Sᵉ _ _ => fun _ => True
      | natᴱ _ _ => fun _ => True
      end nε₁
    with
    | Oε => eq_refl
    | Sε _ nε => I
    end
  ).
+ refine (
    match nε₁ in natε n return
      match n return
        natε n -> Prop
      with
      | Oᵉ _ => fun _ => True
      | Sᵉ _ n' => fun nε₁ => forall nε₀, (forall nε₁ : natε n', nε₀ = nε₁) -> Sε n' nε₀ = nε₁
      | natᴱ _ _ => fun _ => True
      end
        nε₁
    with
    | Oε => I
    | Sε _ nε => _
    end _ IHnε₀
  ).
  clear; intros nε₀ IH.
  f_equal.
  apply IH.
Qed.

Effect Translate projT1.
Effect Translate projT2.

Definition projT1ε {E A Aε B Bε} (p : @sigTᵒ E A B) (pε : @sigTε E A Aε B Bε p) :
  Aε (projT1ᵉ E A B p) :=
  match pε in sigTε _ _ p return Aε (projT1ᵉ E A B p)
  with
  | existTε _ _ _ _ _ xε _ _ => xε
  end.

Definition projT2ε {E A Aε B Bε} (p : @sigTᵒ E A B) (pε : @sigTε E A Aε B Bε p) :
  Bε _ (@projT1ε E A Aε B Bε p pε) (projT2ᵉ E A B p) :=
  match pε in sigTε _ _ p return Bε _ (@projT1ε E A Aε B Bε p pε) (projT2ᵉ E A B p)
  with
  | existTε _ _ _ _ _ _ _ yε => yε
  end.

Lemma ipε : ip_param ip.
Proof.
intros A Aε B Bε p pε; cbn in *.
unfold ip.
specialize (pε (fun _ : El A => Falseᴱ unit tt)).
set (p₀ := p (fun _ : El A => Falseᴱ unit tt)) in *.
clearbody p₀; clear p.
destruct p₀ as [n b|e]; cbn.
+ unshelve refine (existTε _ _ _ _ _ _ _ _).
  - refine (match nat_valid n as b return
      nat_valid n = b ->
      natε (if b then n else Oᵉ unit)
    with
    | true => nat_valid_natε _ _
    | false => fun _ => Oε
    end eq_refl).
  - intros u uε.
    set (b0 := nat_valid n).
    refine (
      match b0 return
        forall e : b0 = nat_valid n,
        forall p : b0 = true -> natε n,
        Bε (if b0 then n else Oᵉ unit)
          ((if b0 as b1 return (b0 = b1 -> natε (if b1 then n else Oᵉ unit))
            then p
            else fun _ : b0 = false => Oε) eq_refl)
          (if b0 return (El (B (if b0 then n else Oᵉ unit)))
           then b
           else Err (B (Oᵉ unit)) tt)
      with
      | true => _
      | false => _
      end eq_refl (nat_valid_natε unit n)
    ).
    * intros _ p; assert (HnA : negε A Aε (fun _ : El A => Falseᴱ unit tt)).
      { intros x xε; destruct (uε x xε). }
      specialize (pε HnA).
      pose (bε := projT2ε _ pε); cbn in *.
      match goal with [ |- Bε n ?p b ] => replace p with (projT1ε _ pε) by apply natε_hprop end.
      apply bε.
    * intros Hn; exfalso.
      assert (HnA : negε A Aε (fun _ : El A => Falseᴱ unit tt)).
      { intros x xε; destruct (uε x xε). }
      specialize (pε HnA).
      assert (Hn' := projT1ε _ pε); cbn in Hn'.
      apply natε_nat_valid in Hn'; clear - Hn Hn'; congruence.
+ unshelve refine (existTε _ _ _ _ _ _ _ _).
  - constructor.
  - intros u uε; exfalso.
    assert (HnA : negε A Aε (fun _ : El A => Falseᴱ unit tt)).
    { intros x xε; destruct (uε x xε). }
    specialize (pε HnA).
    inversion pε.
Qed.
