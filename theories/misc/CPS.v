Set Universe Polymorphism.
Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.

Inductive Ω :=.
(* Axiom Ω : Type. *)

Inductive unit := tt.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Definition M A := (A -> Ω) -> Ω.
Definition ret {A} (x : A) : M A := fun k => k x.

(** The underlying type is the type of stacks *)
Inductive Typeᴿ : ((Type -> Ω) -> Ω) -> Type :=
| IsType : forall (A : Type), ((A -> Ω) -> Type) -> Typeᴿ (ret A)
.

Definition TYPE := sig (M Type) Typeᴿ.

Definition Typeᶠ : TYPE :=
  exist _ _ (ret (Type -> Ω)) (IsType _ Typeᴿ).

Definition C (A : TYPE) : Type :=
  match A.(prf) with IsType A Aᴿ => A end.

Definition Cᴿ (A : TYPE) : (C A -> Ω) -> Type :=
  match A.(prf) as T return
    (match T with IsType A _ => _ end -> _) -> Type
  with IsType A Aᴿ => Aᴿ end.

Definition El (A : TYPE) : Type := sig (C A -> Ω) (Cᴿ A).

Inductive Freeᴿ {A} : M A -> Type :=
| freeᴿ : forall x, Freeᴿ (ret x).

Definition Free (A : Type) : TYPE :=
  exist (M Type) Typeᴿ (ret (A -> Ω)) (IsType _ Freeᴿ).

Check Typeᶠ : El Typeᶠ.

Definition Prodᶠ (A : TYPE) (B : El A -> TYPE) : El Typeᶠ.
Proof.
unshelve refine (exist _ _ (ret _) _).
+ refine (sig (El A) (fun x => C (B x))).
+ refine (IsType _ (fun f => _)).
  refine (forall x : El A, Cᴿ (B x) (fun ω => f (exist _ _ x ω))).
Defined.

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A B} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (exist _ _ (fun ω => _) _).
+ unshelve refine ((f ω.(wit)).(wit) ω.(prf)).
+ unshelve refine (fun x => (f x).(prf)).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (exist _ _ (fun ω => f.(wit) (exist _ _ x ω)) _).
unshelve refine (f.(prf) _).
Defined.

Eval compute in eq_refl : (fun A B f x => Appᶠ (@Lamᶠ A B f) x) = (fun A B f x => f x).
Eval compute in eq_refl : (fun A B f => @Lamᶠ A B (fun x => Appᶠ f x)) = (fun A B f => f).

Notation "t · u" := (Appᶠ t u) (at level 11, left associativity).

Inductive Falseᴿ : M False -> Type :=.

Definition Falseᶠ : TYPE :=
  exist _ _ (ret (False -> Ω)) (IsType _ Falseᴿ).

Inductive boolᴿ : M bool -> Type :=
| trueᴿ : boolᴿ (ret true)
| falseᴿ : boolᴿ (ret false).

Definition boolᶠ : TYPE :=
  exist _ _ (ret (bool -> Ω)) (IsType _ boolᴿ).

Definition trueᶠ : El boolᶠ := exist _ _ _ trueᴿ.
Definition falseᶠ : El boolᶠ := exist _ _ _ falseᴿ.

Definition bool_rectᶠ : El
  (Πᶠ (P : El (boolᶠ →ᶠ Typeᶠ)), P · trueᶠ →ᶠ P · falseᶠ →ᶠ
  Πᶠ (b : El boolᶠ), P · b).
Proof.
refine (λᶠ P Pt Pf b, _).
refine (
match b.(prf) as br in boolᴿ b return El (Appᶠ P (exist _ _ _ br)) with
| trueᴿ => Pt
| falseᴿ => Pf
end
).
Defined.

Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · trueᶠ) = (fun P Pt Pf => Pt).
Eval compute in eq_refl :
  (fun P Pt Pf => bool_rectᶠ · P · Pt · Pf · falseᶠ) = (fun P Pt Pf => Pf).

Definition squash : El (Typeᶠ →ᶠ Typeᶠ).
Proof.
refine (λᶠ A, _).
unshelve refine (exist _ _ (ret (C A)) (IsType _ _)).
unshelve refine (fun _ => unit).
Defined.

Notation "[[ A ]]" := (squash · A).

Definition inhabits : El (Πᶠ (A : El Typeᶠ), A →ᶠ [[ A ]]).
Proof.
refine (λᶠ A x, _).
unshelve refine (exist _ _ x.(wit) tt).
Defined.

Lemma cc : El (Πᶠ (A B : El Typeᶠ), ((A →ᶠ [[ B ]]) →ᶠ [[ A ]]) →ᶠ [[ A ]]).
Proof.
refine (λᶠ A B f, _).
simple refine (exist _ _ (fun ω => _) _).
+ unshelve refine ((f).(wit) (exist _ _ _ _)); [|refine ω].
  unshelve refine (exist _ _ (fun k => (k.(wit).(wit) ω)) _).
  refine (fun _ => tt).
+ refine tt.
Defined.

Lemma squash_consistency : El ([[ Falseᶠ ]]) -> False.
Proof.
refine (fun e => match e.(wit) (False_rect _) with end).
Defined.

Definition squash_bool_caseᶠ :
  El (Πᶠ (P : El Typeᶠ) (Pt : El [[ P ]]) (Pf : El [[ P ]]) (b : El [[ boolᶠ ]]), [[ P ]]).
Proof.
unshelve refine (λᶠ P Pt Pf b, exist _ _ (fun ω => _) _).
+ refine (b.(wit) (fun b => match b with true => Pt.(wit) ω | false => Pf.(wit) ω end)).
+ exact tt.
Defined.

(* Not true : we would need extensional unit types *)
(* Check (eq_refl : (fun P Pt Pf => squash_bool_caseᶠ · P · Pt · Pf · (inhabits · boolᶠ · trueᶠ)) = (fun P Pt Pf => Pt)). *)
(* Check (eq_refl : (fun P Pt Pf => squash_bool_caseᶠ · P · Pt · Pf · (inhabits · boolᶠ · falseᶠ)) = (fun P Pt Pf => Pf)). *)

Lemma squash_bool_caseᶠ_true :
  forall P Pt Pf, squash_bool_caseᶠ · P · Pt · Pf · (inhabits · boolᶠ · trueᶠ) = Pt.
Proof.
intros P Pt Pf; compute.
destruct Pt as [? [ ] ]; reflexivity.
Defined.

Lemma squash_bool_caseᶠ_false :
  forall P Pt Pf, squash_bool_caseᶠ · P · Pt · Pf · (inhabits · boolᶠ · falseᶠ) = Pf.
Proof.
intros P Pt Pf; compute.
destruct Pf as [? [ ] ]; reflexivity.
Defined.

Lemma squash_bool_case_cc : forall P X (M : El ((boolᶠ →ᶠ [[ X ]]) →ᶠ [[ boolᶠ ]])) Pt Pf,
  squash_bool_caseᶠ · P · Pt · Pf · (cc · boolᶠ · X · M) =
  cc · [[ P ]] · X · (λᶠ (k : El ([[ P ]] →ᶠ [[ X ]])),
    squash_bool_caseᶠ · P · Pt · Pf ·
      (M · (λᶠ (x : El boolᶠ),
        k · (squash_bool_caseᶠ · P · Pt · Pf · (inhabits · boolᶠ · x))))).
Proof.
intros P X M Pt Pf.
reflexivity.
Qed.

Definition choice : El (
  Πᶠ (A : El Typeᶠ) (B : El (A →ᶠ Typeᶠ)),
    (Πᶠ x, [[ B · x ]]) →ᶠ
    [[ Πᶠ x, B · x ]]
).
Proof.
refine (λᶠ A B f, _).
refine (exist _ _ _ tt).
cbn; intros [x k].
refine (f.(wit) (exist _ _ x k)).
Defined.

Definition rchoice : El (
  Πᶠ (A : El Typeᶠ) (B : El (A →ᶠ Typeᶠ)),
    [[ Πᶠ x, B · x ]]  →ᶠ
    (Πᶠ x, [[ B · x ]])
).
Proof.
refine (λᶠ A B f x, _).
refine (exist _ _ _ tt).
cbn; intros k.
refine (f.(wit) (exist _ _ x k)).
Defined.

Lemma app_cc : forall (A B : El Typeᶠ) X (M : El (((A →ᶠ B) →ᶠ [[ X ]]) →ᶠ [[ A →ᶠ B ]])) (N : El A),
  rchoice · A · (λᶠ (_ : El A), B) · (cc · (A →ᶠ B) · X · M) · N =
    cc · B · X · (λᶠ (k : El (B →ᶠ [[ X ]])),
      rchoice · A · (λᶠ (_ : El A), B) · (M · (λᶠ (f : El (A →ᶠ B)), k · (f · N))) · N).
Proof.
reflexivity.
Qed.

Inductive psigma (A : Type) (B : A -> Type) :=
| pexist : forall x, B x -> psigma A B.

Inductive sigmaᴿ (A : El Typeᶠ) (B : El (A →ᶠ Typeᶠ)) :
  M (psigma (El A) (fun x => El (B · x))) -> Type :=
| existᴿ : forall x y, sigmaᴿ A B (ret (pexist _ _ x y)).

Definition sigmaᶠ : El (Πᶠ (A : El Typeᶠ) (B : El (A →ᶠ Typeᶠ)), Typeᶠ).
Proof.
refine (λᶠ A B, _).
unshelve refine (exist _ _ (ret (_ -> Ω)) (IsType _ _)).
+ refine (psigma (El A) (fun x => El (B · x))).
+ refine (sigmaᴿ _ _).
Defined.

Definition existᶠ : El (
  Πᶠ (A : El Typeᶠ) (B : El (A →ᶠ Typeᶠ)) (x : El A) (y : El (B · x)),
    sigmaᶠ · A · B).
Proof.
refine (λᶠ A B x y, _).
refine (exist _ _ (ret _) (existᴿ A B x y)).
Defined.

Definition sigma_rectᶠ : El
  (Πᶠ (A : El Typeᶠ) (B : El (A →ᶠ Typeᶠ)) (P : El (sigmaᶠ · A · B →ᶠ Typeᶠ)),
  (Πᶠ x y, P · (existᶠ · A · B · x · y)) →ᶠ Πᶠ (p : El (sigmaᶠ · A · B)), P · p).
Proof.
refine (λᶠ A B P Pex p, _).
refine (
match p.(prf) as pr in sigmaᴿ _ _ p return El (P · (exist _ _ _ pr)) with
| existᴿ _ _ x y => Pex · x · y
end
).
Defined.

(** Does not hold *)
Definition choice : El (
  Πᶠ (A B : El Typeᶠ) (P : El (A →ᶠ B →ᶠ Typeᶠ)),
    (Πᶠ x, [[ sigmaᶠ · B · (λᶠ y, P · x · y) ]]) →ᶠ
    [[ sigmaᶠ · (A →ᶠ B) · (λᶠ f, Πᶠ x, P · x · (f · x)) ]]
).
Proof.
Abort.

Inductive sum (A B : Type) :=
| inl : A -> sum A B
| inr : B -> sum A B.

Inductive sumᴿ (A B : El Typeᶠ) :
  M (sum (El A) (El B)) -> Type :=
| inlᴿ : forall x, sumᴿ A B (ret (inl _ _ x))
| inrᴿ : forall y, sumᴿ A B (ret (inr _ _ y)).

Definition sumᶠ : El (Typeᶠ →ᶠ Typeᶠ →ᶠ Typeᶠ).
Proof.
refine (λᶠ A B, _).
refine (exist _ _ (ret _) (IsType _ (sumᴿ A B))).
Defined.

Definition em : El (Πᶠ A, [[ sumᶠ · A · (A →ᶠ Falseᶠ) ]]).
Proof.
refine (λᶠ A, _).
refine (exist _ _ _ tt).
cbn.
refine (fun ω => ω (inr _ _ (λᶠ x, _))).
destruct (ω (inl _ _ x)).
Defined.

Module Univ.

Inductive path {A} (x : A) : A -> Type :=
| refl : path x x.

Definition isContr A := sig A (fun x => forall y, path x y).

Definition fiber {A B} (f : A -> B) (y : B) : Type :=
  sig A (fun x => path y (f x)).

Definition isEquiv {A B} (f : A -> B) :=
  forall y, isContr (fiber f y).

Definition equiv A B := sig (A -> B) isEquiv.

Definition Univalence := forall A, isContr (sig Type (fun X => equiv X A)).

(*
Definition idToEquiv A B (e : path A B) : sig :=
  @path_rect Type A (fun B _ => A -> B) (fun x => x) B e.

Definition Univalence := forall A B, @isEquiv (path A B) (A -> B) (idToEquiv A B).
*)

End Univ.

Module Univᶠ.

Inductive pathᵀ {A : El Typeᶠ} (x : El A) : El A -> Type :=
| reflᵀ : pathᵀ x x.

Inductive pathᴿ {A : El Typeᶠ} (x : El A) : forall y, M (pathᵀ x y) -> Type :=
| reflᴿ : pathᴿ x x (ret (reflᵀ x)).

Definition pathᶠ : El (Πᶠ (A : El Typeᶠ), A →ᶠ A →ᶠ Typeᶠ).
Proof.
refine (λᶠ A x y, _).
refine (exist _ _ (ret _) (IsType _ (pathᴿ x y))).
Defined.

Definition reflᶠ : El (Πᶠ (A : El Typeᶠ) (x : El A), pathᶠ · A · x · x).
Proof.
refine (λᶠ (A : El Typeᶠ) (x : El A), _).
refine (exist _ _ _ (reflᴿ _)).
Defined.

Definition path_rectᶠ :
  El (Πᶠ (A : El Typeᶠ) (x : El A)
    (P : El (Πᶠ (a : El A), pathᶠ · A · x · a →ᶠ Typeᶠ)),
       P · x · (reflᶠ · A · x) →ᶠ Πᶠ (y : El A) (p : El (pathᶠ · A · x · y)), P · y · p).
Proof.
refine (λᶠ A x P p y e, _).
destruct e as [? [ ] ].
refine p.
Defined.

Definition isContrᶠ : El (Typeᶠ →ᶠ Typeᶠ) :=
  λᶠ A, sigmaᶠ · A · (λᶠ x, Πᶠ (y : El A), pathᶠ · A · x · y).

Definition fiberᶠ :
  El (Πᶠ (A : El Typeᶠ) (B : El Typeᶠ), (A →ᶠ B) →ᶠ B →ᶠ Typeᶠ) :=
  λᶠ A B f y, sigmaᶠ · A · (λᶠ x, pathᶠ · B · y · (f · x)).

Definition isEquivᶠ :
  El (Πᶠ (A : El Typeᶠ) (B : El Typeᶠ) (f : El (A →ᶠ B)), Typeᶠ) :=
  λᶠ (A : El Typeᶠ) (B : El Typeᶠ) f, Πᶠ (y : El B), isContrᶠ · (fiberᶠ · A · B · f · y).

Definition equivᶠ :=
  λᶠ (A : El Typeᶠ) (B : El Typeᶠ),
  sigmaᶠ · (A →ᶠ B) · (λᶠ f, isEquivᶠ · A · B · f).

Definition Univalenceᶠ := Πᶠ (A : El Typeᶠ),
  isContrᶠ · (sigmaᶠ · Typeᶠ · (λᶠ (X : El Typeᶠ), equivᶠ · X · A)).

(*
Definition idToEquivᶠ :=
  λᶠ (A : El Typeᶠ) (B : El Typeᶠ) (e : El (pathᶠ · Typeᶠ · A · B)),
  path_rectᶠ · Typeᶠ · A · (λᶠ (B : El Typeᶠ) _, A →ᶠ B) · (λᶠ (x : El A), x) · B · e.

Definition Univalenceᶠ := Πᶠ (A : El Typeᶠ) (B : El Typeᶠ),
  isEquivᶠ · (pathᶠ · Typeᶠ · A · B) · (A →ᶠ B) · (idToEquivᶠ · A · B).
*)

Lemma equiv_prod : forall A (B : El (A →ᶠ Typeᶠ)),
  Univ.equiv (El (Πᶠ (x : El A), B · x)) (forall (x : El A), El (B · x)).
Proof.
intros A B.
exists (fun f x => f · x).
intros f.
unshelve refine (exist _ _ _ _).
+ unshelve refine (exist _ _ (λᶠ x, f x) _).
  reflexivity.
+ intros [g e].
  refine (
    match e in Univ.path _ h return
      Univ.path
        {|
        wit := λᶠ x : El A, f x;
        prf := Univ.refl (fun x : El A => (λᶠ x0 : El A, f x0) · x) |}
      (exist _ _ (λᶠ x, h x) e)
    with
    | Univ.refl _ => _
    end
  ).
reflexivity.
Defined.

Lemma path_sig : forall A (B : A -> Type) x₀ x₁ (y₀ : B x₀) (y₁ : B x₁)
  (ex : Univ.path x₀ x₁)
  (ey : match ex in Univ.path _ x return B x -> Type
  with
  | Univ.refl _ => fun y => Univ.path y₀ y
  end y₁),
  Univ.path (exist A B x₀ y₀) (exist A B x₁ y₁).
Proof.
intros.
destruct ex.
destruct ey.
reflexivity.
Defined.

(*

Lemma equiv_pathᵀ : forall (A : El Typeᶠ) (x y : El A),
  Univ.equiv (@pathᵀ A x y) (@Univ.path (El A) x y).
Proof.
intros A x y.
unshelve refine (exist _ _ _ _).
+ intros []; reflexivity.
+ intros e.
  unshelve refine (exist _ _ _ _).
  unshelve refine (exist _ _ _ _).
  - destruct e; reflexivity.
  - destruct e; reflexivity.
  - intros [e' α].
    destruct e.
    unshelve refine (path_sig _ _ _ _ _ _ _ _).
clear α.
Defined.

Lemma equiv_path : forall (A : El Typeᶠ) (x y : El A),
  Univ.equiv (El (pathᶠ · A · x · y)) (@Univ.path (El A) x y).
Proof.
Abort.

Lemma Univalence_preservation : Univ.Univalence -> El Univalenceᶠ.
Proof.
intros univ.
refine (λᶠ A, _).
unshelve refine (existᶠ · _ · _ · _ · _).
+ unshelve refine (existᶠ · _ · _ · A · _).
  unshelve refine (existᶠ · _ · _ · (λᶠ (x : El A), x) · _).
  refine (λᶠ x, _).
  unshelve refine (existᶠ · _ · _ · (existᶠ · _ · _ · x · (reflᶠ · _ · x)) · _).
  refine (λᶠ p, _).
  refine (sigma_rectᶠ · _ · _ · _ · _ · p).
  refine (λᶠ y q, _).
  change (
    El
      (pathᶠ · (fiberᶠ · A · A · (λᶠ x : El A, x) · x)
       · (existᶠ · A · (pathᶠ · A · x) · x · (reflᶠ · A · x))
       · (existᶠ · A · (λᶠ y : El A, pathᶠ · A · x · y) · y
          · q))
  ).
  refine (path_rectᶠ · A · x · (λᶠ y q, pathᶠ · (fiberᶠ · A · A · (λᶠ x : El A, x) · x)
       · (existᶠ · A · (pathᶠ · A · x) · x · (reflᶠ · A · x))
       · (existᶠ · A · (λᶠ y : El A, pathᶠ · A · x · y) · y
          · q)) · _ · y · q).
  refine (reflᶠ · _ · _).
+ refine (λᶠ X, _).


Qed.
