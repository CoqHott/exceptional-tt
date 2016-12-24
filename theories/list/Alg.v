Set Universe Polymorphism.
Set Primitive Projections.

Record sig A (P : A -> Type) := exist {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Inductive nlist (A : Type) :=
| nil : A -> nlist A
| cons : A -> nlist A -> nlist A.

Definition ret {A} (x : A) := nil A x.

Fixpoint map {A B} (f : A -> B) (l : nlist A) : nlist B :=
match l with
| nil _ x => nil _ (f x)
| cons _ x l => cons _ (f x) (map f l)
end.

Fixpoint pointwise {A} (f : A -> Type) (l : nlist A) : Type :=
match l with
| nil _ x => f x
| cons _ x l => prod (f x) (pointwise f l)
end.

Definition TYPE := nlist (sig Type (fun A => nlist A -> A)).

Definition mkTYPE (A : Type) (alg : nlist A -> A) : TYPE := nil _ (exist _ _ A alg).

Definition El (A : TYPE) : Type := pointwise wit A.

Fixpoint app {A} (l1 l2 : nlist A) :=
match l1 with
| nil _ x => cons _ x l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Fixpoint bind {A B} (l : nlist A) (f : A -> nlist B) : nlist B :=
match l with
| nil _ x => f x
| cons _ x l => app (f x) (bind l f)
end.

Fixpoint happ {A} : El A -> El A -> El A :=
match A return El A -> El A -> El A with
| nil _ A => fun x y => A.(prf) (cons _ x (nil _ y))
| cons _ A T => fun x y =>
  pair (A.(prf) (cons _ x.(fst) (nil _ y.(fst))))  (happ x.(snd) x.(snd))
end.

(*
Fixpoint hbind {A B} (l : nlist A) (f : A -> El B) {struct l} : El B :=
match l with
| nil _ x => f x
| cons _ x l => happ (f x) (hbind l f)
end.
*)

Definition hbind {A B} (l : nlist A) (f : A -> El B) : El B :=
(fix F l := match l with
| nil _ x => f x
| cons _ x l => happ (f x) (F l)
end) l.

Definition Typeᶫ : TYPE.
Proof.
refine (ret (exist _ _ TYPE _)).
refine (fun T => bind T (fun X => X)).
Defined.

Check Typeᶫ : El Typeᶫ.

Definition free A := mkTYPE (nlist A) (fun b => bind b (fun X => X)).

Definition pointwise_app {A} (f : A -> Type) (l1 l2 : nlist A)
  (p1 : pointwise f l1) (p2 : pointwise f l2) : pointwise f (app l1 l2) :=
(fix F l1 := match l1 return pointwise f l1 -> pointwise f (app l1 l2) with
| nil _ x => fun p1 => pair p1 p2
| cons _ x l1 => fun p1 => pair p1.(fst) (F l1 p1.(snd))
end) l1 p1.

(*
Fixpoint pointwise_app {A} (f : A -> Type) (l1 l2 : nlist A)
  (p1 : pointwise f l1) (p2 : pointwise f l2) {struct l1} : pointwise f (app l1 l2) :=
match l1 return forall l2, pointwise f l1 -> _ -> pointwise f (app l1 l2) with
| nil _ x => fun l2 p1 p2 => pair p1 p2
| cons _ x l1 => fun l2 p1 p2 => pair p1.(fst) (pointwise_app f l1 l2 p1.(snd) p2)
end l2 p1 p2.
*)

Fixpoint pbind {A} {B : A -> El Typeᶫ} (l : nlist A) (f : forall x : A, El (B x)) {struct l} : El (hbind l B) :=
match l return El (hbind l B) with
| nil _ x => f x
| cons _ x l => @pointwise_app _ wit (B x) (hbind l B) (f x) (pbind l f)
end.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE.
Proof.
refine (nil _ (exist _ _ (forall x : El A, El (B x)) _)).
refine (fun f x => hbind f (fun f => f x)).
Defined.

Notation "A →ᶫ B" := (Prodᶫ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶫ'  x .. y , P" := (Prodᶫ _ (fun x => .. (Prodᶫ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition pbind' {A R}
  {B : A -> El (R  →ᶫ Typeᶫ)}
  (l : nlist A) (r : El R) (f : forall x : A, El (B x r)) : El (hbind l B r) :=
(fix F l := match l return El (hbind l B r) with
| nil _ x => f x
| cons _ x l => @pointwise_app _ wit (B x r) (hbind l B r) (f x) (F l)
end) l.

Definition boolᶫ : TYPE.
Proof.
refine (nil _ (exist _ _ (nlist bool) _)).
refine (fun b => bind b (fun b => b)).
Defined.

Definition trueᶫ : El boolᶫ := nil _ true.
Definition falseᶫ : El boolᶫ := nil _ false.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition θ_bool (n : El boolᶫ) : (El boolᶫ -> El Typeᶫ) -> El Typeᶫ :=
  bool_caseᶫ ((boolᶫ →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k trueᶫ) (fun k => k falseᶫ) n.

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (θ_bool b P) :=
  @pbind' bool (boolᶫ →ᶫ Typeᶫ) _ b P (bool_rec _ Pt Pf).

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Inductive nat_ :=
| O_ : nat_
| S_ : nlist nat_ -> nat_.

Definition natᶫ : TYPE := mkTYPE (nlist nat_) (fun l => bind l (fun n => n)).

Definition Oᶫ : El natᶫ := ret O_.
Definition Sᶫ : El (natᶫ →ᶫ natᶫ) := fun n => ret (S_ n).

Definition nat_caseᶫ (P : TYPE) (P0 : El P) (PS : El natᶫ -> El P -> El P) (n : El natᶫ) : El P.
Proof.
refine (hbind n (fun n => _)).
refine ((fix F n := match n return El P with O_ => P0 | S_ n => PS n (hbind n F) end) n).
Defined.

Check (eq_refl : (fun P P0 PS n => nat_caseᶫ P P0 PS Oᶫ) = (fun P P0 PS n => P0)).
Check (eq_refl : (fun P P0 PS n => nat_caseᶫ P P0 PS (Sᶫ n)) = (fun P P0 PS n => PS n (nat_caseᶫ P P0 PS n))).

Definition θ_nat (n : El natᶫ) : (El natᶫ -> El Typeᶫ) -> El Typeᶫ :=
  nat_caseᶫ ((natᶫ →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k Oᶫ) (fun _ r k => r (fun n => k (Sᶫ n))) n.

Definition nat_rectᶫ (P : El natᶫ -> TYPE) (P0 : El (P Oᶫ)) (PS : forall n : El natᶫ, El (θ_nat n P) -> El (θ_nat (Sᶫ n) P)) (n : El natᶫ) :
  El (θ_nat n P).
Proof.
refine (pbind' n _ (fun n => _)).
match goal with [ |- El (?X n P) ] => set (K := X) end.
refine ((fix F n := match n return El (K n P) with O_ => P0 | S_ n => PS n _ end) n).
refine (@pbind' nat_ (Πᶫ _ : El natᶫ, Typeᶫ) _ n P F).
Defined.

Check (eq_refl : (fun P P0 PS n => nat_rectᶫ P P0 PS Oᶫ) = (fun P P0 PS n => P0)).
Check (eq_refl : (fun P P0 PS n => nat_rectᶫ P P0 PS (Sᶫ n)) = (fun P P0 PS n => PS n (nat_rectᶫ P P0 PS n))).

Inductive list_ (A : TYPE) :=
| nil_ : list_ A
| cons_ : El A -> nlist (list_ A) -> list_ A.

Definition listᶫ : El (Typeᶫ →ᶫ Typeᶫ) :=
  fun A => mkTYPE (nlist (list_ A)) (fun l => bind l (fun n => n)).

Definition nilᶫ : El (Πᶫ (A : El Typeᶫ), listᶫ A) := fun A => ret (nil_ A).
Definition consᶫ : El (Πᶫ (A : El Typeᶫ), A →ᶫ listᶫ A →ᶫ listᶫ A) :=
  fun A x l => ret (cons_ A x l).

Definition list_caseᶫ : El (Πᶫ (A : El Typeᶫ) (P : El Typeᶫ) (P0 : El P) (PS : El (A →ᶫ listᶫ A →ᶫ P →ᶫ P)) (l : El (listᶫ A)), P).
Proof.
intros A P P0 PS l.
refine (hbind l (fun l => _)).
refine ((fix F n := match n return El P with nil_ _ => P0 | cons_ _ x l => PS x l (hbind l F) end) l).
Defined.

Check (eq_refl : (fun A P P0 PS => list_caseᶫ A P P0 PS (nilᶫ A)) = (fun A P P0 PS => P0)).
Check (eq_refl : (fun A P P0 PS x l => list_caseᶫ A P P0 PS (consᶫ A x l)) = (fun A P P0 PS x l => PS x l (list_caseᶫ A P P0 PS l))).

Definition θ_list : El (Πᶫ (A : El Typeᶫ), listᶫ A →ᶫ (listᶫ A →ᶫ Typeᶫ) →ᶫ Typeᶫ) :=
  fun A l k => list_caseᶫ A ((listᶫ A →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k (nilᶫ A)) (fun x _ r k => r (fun l => k (consᶫ A x l))) l k.

Definition list_rectᶫ : El (Πᶫ
    (A : El Typeᶫ) (P : El (listᶫ A →ᶫ Typeᶫ))
    (P0 : El (P (nilᶫ A)))
    (PS : El (Πᶫ (x : El A) (l : El (listᶫ A)), θ_list A l P →ᶫ θ_list A (consᶫ A x l) P))
    (l : El (listᶫ A)),
      θ_list A l P).
Proof.
intros A P P0 PS l.
refine (pbind' l _ (fun l => _)).
match goal with [ |- El (?X l P) ] => set (K := X) end.
refine ((fix F l := match l return El (K l P) with nil_ _ => P0 | cons_ _ x l => PS x l _ end) l).
refine (@pbind' (list_ A) (Πᶫ _ : El (listᶫ A), Typeᶫ) _ l P F).
Defined.

Check (eq_refl : (fun A P P0 PS => list_rectᶫ A P P0 PS (nilᶫ A)) = (fun A P P0 PS => P0)).
Check (eq_refl : (fun A P P0 PS x l => list_rectᶫ A P P0 PS (consᶫ A x l)) = (fun A P P0 PS x l => PS x l (list_rectᶫ A P P0 PS l))).

Inductive eq_ (A : El Typeᶫ) (x : El A) : El A -> Type :=
| refl_ : eq_ A x x.

Definition eqᶫ : El (Πᶫ (A : El Typeᶫ), A →ᶫ A →ᶫ Typeᶫ) :=
  fun A x y => mkTYPE (nlist (eq_ A x y)) (fun l => bind l (fun n => n)).

Definition reflᶫ : El (Πᶫ (A : El Typeᶫ) (x : El A), eqᶫ A x x) :=
  fun A x => ret (refl_ A x).

Definition eq_caseᶫ : El (
  Πᶫ (A : El Typeᶫ) (x : El A) (P : El (A →ᶫ Typeᶫ)),
  P x →ᶫ Πᶫ (y : El A), eqᶫ A x y →ᶫ P y).
Proof.
intros A x P p y e.
refine (hbind e (fun e => _)).
refine (eq__rect A x (fun y _ => El (P y)) p y e).
Defined.

Check (eq_refl : (fun A x P p => eq_caseᶫ A x P p x (reflᶫ A x)) = (fun A x P p => p)).

Definition θ_eq : El (
  Πᶫ (A : El Typeᶫ) (x : El A) (y : El A),
    eqᶫ A x y →ᶫ (Πᶫ (y : El A), eqᶫ A x y →ᶫ Typeᶫ) →ᶫ Typeᶫ
  ) :=
  fun A x y e =>
    eq_caseᶫ A x (fun y => (Πᶫ (y : El A), eqᶫ A x y →ᶫ Typeᶫ) →ᶫ Typeᶫ) (fun k => k x (reflᶫ A x)) _ e.

Definition eq_rectᶫ : El (
  Πᶫ (A : El Typeᶫ) (x : El A)
    (P : El (Πᶫ (y : El A), eqᶫ A x y →ᶫ Typeᶫ))
    (Prefl : El (P x (reflᶫ A x)))
    (y : El A) (e : El (eqᶫ A x y)),
    θ_eq A x y e P
).
Proof.
refine (fun A x P prefl y e => _).
unfold θ_eq, eq_caseᶫ.
refine (
@pbind' (eq_ A x y) _ _ e _ (fun e => _)
).
destruct e; exact prefl.
Defined.

Check (eq_refl : (fun A x P p => eq_rectᶫ A x P p x (reflᶫ A x)) = (fun A x P p => p)).

(** Proving that linear terms commute with storage operators *)

Inductive box (A : TYPE) := Box : El A -> box A.

Definition boxᶫ (A : TYPE) : TYPE :=
  mkTYPE (nlist (box A)) (fun b => bind b (fun b => b)).

Definition Boxᶫ (A : TYPE) (x : El A) : El (boxᶫ A) := ret (Box _ x).

Definition box_rectᶫ (A : TYPE) (P : TYPE) (pb : El A -> El P) (b : El (boxᶫ A)) : El P :=
  hbind b (fun b => box_rect A (fun _ => El P) pb b).

(** Linear definition taken from Paul Blain Levy last POPL article. *)
Definition linear {A B} (f : El (A →ᶫ B)) : Prop :=
  forall b : El (boxᶫ A), f (box_rectᶫ _ _ (fun x => x) b) = box_rectᶫ _ _ f b.

Lemma linear_algebra_compat : forall A B (f : El (free A →ᶫ B)),
  linear f -> forall x, hbind x (fun x => f (ret x)) = f x.
Proof.
intros A B f Hf x.
induction x as [x|x₀ x]; cbn.
+ reflexivity.
+ change (happ (f (ret x₀)) (hbind x (fun x => f (ret x))) = f (cons A x₀ x)).
  rewrite IHx; clear IHx.
  specialize (Hf (cons _ (Box (free A) (ret x₀)) (Boxᶫ (free A) x))).
  symmetry; exact Hf.
Defined.

Lemma nat___rect : forall (P : nat_ -> Type) (Q : nlist nat_ -> Type)
  (p0 : P O_)
  (pS : forall n, Q n -> P (S_ n))
  (qnil : forall n, P n -> Q (nil _ n))
  (qcons : forall n l, P n -> Q l -> Q (cons _ n l)), forall n, P n.
Proof.
intros P Q p0 pS qnil qcons.
refine (
fix nat___rect n := match n return P n with
| O_ => p0
| S_ n =>
  pS _
    ((fix F n := match n return Q n with
    | nil _ x => qnil x (nat___rect x)
    | cons _ x n => qcons x n (nat___rect x) (F n) end) n)
end
).
Defined.

Definition nat___rectl (P : nat_ -> Type) (Q : nlist nat_ -> Type)
  (p0 : P O_)
  (pS : forall n, Q n -> P (S_ n))
  (qnil : forall n, P n -> Q (nil _ n))
  (qcons : forall n l, P n -> Q l -> Q (cons _ n l)) : forall n, Q n :=
fix F n := match n with
| nil _ x => qnil x (nat___rect P Q p0 pS qnil qcons x)
| cons _ x n => qcons x n (nat___rect P Q p0 pS qnil qcons x) (F n)
end.

Lemma hbind_extensional : forall A B f g x,
  (forall x, f x = g x) -> @hbind A B x f = @hbind A B x g.
Proof.
intros A B f g x Heq.
induction x; cbn.
+ apply Heq.
+ f_equal; [apply Heq|apply IHx].
Qed.

Lemma happ_assoc : forall A l1 l2 l3,
  @happ (free A) l1 (happ l2 l3) = happ (happ l1 l2) l3.
Proof.
intros A l1; induction l1 as [x|x l1 IHl]; intros l2 l3; cbn.
+ reflexivity.
+ cbn in IHl; rewrite IHl; reflexivity.
Qed.

Lemma hbind_happ : forall A B l1 l2 f,
  @hbind A (free B) (app l1 l2) f = happ (hbind l1 f) (hbind l2 f).
Proof.
intros A B l1; induction l1 as [x|x l1 IHl]; intros l2 f; cbn.
+ reflexivity.
+ change (happ (f x) (hbind (app l1 l2) f) = happ (happ (f x) (hbind l1 f)) (hbind l2 f)).
  rewrite IHl, happ_assoc; reflexivity.
Qed.

Lemma hbind_assoc : forall A B C l f g,
  @hbind B (free C) (@hbind A (free B) l f) g = hbind l (fun x => hbind (f x) g).
Proof.
intros A B C l f g; revert C g.
induction l as [x|x l IHl]; intros C g; cbn.
+ reflexivity.
+ change (hbind (app (f x) (hbind l f)) g = happ (hbind (f x) g) (hbind l (fun x => hbind (f x) g))).
  rewrite <- IHl, hbind_happ; reflexivity.
Qed.

Lemma linear_bool_storage_compat : forall (P : El (boolᶫ →ᶫ Typeᶫ)),
  linear P -> forall n, θ_bool n P = P n.
Proof.
intros P HP b.
unfold θ_bool, bool_caseᶫ.
match goal with [|- hbind b ?f P = _ ] => set (F := f) end.
induction b as [b₀|b₀ b IHb]; cbn.
+ destruct b₀; reflexivity.
+ change (app (F b₀ P) (hbind b F P) = P (cons _ b₀ b)).
  rewrite IHb.
  specialize (HP (cons _ (Box boolᶫ (ret b₀)) (Boxᶫ boolᶫ b))).
  cbn in HP; rewrite HP; f_equal.
  destruct b₀; reflexivity.
Qed.

(** Not true *)
Lemma linear_nat_storage_compat : forall (P : El (natᶫ →ᶫ Typeᶫ)),
  linear P -> forall n, θ_nat n P = P n.
Proof.
intros P HP n.
unfold θ_nat, nat_caseᶫ.
set (F := (fix F (n : nat_) : El (Πᶫ _ : El (Πᶫ _ : El natᶫ, Typeᶫ), Typeᶫ) :=
      match n with
      | O_ => fun k : El (Πᶫ _ : El natᶫ, Typeᶫ) => k Oᶫ
      | S_ n =>
          fun k : El (Πᶫ _ : El natᶫ, Typeᶫ) =>
          hbind n F (fun n : El natᶫ => k (Sᶫ n))
      end)).
revert P HP.
refine (nat___rectl (fun n => forall P, linear P -> F n P = P (nil nat_ n)) (fun n => forall P, linear P -> hbind n F P = P n) _ _ _ _ n);
cbn; clear n.
+ intros P HP; reflexivity.
+ intros n IHn P HP.
  rewrite IHn; [reflexivity|].
  clear - HP.
  admit. (** That's just not true, because S blocks reduction. *)
(*
  intros b; unfold box_rectᶫ.
  induction b as [[b₀]|[b₀] b]; cbn.
  - reflexivity.
  - change (
      P (Sᶫ (app b₀ (hbind b (fun x => box_rect natᶫ (fun _ : box natᶫ => El natᶫ)
        (fun x : nlist nat_ => x) x)))) =
      app (P (Sᶫ b₀)) (hbind b (fun x => box_rect natᶫ (fun _ : box natᶫ => El Typeᶫ)
        (fun n : nlist nat_ => P (Sᶫ n)) x))
    ).
    admit.
*)
+ intros n IHn P HP.
  apply IHn; assumption.
+ intros n l IHn IHl P HP.
  assert (Hnl := HP (cons _ (Box natᶫ (ret n)) (Boxᶫ natᶫ l))).
  cbn in Hnl. rewrite Hnl; clear Hnl.
  f_equal; [apply IHn, HP|apply IHl, HP].
Abort.
