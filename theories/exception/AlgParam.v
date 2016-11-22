Set Universe Polymorphism.
Set Primitive Projections.

Inductive unit := tt.

Axiom E : Type.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Inductive M (A : Type) :=
| Ok : A -> M A
| Err : E -> M A.

Definition pure {A} (P : A -> Type) (l : M A) :=
match l with
| Ok _ x => P x
| Err _ _ => False
end.

Definition map {A B} (f : A -> B) (l : M A) : M B :=
match l with
| Ok _ x => Ok _ (f x)
| Err _ e => Err _ e
end.

Definition pointwise {A} (f : A -> Type) (l : M A) : Type :=
match l with
| Ok _ x => f x
| Err _ _ => unit
end.

Definition hlist (T : M Type) := pointwise (fun A => A) T.
Definition is_alg (T : M Type) := pointwise (fun A => M A -> A) T.

Record TYPE := {
  wit : M Type;
  alg : is_alg wit;
  val : pointwise (fun A => A -> Type) wit;
}.

Definition El (A : TYPE) : Type := hlist A.(wit).

Definition is_pure (A : TYPE) : El A -> Type :=
match A.(wit) as T return pointwise (fun A => A -> Type) T -> hlist T -> Type with
| Ok _ _ => fun P x => P x
| Err _ _ => fun _ _ => False
end A.(val).

Definition bind {A B} (l : M A) (f : A -> M B) : M B :=
match l with
| Ok _ x => f x
| Err _ e => Err _ e
end.

Definition pointwise_alg {T} (f : is_alg T) (l : M (hlist T)) : hlist T :=
match T return is_alg T -> M (hlist T) -> hlist T with
| Ok _ x => fun f l => f l
| Err _ e => fun f l => tt
end f l.

Definition Typeᶫ : TYPE.
Proof.
refine {|
  wit := Ok _ TYPE;
  alg := fun T => {| wit := bind T wit; alg := _ |};
  val := fun T => pure (fun _ => unit) T.(wit);
|}.
{
unfold is_alg.
destruct T as [A|e].
+ apply A.(alg).
+ exact tt.
}
{
destruct T as [A|e]; cbn in *; [exact A.(val)|exact tt].
}
Defined.

Check Typeᶫ : El Typeᶫ.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := Ok _ (forall x : El A, El (B x));
  alg := fun f x => pointwise_alg (B x).(alg) (map (fun f => f x) f);
  val := fun f => forall x : El A, is_pure A x -> is_pure (B x) (f x);
|}.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Inductive bool_pure : M bool -> Type :=
| true_pure : bool_pure (Ok _ true)
| false_pure : bool_pure (Ok _ false)
.

Definition boolᶫ : TYPE := {|
  wit := Ok _ (M bool);
  alg := fun b => bind b (fun b => b);
  val := bool_pure;
|}.

Definition trueᶫ : El boolᶫ := Ok _ true.
Definition falseᶫ : El boolᶫ := Ok _ false.

Definition hbind {A B} (l : M A) (f : A -> El B) : El B :=
match l with
| Ok _ x => f x
| Err _ e => pointwise_alg B.(alg) (Err _ e)
end.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b).
Proof.
induction b as [be|be b IHb]; cbn in *.
+ destruct be; [exact Pt|exact Pf].
+ exact tt.
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Lemma bool_rec_pure : is_pure
  (Prodᶫ (Prodᶫ boolᶫ (fun _ => Typeᶫ)) (fun P => Prodᶫ _ (fun Pt => Prodᶫ _ (fun Pf => Prodᶫ _ _))))
  bool_recᶫ.
Proof.
intros P HP Pt HPt Pf HPf b Hb.
induction b as [[|]|e]; cbn in *.
+ assumption.
+ assumption.
+ inversion Hb.
Defined.

Definition Eᶫ : El Typeᶫ := {|
  wit := Ok _ E;
  alg := fun e => match e with Ok _ e => e | Err _ e => e end;
  val := fun _ => unit
|}.

Definition fail : El (Prodᶫ Eᶫ (fun _ => Prodᶫ Typeᶫ (fun A => A))) :=
  fun e A => pointwise_alg A.(alg) (Err _ e).

Inductive False_pure : M False -> Type :=.

Definition Falseᶫ : TYPE := {|
  wit := Ok _ (M False);
  alg := fun b => bind b (fun b => b);
  val := False_pure;
|}.

Record sigma (A : Type) (B : A -> Type) := exist {
  proj1 : A;
  proj2 : B proj1;
}.

Arguments exist {_ _} _ _.
Arguments proj1 {_ _} _.
Arguments proj2 {_ _} _.

Definition Sigmaᶫ (A : TYPE) (B : El A -> TYPE): TYPE := {|
  wit := Ok _ (M (sigma (El A) (fun x => El (B x))));
  alg := fun b => bind b (fun b => b);
  val := pure (fun p => prod (is_pure _ p.(proj1)) (is_pure _ p.(proj2)));
|}.

Section Indep.

Variable A : TYPE.

Variable B : El boolᶫ -> TYPE.

Variable e : E.

Definition N : TYPE := Prodᶫ A (fun _ => Falseᶫ).
Definition P : TYPE := Prodᶫ N (fun _ => Sigmaᶫ boolᶫ B).
Definition Q : TYPE := Sigmaᶫ boolᶫ (fun b => Prodᶫ N (fun _ => B b)).

Definition Indep := Prodᶫ P (fun _ => Q).

Definition indep : El Indep.
Proof.
intros f; cbn in *.
specialize (f (fun _ : El A => fail e Falseᶫ)).
refine (bind f (fun p => Ok _ _)).
destruct p as [b y].
refine (exist b (fun _ => y)).
Defined.

(*
Not true :
Lemma indep_pure : is_pure _ indep.
Proof.
*)

End Indep.

Lemma consistency : forall f : El (Prodᶫ Typeᶫ (fun A => A)), is_pure _ f -> False.
Proof.
intros f Hf.
cbn in *.
specialize (Hf Falseᶫ); cbn in *.
destruct (Hf tt).
Defined.
