Set Universe Polymorphism.
Set Primitive Projections.

Record sig A (P : A -> Type) := {
  wit : A;
  prf : P wit;
}.

Arguments wit {_ _} _.
Arguments prf {_ _} _.

Record Pack (A : nat -> Type) := mkPack {
  idx : nat;
  val : A idx;
}.

Arguments idx {_} _.
Arguments val {_} _.

Record prod A B := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Fixpoint nTYPE (A : Type) (n : nat) := match n with
| 0 => A
| S n => prod A (nTYPE A n)
end.

Definition M (A : Type) := Pack (nTYPE A).

Fixpoint npointwise {A} (f : A -> Type) n : nTYPE A n -> Type :=
match n return nTYPE A n -> Type with
| 0 => fun x => f x
| S n => fun x => prod (f x.(fst)) (npointwise f n x.(snd))
end.

(*
Fixpoint map {A B} (f : A -> B) (l : nlist A) : nlist B :=
match l with
| nil _ x => nil _ (f x)
| cons _ x l => cons _ (f x) (map f l)
end.
*)

Definition pointwise {A} f l := @npointwise A f l.(idx) l.(val).

Definition hlist (T : M Type) := pointwise (fun A => A) T.
Definition is_alg (T : M Type) := pointwise (fun A => M A -> A) T.

Definition TYPE := Pack (nTYPE (sig Type (fun A => M A -> A))).

Definition El (A : TYPE) : Type := pointwise wit A.

Fixpoint app {A} (l1 l2 : T A) :=
match l1 with
| nil _ x => cons _ x l2
| cons _ x l1 => cons _ x (app l1 l2)
end.

Fixpoint bind {A B} (l : nlist A) (f : A -> nlist B) : nlist B :=
match l with
| nil _ x => f x
| cons _ x l => app (f x) (bind l f)
end.

Fixpoint pointwise_app {A} (f : A -> Type) (l1 l2 : nlist A)
  (p1 : pointwise f l1) (p2 : pointwise f l2) {struct l1} : pointwise f (app l1 l2) :=
match l1 return forall l2, pointwise f l1 -> _ -> pointwise f (app l1 l2) with
| nil _ x => fun l2 p1 p2 => pair p1 p2
| cons _ x l1 => fun l2 p1 p2 => pair p1.(fst) (pointwise_app f l1 l2 p1.(snd) p2)
end l2 p1 p2.

Fixpoint pointwise_alg {T} (f : is_alg T) (l : nlist (hlist T)) : hlist T :=
match T return is_alg T -> nlist (hlist T) -> hlist T with
| nil _ A => fun f l => f l
| cons _ A T => fun f l => pair (f.(fst) (map fst l)) (pointwise_alg f.(snd) (map snd l))
end f l.

Fixpoint hbind {A B} (alg : is_alg B) (l : nlist A) (f : A -> hlist B) {struct l} : hlist B :=
match l with
| nil _ x => f x
| cons _ x l => pointwise_alg alg (cons _ (f x) (nil _ (hbind alg l f)))
end.

Definition Typeᶫ : TYPE.
Proof.
refine {|
  wit := nil _ TYPE;
  alg := fun T => {| wit := bind T wit; alg := _ |};
|}.
unfold is_alg.
induction T as [A|A T IHT]; cbn.
+ apply A.(alg).
+ apply pointwise_app; [apply A.(alg)|apply IHT].
Defined.

Check Typeᶫ : El Typeᶫ.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := nil _ (forall x : El A, El (B x));
  alg := fun f x => pointwise_alg (B x).(alg) (map (fun f => f x) f)
|}.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition boolᶫ : TYPE := {| wit := nil _ (nlist bool); alg := fun b => bind b (fun b => b) |}.
Definition trueᶫ : El boolᶫ := nil _ true.
Definition falseᶫ : El boolᶫ := nil _ false.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind P.(alg) b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b).
Proof.
unfold El, bool_caseᶫ, hlist.
cbn in *.
induction b as [be|be b IHb]; cbn in *.
+ destruct be; [exact Pt|exact Pf].
+ refine (pointwise_app _ _ _ _ IHb).
  destruct be; [exact Pt|exact Pf].
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).
