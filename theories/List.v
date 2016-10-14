Set Primitive Projections.
Set Universe Polymorphism.

Record Pack (A : nat -> Type) := mkPack {
  wit : nat;
  val : A wit;
}.

Arguments wit {_} _.
Arguments val {_} _.

Record prod (A B : Type) := pair { fst : A; snd : B }.

Arguments pair {_ _} _ _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Fixpoint nTYPE (A : Type) (n : nat) := match n with
| 0 => A
| S n => prod A (nTYPE A n)
end.

Definition TYPE := Pack (nTYPE Type).

Definition El (T : TYPE) : Type :=
  (fix F (n : nat) {struct n} :=
  match n as wit return nTYPE Type wit -> Type with
  | 0 => fun T => Pack (nTYPE T)
  | S n => fun T => prod (Pack (nTYPE (fst T))) (F n (snd T))
  end)
    T.(wit) T.(val)
.

Definition Typeᴸ : TYPE := mkPack (nTYPE Type) 0 Type.

Check Typeᴸ : El Typeᴸ.

Definition Prodᴸ (A : TYPE) (B : El A -> TYPE) : TYPE :=
  mkPack _ 0 (forall x : El A, El (B x)).

Definition Lamᴸ {A : TYPE} {B : forall x : El A, TYPE}
  (f : forall x : El A, El (B x)) : El (Prodᴸ A B) :=
  mkPack _ 0 f.

Definition union (A : Type) (x y : Pack (nTYPE A)) : Pack (nTYPE A) := {|
  wit := S (x.(wit) + y.(wit));
  val :=
    (fix F (n : nat) :=
    match n return nTYPE A n -> forall m, nTYPE A m -> nTYPE A (S n + m) with
    | 0 => fun T m U => pair T U
    | S n => fun T m U => pair T.(fst) (F n T.(snd) m U)
    end) x.(wit) x.(val) y.(wit) y.(val)
|}.

Definition ambᴸ (A : TYPE) (x y : El A) : El A.
Proof.
destruct A as [n A]; unfold El in *.
revert A x y; induction n as [|n F]; intros A x y; cbn in *.
+ exact (union A x y).
+ refine (pair (union _ (fst x) (fst y)) _).
  apply (F (snd A) (snd x) (snd y)).
Defined.

Definition Appᴸ {A : TYPE} {B : forall x : El A, TYPE}
  (f : El (Prodᴸ A B)) (x : El A) : El (B x) :=
  (fix F (n : nat) : nTYPE (forall x : El A, El (B x)) n -> El (B x) :=
  match n with
  | 0 => fun f => f x
  | S n => fun f => ambᴸ _ (f.(fst) x) (F n f.(snd))
  end)
    f.(wit) f.(val)
.

Check eq_refl : (fun A B f x => @Appᴸ A B (Lamᴸ f) x) = (fun A B f x => f x).
