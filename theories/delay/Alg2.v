Set Universe Polymorphism.
Set Primitive Projections.

Inductive unit := tt.

CoInductive M (A : Type) :=
   ret : A -> M A
|  step : M A -> M A.

Arguments step {_} _.
Arguments ret {_} _.

CoFixpoint map {A B} (f : A -> B) (s : M A) : M B :=
    match s with
    | ret x => ret (f x)
    | step s => step (map f s)
    end.

CoFixpoint bind {A B} (s : M A) (f : A -> M B) : M B :=
  match s with
  | ret x => f x
  | step s => step (bind s f)
  end.

(* CoInductive Stream (A:Type) := Cons : A -> Stream A -> Stream A.  *)

(* Arguments Cons {_} _ _. *)

(* CoFixpoint constStream {A} (a:A) := Cons a (constStream a). *)

(* CoFixpoint pointwise {A} (f : A -> Type) (s : M A) : Stream Type := *)
(* match s with *)
(* | ret x => Cons (f x) (constStream unit) *)
(* | step s => Cons unit (pointwise f s) *)
(* end. *)

Definition pointwise {A} (f : A -> Type) (s : M A) : Type :=
match s with
| ret x => f x
| step s => unit
end.

Definition hlist (T : M Type) := pointwise (fun A => A) T.
Definition is_alg (T : M Type) := pointwise (fun A => M A -> A) T.

(* CoFixpoint ElStream (A : Stream Type)   *)

Record TYPE := {
  wit : M Type;
  alg : is_alg wit;
}.

Definition El (A : TYPE) : Type := pointwise (fun A => A) A.(wit).

Definition mu {T} : M (M T) -> M T := fun x => bind x (fun x => x). 

Definition pointwise_alg {T} (f : is_alg T) (l : M (hlist T)) : hlist T
  :=
    match T as T return is_alg T -> M (hlist T) -> hlist T with
    | ret A => fun f l => f l
    | step T => fun _ _ => tt
    end f l.

Definition hbind {A B} (l : M A) (f : A -> El B) : El B :=
match l with
| ret x => f x
| step s =>
  let later := cofix later (s : M A) : M (El B) := match s with
  | ret x => ret (f x)
  | step s => step (later s)
  end in
  pointwise_alg (B.(alg)) (later s)
end.

Definition Typeᶫ : TYPE.
   (* :={| *)
   (*    wit := ret (M TYPE); *)
   (*    alg := mu *)
   (*  |}. *)
Proof.
  
  unshelve refine {|
      wit := ret TYPE;
      alg := fun T => Build_TYPE _ _
    |}.
  exact (bind T wit).
  unfold is_alg, pointwise; cbn.
  destruct T as [A|]; [|exact tt].
  destruct A as [wit alg]; cbn.
  unfold is_alg, pointwise in *.
  destruct wit as [X|]; [|exact tt].
  exact alg.
Defined.

Check Typeᶫ : TYPE.

Check Typeᶫ : El Typeᶫ.

Definition Prodᶫ (A : TYPE) (B : El A -> TYPE) : TYPE := {|
  wit := ret (forall x : El A, El (B x));
  alg := fun f x => pointwise_alg (B x).(alg) (map (fun f => f x) f)
|}.

Definition Lamᶫ {A B} (f : forall x : El A, El (B x)) : El (Prodᶫ A B) := f.
Definition Appᶫ {A B} (f : El (Prodᶫ A B)) (x : El A) := f x.

Definition ConstType (T : Type) : TYPE := {|
  wit := ret (M T);
  alg := fun b => bind b (fun b => b);
|}.

Definition boolᶫ : TYPE := ConstType bool. 
Definition trueᶫ : El boolᶫ := ret true.
Definition falseᶫ : El boolᶫ := ret false.

Definition bool_caseᶫ (P : TYPE) (Pt : El P) (Pf : El P) (b : El boolᶫ) : El P :=
  hbind b (fun b => if b then Pt else Pf).

Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_caseᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition bool_recᶫ (P : El boolᶫ -> TYPE)
  (Pt : El (P trueᶫ)) (Pf : El (P falseᶫ)) (b : El boolᶫ) : El (bool_caseᶫ Typeᶫ (P trueᶫ) (P falseᶫ) b).
Proof.
unfold bool_caseᶫ, hbind.
destruct b as [[|]|b]; cbn in *.
+ exact Pt.
+ exact Pf.
+ unfold El; cbn.
  unfold hlist, pointwise, bind; cbn.
  destruct b as [[|]|b]; cbn in *; unfold El, hlist, pointwise in *.
  - exact Pt.
  - exact Pf.
  - exact tt.
Defined.

Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf trueᶫ) = (fun P Pt Pf => Pt)).
Check (eq_refl : (fun P Pt Pf => bool_recᶫ P Pt Pf falseᶫ) = (fun P Pt Pf => Pf)).

Definition Falseᶫ : TYPE := ConstType False.

Definition Trueᶫ : TYPE := ConstType True. 

Notation "A →ᶫ B" := (Prodᶫ A (fun _ => B)) (at level 99, right associativity, B at level 200).

Notation "'Πᶫ'  x .. y , P" := (Prodᶫ _ (fun x => .. (Prodᶫ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Inductive Paths {A : Type} (x : A) : A -> Type :=  id_path : Paths x x.

Definition eqᶫ : El (Πᶫ (A : El Typeᶫ), A →ᶫ A →ᶫ Typeᶫ).
Proof.
  intros A x y. unshelve refine (Build_TYPE _ _).
  - exact (ret (M (Paths x y))).
  - intro m. refine (bind m (fun m => m)).
Defined.

Definition eq_reflᶫ : El (Πᶫ (A : El Typeᶫ) (x:El A), eqᶫ A x x)
  := fun A x => ret (id_path x).

Definition eq_caseᶫ (A : TYPE) (a : El A) (P : TYPE) (p : El P)
           (y : El A) (e : El (eqᶫ A a y)) : El P  :=
  hbind e (fun e => match e with id_paths => p end).

Check (eq_refl : (fun A a P p => eq_caseᶫ A a P p a (eq_reflᶫ A a)) = (fun A a P p => p)).

Definition eq_recᶫ (A : TYPE) (a : El A) (P : El A -> TYPE) (p : El (P a))
           (y : El A) (e : El (eqᶫ A a y)) : El (eq_caseᶫ A a Typeᶫ (P a) y e).
unfold eq_caseᶫ, hbind.
destruct e as [e|e]; cbn in *.
+ exact p.
+ unfold El. cbn.
  unfold hlist, pointwise, bind; cbn.
  destruct e as [e|e]; cbn in *.
  - destruct e. exact p.
  - exact tt. 
Defined.

Check (eq_refl : (fun A a P p y e => eq_recᶫ A a P p a (eq_reflᶫ A a)) =
                 (fun A a P p y e => p)).

Inductive Value {A} : M A -> A -> Type :=
  value_return : forall (a : A), Value (ret a) a
| value_step : forall (x: M A) (a : A), Value x a -> Value (step x) a.

CoInductive Diverge {A} : M A -> Type :=
  diverge : forall (x : M A), Diverge x -> Diverge (step x).

CoInductive included {A} : M A -> M A -> Type :=
  le_value : forall (x y : M A) (a:A) , Value x a -> Value y a -> included x y
| le_steps : forall (x y : M A), included x y -> included (step x) (step y)
| le_lstep : forall (x y : M A), included x y -> included (step x) y.

Infix "⊑" := included (at level 100).

Definition Increasing_sequence A (f : nat -> M A) := forall n, f n ⊑ f (S n).


CoFixpoint fstConv {A} : M A -> M A -> M A :=
  fun x y =>
    match x with
    | ret a => ret a
    | step x_ => match y with
               | ret b => ret b
               | step y_ => step (fstConv x_ y_)
                end
    end. 

CoFixpoint searchFstconv_aux {A} : (nat -> M A) -> nat -> M A -> M A :=
  fun f n x => match x with
            ret a => ret a
          | step x => step (searchFstconv_aux f (S n) (fstConv x (f n)))
          end. 

CoFixpoint div A : M A := step (div A). 

Definition searchFstconv {A} : (nat -> M A) -> M A :=
  fun f => searchFstconv_aux f 0 (div A).

Fixpoint iterate {X} (bot : X) (F : X -> X) (n : nat) : X :=
  match n with
    0 => bot
  | S n => F (iterate bot F n)
  end.

Definition Y2 {A B} (F : (A -> M B) -> A -> M B)  : A -> M B := fun x => searchFstconv (fun n => iterate (fun _ => div _) F n x).

Definition Y {A} (F : M A -> M A) : M A := searchFstconv (fun n => iterate (div _) F n).

Definition bisim {A} (x y : M A) : Type := (x ⊑ y) * (y ⊑ x).

CoFixpoint incl_equiv {A} (x y : M A) : (forall b, Value x b -> Value y b) -> x ⊑ y. 
Proof.
  intro e. destruct x.
  - exact (le_value (ret a) y a (value_return a) (e a (value_return a))). 
  - refine (le_lstep _ _ _). refine (incl_equiv _ _ _ _).
    intros b v. exact (e b (value_step _ _ v)). 
Defined.


CoInductive strong_bisim {A} : M A -> M A -> Type :=
  sb_value : forall (a:A) , strong_bisim (ret a) (ret a)
| sb_step : forall (x y : M A), strong_bisim x y -> strong_bisim (step x) (step y).

Fixpoint bisim_n {A} n (x y : M A) : Type :=
  match n with 0 => match x , y with ret a , ret b => a = b
                               | step _ , step _ => True
                               | _ , _ => False
                   end
          | S n => match x , y with step x , step y => bisim_n n x y
                               | _ , _ => False
                  end
  end.


Definition later : El (Πᶫ (A : El Typeᶫ), A →ᶫ A).
Proof. 
  intros A x. cbn in *.
  unfold El, pointwise in *.
  destruct A as [A algA]; simpl in *. 
  destruct A.
  - apply algA. exact (step (ret x)).
  - exact tt.
Defined.

Definition Box (T : TYPE) : TYPE := {|
  wit := ret (M (El T));
  alg := fun b => bind b (fun b => b);
|}.

Definition fixp2 : El (Πᶫ (A B : El Typeᶫ), ((A →ᶫ B) →ᶫ (A →ᶫ Box B)) →ᶫ (A →ᶫ B)).
Proof.
  intros A B f x. cbn in *.
  destruct B as [B algB]; simpl in *.
  destruct B; simpl in *; try exact tt.
  apply algB. generalize dependent x. refine (Y2 _).
  intros g x. exact (f (fun x => algB (g x)) x). 
Defined.

Definition fixp : El (Πᶫ (A : El Typeᶫ), (A →ᶫ Box A) →ᶫ A).
Proof.
  intros A f. cbn in *.
  destruct A as [A algA]; simpl in *.
  destruct A; simpl in *; try exact tt.
  apply algA. refine (Y _).
  intros x. exact (f (algA x)). 
Defined.


Definition natᶫ := ConstType nat.

Definition zeroᶫ : El natᶫ := ret 0. 

Definition sucᶫ : El (natᶫ →ᶫ natᶫ) := map S.

Fixpoint eval (n:nat) {A} {struct n} : M A -> option A.
Proof. 
  intros x. destruct x as [a | x].
  - exact (Some a).
  - destruct n.
    + exact None.
    + exact (eval n _ x).
Defined.

Definition unbox : El (Πᶫ (A : El Typeᶫ), Box A →ᶫ A).
Proof.
  intros A. cbn in *.
  destruct A as [A algA]; simpl in *.
  destruct A; simpl in *; try exact (fun _ => tt).
  exact algA. 
Defined. 

Definition box : El (Πᶫ (A : El Typeᶫ), A →ᶫ Box A).
Proof.
  intros A. cbn in *.
  destruct A as [A algA]; simpl in *.
  destruct A; simpl in *; try exact (fun _ => ret tt).
  exact ret.
Defined. 

Definition div2_aux : (M nat -> M nat) -> M nat -> M (M nat).
Proof.
  intros f m.
  (* apply (box natᶫ). *)
  refine (map ret _).
  refine (bind m _); clear m; intro m. destruct m.
  - exact (ret 0).
  - destruct m. 
    + exact (ret 0).
    + exact (sucᶫ (f (ret m))). 
Defined. 

Definition div2 : El (natᶫ →ᶫ natᶫ).
Proof.
  refine (fixp2 _ _ _). simpl. refine div2_aux.
Defined.

Check (eq_refl _ : eval 15 (div2 (ret 23)) = Some 11).

