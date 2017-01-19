Require Import Effects.
Require Import delay.Eff.

Set Universe Polymorphism.

Fixpoint eval (n:nat) {A} {struct n} : M A -> option A.
Proof. 
  intros x. destruct x as [a | x].
  - exact (Some a).
  - destruct n.
    + exact None.
    + exact (eval n _ x).
Defined.

Declare Effect delay.Eff.

Effect Definition foo : Type using delay.Eff. 

(* Inductive bool : Type :=  true : bool | false : bool. *)
                                           
(* Effect Translate unit using delay.Eff. *)

Effect Definition bool : Type using delay.Eff.
Proof. 
  refine (ret (exist _ _ (M bool) _)).
  refine (fun b => bind b (fun b => b)).
Defined.

Inductive Paths {A : Type} (x : A) : A -> Type :=  id_path : Paths x x.

(* Effect Translate Paths using delay.Eff. *)

Effect Definition eq : forall (A : Type) (x : A), A -> Type using delay.Eff.
Proof.
  intros A x y.
  refine (ret (exist _ _ (M (Paths x y)) _)).
  refine (fun b => bind b (fun b => b)).
Defined.

(* Definition eq_reflᶫ : El (Πᶫ (A : El Typeᶫ) (x:El A), eqᶫ A x x) *)
(*   := fun A x => ret (id_path x). *)

(* Definition eq_caseᶫ (A : TYPE) (a : El A) (P : TYPE) (p : El P) *)
(*            (y : El A) (e : El (eqᶫ A a y)) : El P  := *)
(*   hbind e (fun e => match e with id_paths => p end). *)

(* Check (eq_refl : (fun A a P p => eq_caseᶫ A a P p a (eq_reflᶫ A a)) = (fun A a P p => p)). *)

(* Definition eq_recᶫ (A : TYPE) (a : El A) (P : El A -> TYPE) (p : El (P a)) *)
(*            (y : El A) (e : El (eqᶫ A a y)) : El (eq_caseᶫ A a Typeᶫ (P a) y e). *)
(* unfold eq_caseᶫ, hbind. *)
(* destruct e as [e|e]; cbn in *. *)
(* + exact p. *)
(* + unfold El. cbn. *)
(*   unfold hlist, pointwise, bind; cbn. *)
(*   destruct e as [e|e]; cbn in *. *)
(*   - destruct e. exact p. *)
(*   - exact tt.  *)
(* Defined. *)

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

(* Definition bisim {A} (x y : M A) : Type := (x ⊑ y) * (y ⊑ x). *)

(* CoFixpoint incl_equiv {A} (x y : M A) : (forall b, Value x b -> Value y b) -> x ⊑ y.  *)
(* Proof. *)
(*   intro e. destruct x. *)
(*   - exact (le_value (ret a) y a (value_return a) (e a (value_return a))).  *)
(*   - refine (le_lstep _ _ _). refine (incl_equiv _ _ _ _). *)
(*     intros b v. exact (e b (value_step _ _ v)).  *)
(* Defined. *)


(* CoInductive strong_bisim {A} : M A -> M A -> Type := *)
(*   sb_value : forall (a:A) , strong_bisim (ret a) (ret a) *)
(* | sb_step : forall (x y : M A), strong_bisim x y -> strong_bisim (step x) (step y). *)

(* Fixpoint bisim_n {A} n (x y : M A) : Type := *)
(*   match n with 0 => match x , y with ret a , ret b => a = b *)
(*                                | step _ , step _ => True *)
(*                                | _ , _ => False *)
(*                    end *)
(*           | S n => match x , y with step x , step y => bisim_n n x y *)
(*                                | _ , _ => False *)
(*                   end *)
(*   end. *)

Effect Definition later : forall (A : Type), A -> A using delay.Eff.
Proof. 
  intros A x. cbn in *. compute. 
  destruct A as [A | A]. 
  - apply A.(prf). exact (step (ret x)).
  - exact tt.
Defined. 

Effect Definition Box : Type -> Type using delay.Eff. 
Proof.
  intro T. 
  refine (ret (exist _ _ (M (El T).(wit)) _)).
  refine (fun b => bind b (fun b => b)).
Defined.

Effect Definition fixp2 : forall (A B : Type), ((A -> B) -> (A -> Box B)) -> (A -> B) using delay.Eff.
Proof.
  intros A B f x. cbn in *.
  destruct B as [B | B] ; simpl in *; try exact tt.
  apply B.(prf). generalize dependent x. refine (Y2 _).
  intros g x. exact (f (fun x => B.(prf) (g x)) x). 
Defined.

(* Definition fixp : El (Πᶫ (A : El Typeᶫ), (A →ᶫ Box A) →ᶫ A). *)
(* Proof. *)
(*   intros A f. cbn in *. *)
(*   destruct A as [A algA]; simpl in *. *)
(*   destruct A; simpl in *; try exact tt. *)
(*   apply algA. refine (Y _). *)
(*   intros x. exact (f (algA x)).  *)
(* Defined. *)

Effect Definition nat : Type using delay.Eff.
Proof.
  refine (ret (exist _ _ (M nat) _)).
  refine (fun b => bind b (fun b => b)).
Defined.

Effect Definition zero : nat using delay.Eff.
Proof. 
  refine (ret 0).
Defined.

Effect Definition suc : nat -> nat using delay.Eff.
Proof. 
  refine (map S).
Defined.

Effect Definition nat_rec :  forall A :Type,
       A ->
       (forall n : nat, A -> A) ->
       forall n : nat, A using delay.Eff. 
Proof.
  cbn. intros P P0 PS n. refine (hbind n _).
  clear n; intro n. induction n.
  - exact P0.
  - exact (PS (ret n) IHn).
Defined.

(* Effect Definition nat_rec :  forall P : nat -> Type, *)
(*        P zero -> *)
(*        (forall n : nat, P n -> P (suc n)) -> *)
(*        forall n : nat, P n using delay.Eff.  *)
(* Proof.  *)
(*   cbn. intros P P0 PS n. destruct n. induction n.  *)
(*   - exact P0. *)
(*   - pose (PS _ IHn). cbn in *. unfold sucᵉ in *. cbn  in w.  *)
  
Effect Definition unbox : forall (A : Type), Box A -> A using delay.Eff.
Proof.
  intros A. cbn in *.
  destruct A as [A | A]; simpl in *; try exact (fun _ => tt).
  exact A.(prf). 
Defined. 

Effect Definition box : forall (A : Type), A -> Box A using delay.Eff.
Proof.
  intros A. cbn in *.
  destruct A as [A | A]; simpl in *; try exact (fun _ => ret tt).
  exact ret.
Defined. 

Effect Definition base_box : nat -> Box nat using delay.Eff.
Proof. 
  refine (map ret).
Defined.
  
Definition div2_aux : (nat -> nat) -> nat -> Box nat.
Proof.
  intros f m. apply base_box.
  refine (nat_rec _ _ _ m); clear m. 
  - exact zero.
  - intros m Hm. refine (nat_rec _ _ _ m); clear m.
    + exact zero. 
    + intros m Hm'. exact (suc (f m)).
Defined.

Definition div2 : nat -> nat.
Proof.
  refine (fixp2 _ _ _). refine div2_aux.
Defined.

Effect Translate div2_aux using delay.Eff.

Effect Translate div2 using delay.Eff.

Effect Definition option : Type -> Type using delay.Eff.
Proof.
  refine (fun A => bind A _). clear A; intro A. 
  refine (ret (exist _ _ (M (option A.(wit))) _)).
  refine (fun b => bind b (fun b => b)).
Defined.

Effect Definition some : forall A, A -> option A using delay.Eff.
Proof.
  cbn. intros A x. destruct A as [A | A ]; cbn. 
  - exact (ret (Some x)).
  - exact tt.
Defined.

Effect Definition evalM : nat -> option nat using delay.Eff. 
Proof. 
  cbn. intros n. 
  refine (ret (option_map ret (eval 1000 n))).
Defined.

Effect Definition eq_div2 : eq _ (evalM (div2 (suc (suc (suc (suc (suc zero))))))) (evalM (suc (suc zero))) using delay.Eff.
Proof. compute. refine (ret (id_path _)).
Defined.




