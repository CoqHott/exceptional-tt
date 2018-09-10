
Require Import Weakly.Effects.


(** Here we are going to give a detailed explenation of how the new 
    exceptional translation works. *)

(** First of all, it is important to nat that the translation behave 
    differently when translating elements in Prop or elements in Type *)

(** Prop is interpreted as (TypeVal Prop (fun _ => True)), while 
    Type is interpreted as (TypeVale type TypeErr). This can 
    be seen in the type of a simple translation *)

(** Keep in mind that:
      Propᵉ = TypeVal Prop (fun _ => True)
      Typeᵉ = TypeVal type TypeErr 
    
    and that: 
      El (TypeVal v e) = v
*)

Definition TypeDifference : Prop -> Type -> Type := fun _ _ => Type.
Effect Translate TypeDifference. Check TypeDifferenceᵉ. 
(* forall E : Type, El (Propᵉ E) -> El Typeᵉ -> El Typeᵉ =
   forall E : Type, Prop -> type E -> El Typeᵉ *)

(** This means that is not possible to raise exceptions on
    Prop. These elements do not know how. *)

(** As a consequence, the translation of inductives is also 
    different. For Types, it adds a default exceptional constructor
    while for Prop it does not. *)

(** The name of the new exceptional Inductive is $INDUCTIVEᵒ *)

Effect Translate nat. Print natᵒ.
(* 
   Inductive natᵒ (E : Type) : Type :=  
   | Oᵉ : natᵒ E 
   | Sᵉ : natᵒ E -> natᵒ E 
   | natᴱ : E -> natᵒ E
*)

Effect Translate eq. Print eqᵒ.
(* 
   Inductive eqᵒ (E : Type) (A : El Typeᵉ) (x : El A) : El A -> Prop :=  
   | eq_reflᵉ : eqᵒ E A x x    
 *)

(** Here we can see how the translation adds a new constructor
    for the inductives in Type, while for inductives on Prop
    only add the exceptional layer over the terms/arguments/indices *)

(** It is also important that in the case that the inductive lives in 
    the Type hierarchy, the translation generates a parametric inductive
    and an instance for a parametric modality which in practice can be 
    used to enforce the purity of the exceptional term *)

(** The name of the parametric inductive is $INDUCTIVE_param and the 
    name of the parametric modality is 
    $INDUCTIVE_instance *)

(** Here the parametric modality has the form of:
      Class ParamMod (A: Type) := {
        param := A -> Prop
      }
     
   It is also important to note that this class is a primitive
   record, which enables the translation of the param operator
   as intended
*)

Print nat_param.
(*
  Inductive nat_param (E : Type) : natᵒ E -> Prop :=
    | O_param : nat_param E (Oᵉ E) 
    | S_param : forall H : natᵒ E, nat_param E H -> nat_param E (Sᵉ E H)
 *)

Print nat_instance.
(* nat_instance: AXIOM -> ParamMod nat *)

(** We actually need the instance for the parametric modality in the target
    theory but also in the source theory. However, is not possible to enforce that 
    the term is pure in the source theory, so the instance is an axiom in order
    to mantain consistency (?). 
    Here we can see that the modality does what we want in the target theory *)

Print nat_instanceᵉ.
(* nat_instanceᵉ = fun E : Type => {| paramᵉ := fun H : natᵒ E => nat_param E H |} *)

(** When applying the translation, nat_instance is mapped to nat_instanceᵉ, thus
    enforcing the purity of the term in the target theory *)

(** Note that the generated instances are declared instances of the modality class
    automatically *)

(** Note that is sufficient to make the source term an instance of the modality *)

Effect List Translate True list bool.
Print list_param.
(*
  Inductive list_param (E : Type) (A : El Typeᵉ) : listᵒ E A -> Prop :=
  | nil_param : list_param E A (nilᵉ E A)
  | cons_param : forall (H : El A) (H0 : listᵒ E A), list_param E A H0 -> list_param E A (consᵉ E A H H0)
 *)

(** It is important to note that the generated parametric inductive is a shallow parametricity *)

Inductive DeepInductive : Type :=
| def: DeepInductive
| deep: (Type -> DeepInductive) -> DeepInductive.

Effect Translate DeepInductive.
Print DeepInductive_param.
(*
  Inductive DeepInductive_param (E : Type) : DeepInductiveᵒ E -> Prop :=  
  | def_param : DeepInductive_param E (defᵉ E)
  | deep_param : forall H : El Typeᵉ -> DeepInductiveᵒ E, DeepInductive_param E (deepᵉ E H)
*)

(* The translation also support the mutual inductive definitions *)

Inductive even: nat -> Type :=
| evenZ: even 0
| evenS: forall n, odd n -> even (S n)
with odd: nat -> Type :=
| oddS: forall n, even n -> odd (S n).

Effect Translate even.
Print even_param.
(*
  Inductive even_param (E : Type) : forall H : natᵒ E, evenᵒ E H -> Prop :=
  | evenZ_param : even_param E (Oᵉ E) (evenZᵉ E)    
  | evenS_param : forall (n : natᵒ E) (H : oddᵒ E n), odd_param E n H -> even_param E (Sᵉ E n) (evenSᵉ E n H)
  with odd_param (E : Type) : forall H : natᵒ E, oddᵒ E H -> Prop :=
  | oddS_param : forall (n : natᵒ E) (H : evenᵒ E n), even_param E n H -> odd_param E (Sᵉ E n) (oddSᵉ E n H)
*)
Print even_instanceᵉ. (* Print odd_instance *)
(* even_pinstance_0 = fun (E : Type) (H : natᵒ E) => {| paramᵉ := fun H0 : evenᵒ E H => even_param E H H0 |} *)

(* The generated parametric inductive in this case is something to look at.
   Currently, it ask for the parametricity proof of the other inductive, although
   it can be relaxed *)

Definition param_translation_example: forall (n: nat), param n -> Type := fun _ _ => Type.
Effect Translate param_translation_example.

(** Enabling the print of implicits gives *)
Set Printing Implicit.
Check param_translation_exampleᵉ.
(* param_translation_exampleᵉ
     : forall (E : Type) (n : natᵒ E), @paramᵉ _ _ (nat_pinstance_0 E) n -> @El E (@Typeᵉ E) *)

(** That's all for the moment folks! *)
Unset Printing Implicit.

Effect Translate False.
Effect Translate not.

Effect Definition Exception : Type.
Proof.
  exact (fun E : Type => TypeVal E E (@id E)).
Defined. 

Effect Definition raise : forall A, Exception -> A.
Proof.
  exact (fun (E:Type) (A : type E) => Err A).
Defined. 

Arguments raise [A] _.

Effect Definition catch_bool : forall (P : bool -> Type), P true -> P false -> (forall e, P (raise e)) -> forall b, P b.
Proof.
  intros Exc P Pt Pf Perr b. destruct b.
  - exact Pt.
  - exact Pf.
  - exact (Perr e).
Defined.

Effect Definition catch_bool_Prop : forall (P : bool -> Prop), P true -> P false -> (forall e, P (raise e)) -> forall b, P b.
Proof.
  intros Exc P Pt Pf Perr b. destruct b.
  - exact Pt.
  - exact Pf.
  - exact (Perr e).
Defined.

Effect Translate bool_rect.

(* Fail because it requires it parametricity proof *)
Fail Effect Translate bool_ind.

(* explain how param works on nat *)

Effect Definition param_bool_true : param true.
Proof.
  econstructor. 
Defined. 

Effect Definition param_bool_false : param false.
Proof.
  econstructor. 
Defined. 

Effect Definition param_bool_raise : forall (e:Exception), param (@raise bool e) -> False.
Proof.
  intros E e H. inversion H. 
Defined. 

(* Define specific eliminations: parametric for Prop, default raise for Type *)

Definition bool_ind : forall (P : bool -> Prop) (Pt : P true) (Pf : P false) (b:bool), param b -> P b.
Proof.
  intros P Pt Pf b. induction b using catch_bool_Prop; intros H; auto.
  - destruct (param_bool_raise e H).
Defined.

Effect Translate bool_ind. 
 
(* correctness of param for bool *)

Effect Definition raise_nottrue : forall (e:Exception), true <> raise e.
Proof.
  compute; intros. inversion H.
Defined. 

Effect Definition raise_notfalse : forall (e:Exception), false <> raise e.
Proof.
  compute; intros. inversion H.
Defined. 

Definition param_correct_bool (b:bool) : param b -> forall e, b <> raise e.
  intro H. refine (bool_ind (fun b => forall e : Exception, b <> raise e) _ _ b H).
  - exact raise_nottrue. 
  - exact raise_notfalse. 
Defined.

Effect Translate param_correct_bool. 

(* Define catch eliminator on Prop and Type *)

Scheme natᵒ_rect := Induction for natᵒ Sort Type.
Scheme natᵒ_ind := Induction for natᵒ Sort Prop.

Effect Definition catch_nat : forall (P : nat -> Type) (P0 : P 0) (PS : forall n, P n -> P (S n)) (Praise : forall e, P (raise e)) (n:nat), P n.
Proof.
  intros Exc P P0 PS Perr n. induction n.
  - exact P0.
  - apply PS. auto. 
  - exact (Perr e).
Defined.

Effect Definition catch_nat_Prop : forall (P : nat -> Prop) (P0 : P 0) (PS : forall n, P n -> P (S n)) (Praise : forall e, P (raise e)) (n:nat), P n.
Proof.
  intros Exc P P0 PS Perr n. induction n.
  - exact P0.
  - apply PS. auto. 
  - exact (Perr e).
Defined.

(* explain how param works on nat *)

Effect Definition param_nat_0 : param 0.
Proof.
  econstructor. 
Defined. 
 
Effect Definition param_nat_S : forall n, param (S n) -> param n.
Proof.
  intros. inversion H. exact H1. 
Defined. 

Effect Definition param_nat_raise : forall (e:Exception), param (@raise nat e) -> False.
Proof.
  intros E e H. inversion H. 
Defined. 

(* Define specific eliminations: parametric for Prop, default raise for Type *)

(* Fail because it requires it parametricity proof *)
Fail Effect Translate nat_ind.

Definition nat_ind : forall (P : nat -> Prop) (P0 : P 0) (PS : forall n, P n -> P (S n)) (n:nat), param n -> P n.
Proof.
  intros P P0 PS n. induction n using catch_nat_Prop; auto. 
  - intros HS. apply PS. apply IHn. exact (param_nat_S _ HS).
  - intros H. destruct (param_nat_raise e H).
Defined.

Effect Translate nat_ind.
Effect Translate nat_rect.
  
(* correctness of param for nat *)

Effect Definition raise_not0 : forall (e:Exception), 0 <> raise e.
Proof.
  compute; intros. inversion H.
Defined. 

Effect Definition raise_notS : forall (e:Exception) n, S n <> raise e.
Proof.
  compute; intros. inversion H.
Defined. 

Definition param_correct_nat (n:nat) : param n -> forall e, n <> raise e.
  intro H. refine (nat_ind (fun n => forall e : Exception, n <> raise e) _ _ n H).
  - exact raise_not0. 
  - clear; intros n H e. exact (raise_notS e n).
Defined.

Effect Translate param_correct_nat. 

(* dummy test *)

Definition bar e : { n:nat & n = raise e} := existT _ (raise e) eq_refl.


(* Define catch eliminator on Prop and Type *)

Scheme listᵒ_rect := Induction for listᵒ Sort Type.
Scheme listᵒ_ind := Induction for listᵒ Sort Prop.

Effect Definition catch_list : forall A (P : list A -> Type) (Pnil : P nil) (Pcons : forall (a:A) l , P l -> P (a :: l)%list) (Praise : forall e, P (raise e)) (l:list A), P l.
Proof.
  intros Exc A P Pnil Pcons Perr l. induction l.
  - exact Pnil.
  - apply Pcons. auto. 
  - exact (Perr e).
Defined.

Effect Definition catch_list_Prop : forall A (P : list A -> Prop) (Pnil : P nil) (Pcons : forall (a:A) l , P l -> P (a :: l)%list) (Praise : forall e, P (raise e)) (l:list A), P l.
Proof.
  intros Exc A P Pnil Pcons Perr l. induction l.
  - exact Pnil.
  - apply Pcons. auto. 
  - exact (Perr e).
Defined.

(* explain how param works on nat *)

Effect Definition param_list_nil : forall A, param (@nil A).
Proof.
  econstructor. 
Defined. 
 
Effect Definition param_list_cons : forall A a (l:list A), param (cons a l) -> param l.
Proof.
  intros. inversion H. exact H1. 
Defined. 

Effect Definition param_list_raise : forall (e:Exception) A, param (@raise (list A) e) -> False.
Proof.
  intros E A e H. inversion H. 
Defined. 

(* Define specific eliminations: parametric for Prop, default raise for Type *)

(* Fail because it requires it parametricity proof *)
Fail Effect Translate list_ind.

Definition list_ind : forall A (P : list A -> Prop) (Pnil : P nil) (PS : forall a l, P l -> P (cons a l)) l, param l -> P l.
Proof.
  intros A P Pnil Pcons l. induction l using catch_list_Prop; auto. 
  - intros Hcons. apply Pcons. apply IHl. exact (param_list_cons _ _ _ Hcons).
  - intros H. destruct (param_list_raise e A H).
Defined.

Effect Translate list_ind.
Effect Translate list_rect.
  
(* correctness of param for nat *)

Effect Definition raise_notnil : forall A (e:Exception), (@nil A) <> raise e.
Proof.
  compute; intros. inversion H.
Defined. 

Effect Definition raise_notcons : forall A (e:Exception) a (l:list A), cons a l <> raise e.
Proof.
  compute; intros. inversion H.
Defined. 

Definition param_correct_list A (l:list A) : param l -> forall e, l <> raise e.
  intro H. refine (list_ind A (fun l => forall e : Exception, l <> raise e) _ _ l H).
  - exact (raise_notnil A). 
  - clear; intros a l H e. exact (raise_notcons A e a l).
Defined.

Effect Translate param_correct_list. 

