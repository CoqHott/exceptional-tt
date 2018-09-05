
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
    Typeᵉ = TypeVal type TypeErr *)

Definition TypeDifference : Prop -> Type -> Type := fun _ _ => Type.
Effect Translate TypeDifference. Check TypeDifferenceᵉ. 
(* forall E : Type, El (Propᵉ E) -> El Typeᵉ -> El Typeᵉ =
   forall E : Type, Prop -> type E -> El Typeᵉ *)

(** This means that is not possible to raise exceptions on
    Prop. These elements do not know how. *)

(** This means that the translation of inductives is also 
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
    only add the exceptional layer over the terms *)

(** It is also important that in the case that the inductive lives in 
    the Type hierarchy, the translation generates a parametric inductive
    and an instance for a parametric modality which in practice can be 
    used to enforce the purity of the exceptional term *)

(** The name of the parametric inductive is $INDUCTIVE_param and the 
    name of the parametric modality is 
    $INDUCTIVE_instance_$NUMBER_OF_INDUCTIVE_IN_BLOCK *)

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

Print nat_instance_0.
(* nat_instance_0 = {| param := fun _ : nat => True |} *)

(** We actually need the instance for the parametric modality in the target
    theory but also in the source theory. However, is not possible to enforce that 
    the term is pure in the source theory, so the instance is choosed degenerated. 
    Here we can see that the modality does what we want in the target theory *)

Print nat_pinstance_0.
(* nat_pinstance_0 = fun E : Type => {| paramᵉ := fun H : natᵒ E => nat_param E H |} *)

(** When applying the translation, nat_instance_0 is mapped to nat_pinstance_0, thus
    enforcing the purity of the term in the target theory *)

(** Currently, these terms are not made instance of the modality but can be declared 
    as such with *)

Existing Instance nat_instance_0.

(** Note that is sufficient to make the source term an instance of the modality *)

Effect List Translate list bool.
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
Print even_pinstance_0. (* Print even_instance_1 *)
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
