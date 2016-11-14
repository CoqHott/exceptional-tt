open Names
open Libnames
open ETranslate

type effect = reference

val translate : effect -> reference -> Id.t list option -> unit

val implement : effect -> Id.t -> Constrexpr.constr_expr -> Id.t option -> unit

val declare_effect : effect -> unit
(** Declare a new effect in the current module, by deriving the required data
    from the most basic blocs. The current environment must contain:
    1. M : Type -> Type
    2. ret : forall A : Type, A -> M A
    3. bind : forall (A B : Type), M A -> (A -> M B) -> M B
    4. pointwise : forall (A : Type), (A -> Type) -> M A -> Type
    5. hbind : forall (A : Type) (B : TYPE), M A -> (A -> El B) -> El B

    where the following data is defined on the fly:
      TYPE := M {A : Type & M A -> A}
      El (A : TYPE) := pointwise proj1 A
      Π (A : TYPE) (B : El A -> TYPE) : TYPE := ...
*)
