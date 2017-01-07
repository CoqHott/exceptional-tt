# Self-algebraic effects in Coq

This plugin allows to easily apply an effectful translation to CIC terms.
The translation is generic over the effect, provided it complies with a few
requirements, that turn it into what we call a self-algebraic pseudo-monad (SAPM).

A SAPM is described by the following terms:
- `M : Type@{i} -> Type@{i}`
- `ret : forall A : Type, A -> M A`
- `bind : forall (A B : Type), M A -> (A -> M B) -> M B`
- `El : M TYPE -> TYPE`
- `hbind : forall (A : Type) (B : TYPE), M A -> (A -> El B) -> El B`
- `pbind : foral (A : Type) (R : M TYPE) (B : A -> El (R  →ᵉ Typeᵉ))
    (l : M A) (r : El R) (f : forall x : A, El (B x r)), El (hbind A (R  →ᵉ Typeᵉ) l B r)`

where the following data is derived as:
- `TYPE := {A : Type & M A -> A}`

The terms must satisfy a few definitional equations, namely:
- `hbind A B (ret A t) f ≡ f t`
- `pbind A B (ret A t) f r ≡ f t r`

# Compilation

This requires Coq 8.6. If the `COQBIN` variable is correctly set, a `make`
invokation should be enough.

# Use of the plugin

An effect is described by any module `EFF` containing the above definitions,
plus the following constants:
- `Free : Type -> M TYPE := ret (exist Type (fun A => M A -> A) (M A) (fun x => bind x (fun x => x)))`
- `Typeᵉ : M TYPE := Free TYPE`
- `Prodᵉ : forall (A : M TYPE), (B : (El A).(wit) -> M TYPE) -> M TYPE := ...`

Ideally, these constants should be derived from the given self-algebraic structure,
but for now this is still a TODO.

Before being available, the effect must first be declared using the following
command:

```
Declare Effect EFF.
```

Aftewards, it can be used in two ways.
- Coq definitions can be automatically translated.
- New terms can by constructed through the translation.

The first case is covered by the command:
```
Effect Translate foo using EFF.
```
where `foo` is the global definition to translate. The command defines a new
constant `fooᵉ` whose type is the translated type of `foo`.

The second case is covered by the command:
```
Effect Definition foo : T using EFF.
```
which opens a proof whose goal is the translation of T. After the proof is
completed, an axiom `foo : T` is added to the environment, and a constant
`fooᵉ` is defined with the term given by the proof.

# Examples

The repository contains a few examples of SAPM, some as effects, other
handcoded.

## Exceptions (`M A ~ A + E`)

The underlying translation is a variant of Friedman's trick, except that it
scales to dependent type theory in a convoluted way. Obviously, the resulting
theory is inconsistent, but it allows to extract constructive data out of CIC
proofs. Most notably `[(A → ⊥) → ⊥] ∼ ([A] → E) → E`, which allows to reason
classically on the first-order fragment.

## Non-determinism (`M A ~ A × list A`)

I do not know any logical interpretation for that one.

## Unbounded fixpoints (`M A ~ νX. A + X`)

Nothing interesting yet.

## Writer (`M A ~ A × W`)

Nothing interesting yet.

# License

This software is licensed under the WTFPL 2.0.
