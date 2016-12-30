# Writer-like effects in Coq

This plugin allows to easily apply an effectful translation to CIC terms.
The translation is generic over the effect, provided it complies with a few
requirements, that turn it into what we call a writer-like pseudo-monad (WLPM).

A WLPM is described by the following terms:
- `M : Type@{i} -> Type@{i}`
- `ret : forall A : Type, A -> M A`
- `bind : forall (A B : Type), M A -> (A -> M B) -> M B`
- `pointwise : forall (A : Type), (A -> Type) -> M A -> Type`
- `hbind : forall (A : Type) (B : TYPE), M A -> (A -> El B) -> El B`

where the following data is derived as:
- `TYPE := M {A : Type & M A -> A}`
- `El (A : TYPE) := pointwise proj1 A`

The terms must satisfy a few definitional equations, namely:
- `bind A B (ret A t) f ≡ f t`
- `pointwise A P (ret A t) ≡ P t`
- `hbind A B (ret A t) f ≡ f t`

# Compilation

This requires Coq 8.6. If the `COQBIN` variable is correctly set, a `make`
invokation should be enough.

# Use of the plugin

An effect is described by any module `EFF` containing the above definitions. It
must first be declared using the following command:

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

The repository contains a few examples of WLPM, some as effects, other
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
