{-# OPTIONS --rewriting --prop --confluence-check --cumulativity  #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Data.Vec.Base
open import Data.Bool
open import Data.Sum
open import Data.Product using (_×_)
open import ett-rr

{- Axiomatisation of the Cast calculus -}

{- diagonal cases -}

postulate cast : (A : Set ℓ) (B : Set ℓ₁) → A → B

postulate cast-set : (A : Set ℓ) → cast (Set ℓ) (Set ℓ) A ≡ A

{-# REWRITE cast-set #-}

postulate cast-prop : (A : Prop ℓ) → cast (Prop ℓ) (Prop ℓ) A ≡ A

{-# REWRITE cast-prop #-}

postulate cast-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (A' : Set ℓ₂) (B' : A' → Set ℓ₃) (f : (a : A) → B a)  →
                    cast ((a : A) → B a) ((a' : A') → B' a') f ≡
                    λ (a' : A') → cast _ _ (f (cast A' A a'))

{-# REWRITE cast-Pi #-}

postulate cast-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (A' : Set ℓ₂) (B' : A' → Set ℓ₃) (p : Σ {a = ℓ} {b = ℓ₁} A B) →
                       cast (Σ A B) (Σ A' B') p ≡ (cast {ℓ = ℓ} {ℓ₁ = ℓ₂} A A' (p .fst) , cast (B (p .fst)) (B' (cast A A' (p .fst))) (p .snd))

{-# REWRITE cast-Sigma #-}

postulate cast-Sum-inj₁ : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) →
                    cast (A ⊎ B) (A' ⊎ B') (inj₁ a) ≡ inj₁ (cast A A' a)

postulate cast-Sum-inj₂ : (A A' : Set ℓ) (B B' : Set ℓ₁) (b : B) →
                    cast (A ⊎ B) (A' ⊎ B') (inj₂ b) ≡ inj₂ (cast B B' b)

postulate cast-Sum-raise : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) →
                    cast (A ⊎ B) (A' ⊎ B') (raise _) ≡ raise _

postulate cast-Sum-unk : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) →
                    cast (A ⊎ B) (A' ⊎ B') (unk _) ≡ unk _

{-# REWRITE cast-Sum-inj₁ #-}
{-# REWRITE cast-Sum-inj₂ cast-Sum-raise cast-Sum-unk #-}

postulate cast-List-nil : (A A' : Set ℓ) →
                          cast (List A) (List A') [] ≡ []

postulate cast-List-cons : (A A' : Set ℓ) (a : A) (l : List {a = ℓ} A) →
                           cast (List A) (List {a = ℓ} A') (a ∷ l) ≡
                           cast A A' a ∷ cast (List A) (List A') l

postulate cast-List-raise : (A A' : Set ℓ) →
                          cast (List A) (List A') (raise (List _)) ≡ raise (List _)
postulate cast-List-unk : (A A' : Set ℓ) →
                          cast (List A) (List A') (unk (List _)) ≡ unk (List _)

{-# REWRITE cast-List-nil #-}
{-# REWRITE cast-List-cons cast-List-raise cast-List-unk #-}

postulate cast-Nat-zero : cast Nat Nat 0 ≡ 0

postulate cast-Nat-suc : (n : Nat ) → cast Nat Nat (suc n) ≡ suc (cast _ _ n)

postulate cast-Nat-raise : cast Nat Nat (raise Nat) ≡ raise Nat

postulate cast-Nat-unk : cast Nat Nat (unk Nat) ≡ unk Nat

{-# REWRITE cast-Nat-zero cast-Nat-suc cast-Nat-raise cast-Nat-unk #-}

postulate cast-Bool-true : cast Bool Bool true ≡ true

postulate cast-Bool-false : cast Bool Bool false ≡ false

postulate cast-Bool-raise : cast Bool Bool (raise Bool) ≡ raise Bool
  
postulate cast-Bool-unk : cast Bool Bool (unk Bool) ≡ unk Bool

{-# REWRITE cast-Bool-true cast-Bool-false cast-Bool-raise cast-Bool-unk #-}

postulate cast-Unit : cast ⊤ ⊤ tt ≡ tt
{- Beware that raise ⊤ ≡ tt ≡ unk ⊤ because of definitional singleton -}
postulate cast-Unit-raise : cast ⊤ ⊤ (raise ⊤) ≡ raise ⊤
postulate cast-Unit-unk : cast ⊤ ⊤ (unk ⊤) ≡ unk ⊤

{-# REWRITE cast-Unit cast-Unit-raise cast-Unit-unk #-}

{- non-diagonal cases -}

postulate cast-Set-bad : (A : Set (lsuc ℓ)) → cast (Set (lsuc ℓ)) (Set ℓ) A ≡ raise _

{-# REWRITE cast-Set-bad #-}

postulate cast-raise :  ∀ ℓ ℓ₁ → (x : raise {ℓ = lsuc ℓ} (Set ℓ)) (A : Set ℓ₁) → cast (raise {ℓ = lsuc ℓ} (Set ℓ)) A x ≡ raise _

{-# REWRITE cast-raise #-}

postulate cast-Pi-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a)  →
                    cast ((a : A) → B a) (Σ {a = ℓ} {b = ℓ₁} A' B') f ≡ raise (Σ A' B')

{-# REWRITE cast-Pi-Sigma #-}

postulate cast-Pi-Nat : (A : Set ℓ) (B : A → Set ℓ₁) (f : (a : A) → B a) →
                    cast ((a : A) → B a) Nat f ≡ raise Nat

{-# REWRITE cast-Pi-Nat #-}

-- missing many conflict rules



{- Rules specific to Unk -}

{- unk-cast ℓ A a  is just a copy of  cast A (Unk ℓ) a
   but we need to split it off for rewriting.
   Making it private so that the only closed  values we can create in Unk ℓ come from cast -}
private
  postulate unk-cast : ∀ (A : Set ℓ) → A → Unk (lsuc ℓ)

postulate cast-Unk : (A : Set ℓ) (B : Set ℓ₁) (f : A) →
                        cast (Unk (lsuc ℓ)) B (unk-cast A f) ≡ cast A B f
{-# REWRITE cast-Unk #-}

postulate cast-Unk-raise : ∀ ℓ → (B : Set ℓ₁)  →
                           cast (Unk ℓ) B (raise _) ≡ raise _
{-# REWRITE cast-Unk-raise #-}

postulate cast-Pi-Unk : (A : Set ℓ) (B : A → Set ℓ₁) (f : ((a : A) → B a)) →
                        cast ((a : A) → B a) (Unk (lsuc (ℓ ⊔ ℓ₁))) f ≡  unk-cast (Unk ℓ → Unk ℓ₁) (cast ((a : A) → B a) (Unk ℓ → Unk ℓ₁) f)


{-# REWRITE cast-Pi-Unk #-}

postulate cast-Pi-Unk-bad : (f : Unk ℓ → Unk ℓ₁) →
                            cast (Unk ℓ → Unk ℓ₁) (Unk (ℓ ⊔ ℓ₁)) f ≡ raise _

{-# REWRITE cast-Pi-Unk-bad #-}

postulate cast-Sigma-Unk : (A : Set ℓ) (B : A → Set ℓ₁) (x : Σ {a = ℓ} {b = ℓ₁} A B) →
                        cast (Σ A B) (Unk (lsuc (ℓ ⊔ ℓ₁))) x ≡ unk-cast (_×_ {a = ℓ} {b = ℓ₁} (Unk ℓ) (Unk ℓ₁)) (cast (Σ A B) (Unk ℓ × Unk ℓ₁) x)

{-# REWRITE cast-Sigma-Unk #-}


delta : Unk ℓ → Unk ℓ
delta {ℓ} x = cast (Unk ℓ) (Unk ℓ → Unk ℓ) x x

omega : Unk ℓ
omega {ℓ} = delta {ℓ = ℓ} (cast (Unk ℓ → Unk ℓ) (Unk ℓ) (delta {ℓ = ℓ}))

