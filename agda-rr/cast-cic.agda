{-# OPTIONS --rewriting --prop --confluence-check #-}

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
open import ett-rr


{- Axiomatisation of the Cast calculus -}

{- diagonal cases -}

postulate cast : (A B : Set ℓ) → A → B

postulate cast-set : (A : Set ℓ) → cast (Set ℓ) (Set ℓ) A ≡ A

{-# REWRITE cast-set #-}

postulate cast-prop : (A : Prop ℓ) → cast (Prop ℓ) (Prop ℓ) A ≡ A

{-# REWRITE cast-prop #-}

postulate cast-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a)  →
                    cast ((a : A) → B a) ((a' : A') → B' a') f ≡
                    λ (a' : A') → cast _ _ (f (cast A' A a'))

{-# REWRITE cast-Pi #-}

postulate cast-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (x : A) (y : B x) →
                       cast (Σ A B) (Σ A' B') (x , y) ≡ (cast A A' x , cast (B x) (B' (cast A A' x)) y)

{-# REWRITE cast-Sigma #-}

postulate cast-Sum-inj₁ : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) →
                    cast (A ⊎ B) (A' ⊎ B') (inj₁ a) ≡ inj₁ (cast A A' a)

postulate cast-Sum-inj₂ : (A A' : Set ℓ) (B B' : Set ℓ₁) (b : B) →
                    cast (A ⊎ B) (A' ⊎ B') (inj₂ b) ≡ inj₂ (cast B B' b)


{-# REWRITE cast-Sum-inj₁ #-}
{-# REWRITE cast-Sum-inj₂ #-}

 
postulate cast-List-nil : (A A' : Set ℓ) →
                          cast (List A) (List A') [] ≡ []

postulate cast-List-cons : (A A' : Set ℓ) (a : A) (l : List A) →
                           cast (List A) (List A') (a ∷ l) ≡
                           cast A A' a ∷ cast _ _ l

{-# REWRITE cast-List-nil #-}

{-# REWRITE cast-List-cons #-}


postulate cast-Nat-zero : cast Nat Nat 0 ≡ 0

postulate cast-Nat-suc : (n : Nat ) →
                         cast Nat Nat (suc n) ≡ suc (cast _ _ n)

{-# REWRITE cast-Nat-zero #-}

{-# REWRITE cast-Nat-suc #-}

postulate cast-Bool-true : cast Bool Bool true ≡ true

{-# REWRITE cast-Bool-true #-}

postulate cast-Bool-false : cast Bool Bool false ≡ false

{-# REWRITE cast-Bool-false #-}

postulate cast-Unit : cast ⊤ ⊤ tt ≡ tt

{-# REWRITE cast-Unit #-}

{- non-diagonal cases -}

postulate cast-Pi-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a)  →
                    cast ((a : A) → B a) (Σ A' B') f ≡ raise (Σ A' B')

{-# REWRITE cast-Pi-Sigma #-}
