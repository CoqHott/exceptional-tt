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

variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

record Top ℓ : Set ℓ where
  constructor ⟨⟩


{- 
 Axiomatisation of ExTT
-}

postulate raise : (A : Set ℓ) → A

-- we now state rewrite rules for raise

postulate raise-Pi : (A : Set ℓ) (B : A → Set ℓ₁) →
                     raise ((a : A) → B a) ≡ λ a → raise (B a)

{-# REWRITE raise-Pi #-}

postulate raise-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) →
                     raise (Σ A B) ≡ (raise A , raise (B (raise A)))

{-# REWRITE raise-Sigma #-}

nat-rec : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) → (n : Nat) → P n 
nat-rec P P0 PS zero = P0
nat-rec P P0 PS (suc n) = PS n (nat-rec P P0 PS n)

postulate raise-nat-rec : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                          nat-rec P P0 PS (raise Nat) ≡ raise (P (raise Nat))
                
{-# REWRITE raise-nat-rec #-}

postulate catch-nat : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                      (Praise : P (raise Nat)) → (n : Nat) → P n 

postulate catch-nat-zero : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                           (Praise : P (raise Nat)) → catch-nat P P0 PS Praise 0 ≡ P0

postulate catch-nat-suc : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                          (Praise : P (raise Nat)) → (n : Nat) →
                          catch-nat P P0 PS Praise (suc n) ≡ PS n (catch-nat P P0 PS Praise n)

postulate catch-nat-raise : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                            (Praise : P (raise Nat)) → catch-nat P P0 PS Praise (raise Nat) ≡ Praise

{-# REWRITE catch-nat-zero #-}
{-# REWRITE catch-nat-suc #-}
{-# REWRITE catch-nat-raise #-}

postulate raise-Top : raise (Top ℓ) ≡ ⟨⟩

{-# REWRITE raise-Top #-}

postulate raise-Set : raise (Set ℓ) ≡ Top ℓ

{-# REWRITE raise-Set #-}




{- 
 Axiomatisation of unk
-}

postulate unk : (A : Set ℓ) → A

-- we now state rewrite rules for unk

postulate unk-Pi : (A : Set ℓ) (B : A → Set ℓ₁) →
                     unk ((a : A) → B a) ≡ λ a → unk (B a)

{-# REWRITE unk-Pi #-}

postulate unk-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) →
                     unk (Σ A B) ≡ (unk A , unk (B (unk A)))

{-# REWRITE unk-Sigma #-}

postulate unk-nat-rec : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                          nat-rec P P0 PS (unk Nat) ≡ unk (P (unk Nat))
                
{-# REWRITE unk-nat-rec #-}

postulate catch-unk-nat : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                      (Punk : P (unk Nat)) → (n : Nat) → P n 

postulate catch-unk-nat-zero : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                           (Punk : P (unk Nat)) → catch-unk-nat P P0 PS Punk 0 ≡ P0

postulate catch-unk-nat-suc : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                          (Punk : P (unk Nat)) → (n : Nat) →
                          catch-unk-nat P P0 PS Punk (suc n) ≡ PS n (catch-unk-nat P P0 PS Punk n)

postulate catch-unk-nat-unk : (P : Nat → Set ℓ) (P0 : P 0) (PS : (n : Nat) → P n → P (suc n)) →
                            (Punk : P (unk Nat)) → catch-unk-nat P P0 PS Punk (unk Nat) ≡ Punk

{-# REWRITE catch-unk-nat-zero #-}
{-# REWRITE catch-unk-nat-suc #-}
{-# REWRITE catch-unk-nat-unk #-}

postulate unk-Top : unk (Top ℓ) ≡ ⟨⟩

{-# REWRITE unk-Top #-}

Unk : ∀ ℓ → Set ℓ
Unk ℓ = unk (Set ℓ)

-- postulate Unk : ∀ ℓ → Set (lsuc ℓ)
-- -- record Unk ℓ : Set (lsuc ℓ) where
-- --   constructor box
-- --   field
-- --     type : Set ℓ
-- --     elem : type

-- postulate raise-Unk :  ∀ ℓ → raise (Unk ℓ) ≡ box (raise (Set ℓ)) (raise _)

-- {-# REWRITE raise-Unk #-}

