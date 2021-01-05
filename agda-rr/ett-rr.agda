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

record Unk ℓ : Set (lsuc ℓ) where
  constructor box
  field
    type : Set ℓ
    elem : type

postulate raise-Unk :  ∀ ℓ → raise (Unk ℓ) ≡ box (raise (Set ℓ)) (raise _)

{-# REWRITE raise-Unk #-}

