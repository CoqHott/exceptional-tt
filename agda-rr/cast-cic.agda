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

postulate cast-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (A' : Set ℓ₂) (B' : A' → Set ℓ₃) (x : A) (y : B x) →
                       cast (Σ A B) (Σ A' B') (x , y) ≡ (cast {ℓ = ℓ} {ℓ₁ = ℓ₂} A A' x , cast (B x) (B' (cast A A' x)) y)

{-# REWRITE cast-Sigma #-}

postulate cast-Sum-inj₁ : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) →
                    cast (A ⊎ B) (A' ⊎ B') (inj₁ a) ≡ inj₁ (cast A A' a)

postulate cast-Sum-inj₂ : (A A' : Set ℓ) (B B' : Set ℓ₁) (b : B) →
                    cast (A ⊎ B) (A' ⊎ B') (inj₂ b) ≡ inj₂ (cast B B' b)

{-# REWRITE cast-Sum-inj₁ #-}
{-# REWRITE cast-Sum-inj₂ #-}

postulate cast-List-nil : (A A' : Set ℓ) →
                          cast (List A) (List A') [] ≡ []

postulate cast-List-cons : (A A' : Set ℓ) (a : A) (l : List {a = ℓ} A) →
                           cast (List A) (List {a = ℓ} A') (a ∷ l) ≡
                           cast A A' a ∷ cast (List A) (List A') l

{-# REWRITE cast-List-nil #-}

{-# REWRITE cast-List-cons #-}

postulate cast-Nat-zero : cast Nat Nat 0 ≡ 0

postulate cast-Nat-suc : (n : Nat ) → cast Nat Nat (suc n) ≡ suc (cast _ _ n)

{-# REWRITE cast-Nat-zero #-}

{-# REWRITE cast-Nat-suc #-}

postulate cast-Bool-true : cast Bool Bool true ≡ true

{-# REWRITE cast-Bool-true #-}

postulate cast-Bool-false : cast Bool Bool false ≡ false

{-# REWRITE cast-Bool-false #-}

postulate cast-Unit : cast ⊤ ⊤ tt ≡ tt

{-# REWRITE cast-Unit #-}

{- non-diagonal cases -}

postulate cast-Set-bad : (A : Set (lsuc ℓ)) → cast (Set (lsuc ℓ)) (Set ℓ) A ≡ raise _

{-# REWRITE cast-Set-bad #-}

postulate cast-raise :  ∀ ℓ ℓ₁ → (A : Set ℓ₁) → cast (raise {ℓ = lsuc ℓ} (Set ℓ)) A (raise _) ≡ raise _

{-# REWRITE cast-raise #-}


postulate cast-Pi-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a)  →
                    cast ((a : A) → B a) (Σ {a = ℓ} {b = ℓ₁} A' B') f ≡ raise (Σ A' B')

{-# REWRITE cast-Pi-Sigma #-}

postulate cast-Pi-Nat : (A : Set ℓ) (B : A → Set ℓ₁) (f : (a : A) → B a) →
                    cast ((a : A) → B a) Nat f ≡ raise Nat

{-# REWRITE cast-Pi-Nat #-}

{- Rules specific to Unk -}

postulate cast-Pi-Unk : (A : Set ℓ) (B : A → Set ℓ₁) (f : ((a : A) → B a)) →
                        cast ((a : A) → B a) (Unk (ℓ ⊔ ℓ₁)) f ≡ box ((a : A) → B a) f

postulate cast-Unk : (A : Set ℓ) (B : Set ℓ₁) (f : A) →
                        cast (Unk ℓ) B (box A f) ≡ cast A B f

postulate cast-Pi-Unk-bad : (f : Unk ℓ → Unk ℓ₁) →
                            cast (Unk ℓ → Unk ℓ₁) (Unk (ℓ ⊔ ℓ₁)) f ≡ raise _

{-# REWRITE cast-Pi-Unk cast-Unk cast-Pi-Unk-bad #-}

postulate cast-Sigma-Unk : (A : Set ℓ) (B : A → Set ℓ₁) (x : Σ {a = ℓ} {b = ℓ₁} A B) →
                        cast (Σ A B) (Unk _) x ≡ box (Σ A B) x

{-# REWRITE cast-Sigma-Unk #-}

proj : {A : Set ℓ₁} → Unk ℓ → A
proj {ℓ₁} {ℓ} {A} (box A' a') = cast {ℓ = ℓ} {ℓ₁ = ℓ₁} A' A a' 

delta : Unk ℓ → Unk ℓ
delta {ℓ} x = proj {A = Unk ℓ → Unk ℓ} x x

omega : Unk (lsuc ℓ)
omega {ℓ} = delta {ℓ = lsuc ℓ} (box (Unk ℓ → Unk ℓ) (delta {ℓ = ℓ}))

