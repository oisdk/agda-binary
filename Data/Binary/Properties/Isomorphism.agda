{-# OPTIONS --cubical #-}

module Data.Binary.Properties.Isomorphism where

open import Data.Binary.Definition
open import Data.Binary.Conversion
open import Data.Binary.Increment
open import Data.Binary.Properties.Helpers
open import Data.Binary.Helpers
import Agda.Builtin.Nat as ℕ

inc-suc : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-suc 0ᵇ     = refl
inc-suc (1ᵇ x) = refl
inc-suc (2ᵇ x) = cong (λ r → suc (r ℕ.* 2)) (inc-suc x)

inc-2*-1ᵇ : ∀ n → inc ⟦ n ℕ.* 2 ⇑⟧ ≡ 1ᵇ ⟦ n ⇑⟧
inc-2*-1ᵇ zero    = refl
inc-2*-1ᵇ (suc n) = cong (λ r → inc (inc r)) (inc-2*-1ᵇ n)

ℕ→𝔹→ℕ : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
ℕ→𝔹→ℕ zero    = refl
ℕ→𝔹→ℕ (suc x) = inc-suc ⟦ x ⇑⟧ ∙ cong suc (ℕ→𝔹→ℕ x)

𝔹→ℕ→𝔹 : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝔹→ℕ→𝔹 0ᵇ = refl
𝔹→ℕ→𝔹 (1ᵇ x) =           inc-2*-1ᵇ ⟦ x ⇓⟧  ∙ cong 1ᵇ_ (𝔹→ℕ→𝔹 x)
𝔹→ℕ→𝔹 (2ᵇ x) = cong inc (inc-2*-1ᵇ ⟦ x ⇓⟧) ∙ cong 2ᵇ_ (𝔹→ℕ→𝔹 x)

𝔹⇔ℕ : Iso 𝔹 ℕ
𝔹⇔ℕ .fun = ⟦_⇓⟧
𝔹⇔ℕ .inv = ⟦_⇑⟧
𝔹⇔ℕ .rightInv = ℕ→𝔹→ℕ
𝔹⇔ℕ .leftInv  = 𝔹→ℕ→𝔹
