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

𝔹-rightInv : ∀ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ≡ x
𝔹-rightInv zero    = refl
𝔹-rightInv (suc x) = inc-suc ⟦ x ⇑⟧ ∙ cong suc (𝔹-rightInv x)

𝔹-leftInv : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
𝔹-leftInv 0ᵇ = refl
𝔹-leftInv (1ᵇ x) =           inc-2*-1ᵇ ⟦ x ⇓⟧  ∙ cong 1ᵇ_ (𝔹-leftInv x)
𝔹-leftInv (2ᵇ x) = cong inc (inc-2*-1ᵇ ⟦ x ⇓⟧) ∙ cong 2ᵇ_ (𝔹-leftInv x)

𝔹⇔ℕ : Iso 𝔹 ℕ
𝔹⇔ℕ .fun = ⟦_⇓⟧
𝔹⇔ℕ .inv = ⟦_⇑⟧
𝔹⇔ℕ .rightInv = 𝔹-rightInv
𝔹⇔ℕ .leftInv  = 𝔹-leftInv
