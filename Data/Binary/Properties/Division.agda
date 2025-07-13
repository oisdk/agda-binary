{-# OPTIONS --cubical #-}

module Data.Binary.Properties.Division where

open import Data.Binary.Definition
open import Data.Binary.Conversion
open import Data.Binary.Division
import Agda.Builtin.Nat as ℕ

open import Data.Binary.Properties.Isomorphism
open import Data.Binary.Properties.Helpers
open import Data.Binary.Helpers

0÷ : ∀ ys → 0ᵇ ÷ ys ≡ 0ᵇ
0÷ 0ᵇ      = refl
0÷ (1ᵇ ys) = refl
0÷ (2ᵇ ys) = refl

÷0 : ∀ xs → xs ÷ 0ᵇ ≡ 0ᵇ
÷0 0ᵇ      = refl
÷0 (1ᵇ xs) = refl
÷0 (2ᵇ xs) = refl

÷-cong : ∀ xs ys → ⟦ xs ÷ ys ⇓⟧ ≡ div ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
÷-cong xs ys = ℕ→𝔹→ℕ (div ⟦ xs ⇓⟧ ⟦ ys ⇓⟧)

