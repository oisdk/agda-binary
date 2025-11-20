{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Double where

open import Data.Binary.Conversion
open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Double
open import Data.Binary.Definition

import Agda.Builtin.Nat as ℕ

double-cong : ∀ xs → ⟦ 2× xs ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* 2
double-cong 0ᵇ = refl
double-cong (1ᵇ xs) = cong (λ r → 2 ℕ.+ r ℕ.* 2) (double-cong xs)
double-cong (2ᵇ xs) = refl

double-plus : ∀ x → x ℕ.+ x ≡ x ℕ.* 2
double-plus x = cong (x ℕ.+_) (sym (+-idʳ x)) ∙ *-comm 2 x
