{-# OPTIONS --cubical #-}

module Data.Binary.Properties.Double where

open import Data.Binary.Conversion
open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Double
open import Data.Binary.Definition

import Agda.Builtin.Nat as ℕ

double-cong : ∀ xs → ⟦ double xs ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* 2
double-cong 0ᵇ i = zero
double-cong (1ᵇ xs) i = 2 ℕ.+ double-cong xs i ℕ.* 2
double-cong (2ᵇ xs) i = ⟦ 2ᵇ 1ᵇ xs ⇓⟧

double-plus : ∀ x → x ℕ.+ x ≡ x ℕ.* 2
double-plus x = cong (x ℕ.+_) (sym (+-idʳ x)) ∙ *-comm 2 x
