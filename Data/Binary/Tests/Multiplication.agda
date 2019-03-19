{-# OPTIONS --without-K --safe #-}

module Data.Binary.Tests.Multiplication where

open import Data.Binary.Operations.Multiplication
open import Data.Binary.Operations.Semantics
open import Data.Binary.Tests.Helpers
import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality

_ : ∀⟨ℕ⟩₂< 25 ∶ _*_ ≐ ℕ._*_
_ = refl

_ : ⟦ ⟦ 1000 ⇑⟧ * ⟦ 531 ⇑⟧ ⇓⟧ ≡ 1000 ℕ.* 531
_ = refl
