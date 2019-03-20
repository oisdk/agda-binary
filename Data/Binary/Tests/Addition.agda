{-# OPTIONS --without-K --safe #-}

module Data.Binary.Tests.Addition where

open import Data.Binary.Operations.Addition
open import Data.Binary.Tests.Helpers
import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality

_ : ∀⟨ℕ⟩₂< 60 ∶ _+_ ≐ ℕ._+_
_ = refl
