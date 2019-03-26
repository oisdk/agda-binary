{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Tests.Addition where

open import Data.Binary.Segmented.Tests.Helpers
open import Relation.Binary.PropositionalEquality
import Data.Binary.Segmented.Operations.Addition as 𝔹
import Data.Nat as ℕ

_ : 𝔹._+_ ≡⌈ 60 ⌉₂≡ ℕ._+_
_ = refl
