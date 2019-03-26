{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Tests.Multiplication where

import Data.Binary.Segmented.Operations.Multiplication as 𝔹
open import Data.Binary.Segmented.Tests.Helpers
open import Relation.Binary.PropositionalEquality
import Data.Nat as ℕ

_ : 𝔹._*_ ≡⌈ 20 ⌉₂≡ ℕ._*_
_ = refl
