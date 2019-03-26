{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Tests.Multiplication where

import Data.Binary.NonZero.Operations.Multiplication as 𝔹
open import Data.Binary.NonZero.Tests.Helpers
open import Relation.Binary.PropositionalEquality
import Data.Nat as ℕ

_ : 𝔹._*_ ≡⌈ 60 ⌉₂≡ ℕ._*_
_ = refl
