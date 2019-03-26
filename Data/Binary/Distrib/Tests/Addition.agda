{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Tests.Addition where

open import Data.Binary.Distrib.Tests.Helpers
open import Relation.Binary.PropositionalEquality
import Data.Binary.Distrib.Operations.Addition as 𝔹
import Data.Nat as ℕ

_ : 𝔹._+_ ≡⌈ 60 ⌉₂≡ ℕ._+_
_ = refl
