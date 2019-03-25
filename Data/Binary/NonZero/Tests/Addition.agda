module Data.Binary.NonZero.Tests.Addition where

import Data.Binary.NonZero.Operations.Addition as 𝔹
open import Data.Binary.NonZero.Tests.Helpers
open import Relation.Binary.PropositionalEquality
import Data.Nat as ℕ

_ : 𝔹._+_ ≡⌈ 60 ⌉₂≡ ℕ._+_
_ = refl
