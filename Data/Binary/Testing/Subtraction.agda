{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Testing.Subtraction where

open import Data.Binary.Definition
open import Data.Binary.Helpers
open import Agda.Builtin.Unit
open import Data.Binary.Testing
open import Data.Binary.Subtraction
import Agda.Builtin.Nat as ℕ

_ : test _-_ ℕ._-_ 30
_ = refl

-- perf : perf-test _-_ 400
-- perf = refl
