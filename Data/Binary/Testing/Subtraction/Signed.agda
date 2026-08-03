{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Testing.Subtraction.Signed where

open import Data.Binary.Definition
open import Data.Binary.Increment
open import Data.Binary.Testing
open import Data.Binary.Subtraction.Signed
import Agda.Builtin.Nat as ℕ

pos : ℤᵇ → 𝔹
pos +[ x ] = x
pos _      = 0ᵇ

mag : ℤᵇ → 𝔹
mag +[ _ ]   = 0ᵇ
mag -1ᵇ      = 1ᵇ 0ᵇ
mag -2ᵇ      = 2ᵇ 0ᵇ
mag -[3+ x ] = inc (inc (inc x))

_ : test (λ x y → pos (x - y)) ℕ._-_ 30
_ = refl

_ : test (λ x y → mag (x - y)) (λ x y → y ℕ.- x) 30
_ = refl
