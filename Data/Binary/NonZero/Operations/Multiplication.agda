{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Multiplication where

open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Addition

mul : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
mul 1⁺ ys = ys
mul (0⁺∷ xs) ys = 0⁺∷ (mul xs ys)
mul (1⁺∷ xs) ys = add₀ (0⁺∷ mul ys xs) ys

_*_ :  𝔹 → 𝔹 → 𝔹
0ᵇ * ys = 0ᵇ
(0< x) * 0ᵇ = 0ᵇ
(0< xs) * (0< ys) = 0< mul xs ys
