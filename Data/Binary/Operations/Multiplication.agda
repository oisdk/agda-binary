{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Multiplication where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition

mul : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
mul 1ᵇ ys = ys
mul (O ∷ xs) ys = O ∷ (mul xs ys)
mul (I ∷ xs) ys = add O (O ∷ mul ys xs) ys

_*_ :  𝔹 → 𝔹 → 𝔹
0ᵇ * ys = 0ᵇ
(0< _) * 0ᵇ = 0ᵇ
(0< xs) * (0< ys) = 0< mul xs ys
{-# INLINE _*_ #-}
