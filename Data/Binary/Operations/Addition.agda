{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Addition where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary

mutual
  add : Bit → 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  add c (x ∷ xs) (y ∷ ys) = sumᵇ c x y ∷ add (carryᵇ c x y) xs ys
  add O 1ᵇ ys = inc⁺⁺ ys
  add O (O ∷ xs) 1ᵇ = I ∷ xs
  add O (I ∷ xs) 1ᵇ = O ∷ inc⁺⁺ xs
  add I 1ᵇ 1ᵇ = I ∷ 1ᵇ
  add I 1ᵇ (y ∷ ys) = y ∷ inc⁺⁺ ys
  add I (x ∷ xs) 1ᵇ = x ∷ inc⁺⁺ xs

_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< xs) + (0< ys) = 0< add O xs ys
