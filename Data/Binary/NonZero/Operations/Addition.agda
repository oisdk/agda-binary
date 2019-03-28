{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Addition where

open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary

mutual
  add : Bit → 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  add O 1ᵇ ys = inc⁺⁺ ys
  add O (O ∷ xs) 1ᵇ = I ∷ xs
  add O (O ∷ xs) (O ∷ ys) = O ∷ add O xs ys
  add O (O ∷ xs) (I ∷ ys) = I ∷ add O xs ys
  add O (I ∷ xs) 1ᵇ = O ∷ inc⁺⁺ xs
  add O (I ∷ xs) (O ∷ ys) = I ∷ add O xs ys
  add O (I ∷ xs) (I ∷ ys) = O ∷ add I xs ys
  add I 1ᵇ 1ᵇ = I ∷ 1ᵇ
  add I 1ᵇ (O ∷ ys) = O ∷ inc⁺⁺ ys
  add I 1ᵇ (I ∷ ys) = I ∷ inc⁺⁺ ys
  add I (O ∷ xs) 1ᵇ = O ∷ inc⁺⁺ xs
  add I (O ∷ xs) (O ∷ ys) = I ∷ add O xs ys
  add I (O ∷ xs) (I ∷ ys) = O ∷ add I xs ys
  add I (I ∷ xs) 1ᵇ = I ∷ inc⁺⁺ xs
  add I (I ∷ xs) (O ∷ ys) = O ∷ add I xs ys
  add I (I ∷ xs) (I ∷ ys) = I ∷ add I xs ys

_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< xs) + (0< ys) = 0< add O xs ys
