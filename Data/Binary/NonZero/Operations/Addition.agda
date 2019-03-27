{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Addition where

open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary

mutual
  add₀ : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  add₀ 1⁺ ys = inc⁺⁺ ys
  add₀ (0⁺∷ xs) 1⁺ = 1⁺∷ xs
  add₀ (0⁺∷ xs) (0⁺∷ ys) = 0⁺∷ add₀ xs ys
  add₀ (0⁺∷ xs) (1⁺∷ ys) = 1⁺∷ add₀ xs ys
  add₀ (1⁺∷ xs) 1⁺ = 0⁺∷ inc⁺⁺ xs
  add₀ (1⁺∷ xs) (0⁺∷ ys) = 1⁺∷ add₀ xs ys
  add₀ (1⁺∷ xs) (1⁺∷ ys) = 0⁺∷ add₁ xs ys

  add₁ : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  add₁ 1⁺ 1⁺ = 1⁺∷ 1⁺
  add₁ 1⁺ (0⁺∷ ys) = 0⁺∷ inc⁺⁺ ys
  add₁ 1⁺ (1⁺∷ ys) = 1⁺∷ inc⁺⁺ ys
  add₁ (0⁺∷ xs) 1⁺ = 0⁺∷ inc⁺⁺ xs
  add₁ (0⁺∷ xs) (0⁺∷ ys) = 1⁺∷ add₀ xs ys
  add₁ (0⁺∷ xs) (1⁺∷ ys) = 0⁺∷ add₁ xs ys
  add₁ (1⁺∷ xs) 1⁺ = 1⁺∷ inc⁺⁺ xs
  add₁ (1⁺∷ xs) (0⁺∷ ys) = 0⁺∷ add₁ xs ys
  add₁ (1⁺∷ xs) (1⁺∷ ys) = 1⁺∷ add₁ xs ys

_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< xs) + (0< ys) = 0< add₀ xs ys
