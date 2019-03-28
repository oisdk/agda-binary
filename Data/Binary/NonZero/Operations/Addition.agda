{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Addition where

open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary

mutual
  add₀ : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  add₀ 1ᵇ ys = inc⁺⁺ ys
  add₀ (O ∷ xs) 1ᵇ = I ∷ xs
  add₀ (O ∷ xs) (O ∷ ys) = O ∷ add₀ xs ys
  add₀ (O ∷ xs) (I ∷ ys) = I ∷ add₀ xs ys
  add₀ (I ∷ xs) 1ᵇ = O ∷ inc⁺⁺ xs
  add₀ (I ∷ xs) (O ∷ ys) = I ∷ add₀ xs ys
  add₀ (I ∷ xs) (I ∷ ys) = O ∷ add₁ xs ys

  add₁ : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  add₁ 1ᵇ 1ᵇ = I ∷ 1ᵇ
  add₁ 1ᵇ (O ∷ ys) = O ∷ inc⁺⁺ ys
  add₁ 1ᵇ (I ∷ ys) = I ∷ inc⁺⁺ ys
  add₁ (O ∷ xs) 1ᵇ = O ∷ inc⁺⁺ xs
  add₁ (O ∷ xs) (O ∷ ys) = I ∷ add₀ xs ys
  add₁ (O ∷ xs) (I ∷ ys) = O ∷ add₁ xs ys
  add₁ (I ∷ xs) 1ᵇ = I ∷ inc⁺⁺ xs
  add₁ (I ∷ xs) (O ∷ ys) = O ∷ add₁ xs ys
  add₁ (I ∷ xs) (I ∷ ys) = I ∷ add₁ xs ys

_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< xs) + (0< ys) = 0< add₀ xs ys
