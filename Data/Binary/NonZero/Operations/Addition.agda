{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Addition where

open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary

mutual
  add₀ : 𝔹⁺ → 𝔹⁺ → Bit ⁺
  add₀ [] ys = inc⁺ ys
  add₀ (∹ xs) ys = add₀⁺ xs ys

  add₀⁺ : Bit ⁺ → 𝔹⁺ → Bit ⁺
  add₀⁺ xs (∹ ys) = add₀⁺⁺ xs ys
  add₀⁺ xs [] = inc⁺⁺ xs

  add₀⁺⁺ : Bit ⁺ → Bit ⁺ → Bit ⁺
  head (add₀⁺⁺ (O & xs) (y & ys)) = y
  tail (add₀⁺⁺ (O & xs) (y & ys)) = ∹ add₀ xs ys
  head (add₀⁺⁺ (I & xs) (O & ys)) = I
  tail (add₀⁺⁺ (I & xs) (O & ys)) = ∹ add₀ xs ys
  head (add₀⁺⁺ (I & xs) (I & ys)) = O
  tail (add₀⁺⁺ (I & xs) (I & ys)) = ∹ add₁ xs ys

  add₁ : 𝔹⁺ → 𝔹⁺ → Bit ⁺
  add₁ []       []       = I & []
  add₁ []       (y ∷ ys) = y & ∹ inc⁺ ys
  add₁ (O ∷ xs) []       = O & ∹ inc⁺ xs
  add₁ (O ∷ xs) (O ∷ ys) = I & ∹ add₀ xs ys
  add₁ (O ∷ xs) (I ∷ ys) = O & ∹ add₁ xs ys
  add₁ (I ∷ xs) []       = I & ∹ inc⁺ xs
  add₁ (I ∷ xs) (y ∷ ys) = y & ∹ add₁ xs ys

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< xs) + (0< ys) = 0< ∹ add₀ xs ys
