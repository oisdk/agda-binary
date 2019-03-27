{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Unary where

open import Data.Binary.NonZero.Definitions
open import Data.Maybe using (maybe)
open import Function

mutual
  inc⁺⁺ : Bit ⁺ → Bit ⁺
  inc⁺⁺ (O & xs) = I & xs
  inc⁺⁺ (I & xs) = O & ∹ inc⁺ xs

  inc⁺ : 𝔹⁺ → Bit ⁺
  inc⁺ [] = O & []
  inc⁺ (∹ xs) = inc⁺⁺ xs

inc : 𝔹 → 𝔹
inc x = 0< maybe (∹_ ∘ inc⁺) [] x

dec⁺ : 𝔹⁺ → 𝔹
dec⁺ [] = 0ᵇ
dec⁺ (O ∷ xs) = 1ᵇ∷ dec⁺ xs
dec⁺ (I ∷ xs) = 0< O ∷ xs

dec : 𝔹 → 𝔹
dec 0ᵇ = 0ᵇ
dec (0< x) = dec⁺ x
