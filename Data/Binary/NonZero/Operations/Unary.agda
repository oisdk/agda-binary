{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Unary where

open import Data.Binary.NonZero.Definitions
open import Function

inc⁺⁺ : 𝔹⁺ → 𝔹⁺
inc⁺⁺ 1⁺ = 0⁺∷ 1⁺
inc⁺⁺ (0⁺∷ xs) = 1⁺∷ xs
inc⁺⁺ (1⁺∷ xs) = 0⁺∷ inc⁺⁺ xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0ᵇ = 1⁺
inc⁺ (0< x) = inc⁺⁺ x

inc : 𝔹 → 𝔹
inc x = 0< inc⁺ x

dec⁺ : 𝔹⁺ → 𝔹
dec⁺ 1⁺ = 0ᵇ
dec⁺ (0⁺∷ xs) = 0< (case dec⁺ xs of λ { 0ᵇ → 1⁺ ; (0< ys) → 1⁺∷ ys })
dec⁺ (1⁺∷ xs) = 0< 0⁺∷ xs

dec : 𝔹 → 𝔹
dec 0ᵇ = 0ᵇ
dec (0< x) = dec⁺ x
