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

dec⁺⁺ : Bit → 𝔹⁺ → 𝔹⁺
dec⁺⁺ I xs = 0⁺∷ xs
dec⁺⁺ O 1⁺ = 1⁺
dec⁺⁺ O (x ⁺∷ xs) = 1⁺∷ dec⁺⁺ x xs

dec⁺ : 𝔹⁺ → 𝔹
dec⁺ 1⁺ = 0ᵇ
dec⁺ (x ⁺∷ xs) = 0< dec⁺⁺ x xs

dec : 𝔹 → 𝔹
dec 0ᵇ = 0ᵇ
dec (0< x) = dec⁺ x
