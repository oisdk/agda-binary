{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Unary where

open import Data.Binary.Definitions
open import Function

inc⁺⁺ : 𝔹⁺ → 𝔹⁺
inc⁺⁺ 1ᵇ = O ∷ 1ᵇ
inc⁺⁺ (O ∷ xs) = I ∷ xs
inc⁺⁺ (I ∷ xs) = O ∷ inc⁺⁺ xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0ᵇ = 1ᵇ
inc⁺ (0< x) = inc⁺⁺ x

inc : 𝔹 → 𝔹
inc x = 0< inc⁺ x

dec⁺⁺ : Bit → 𝔹⁺ → 𝔹⁺
dec⁺⁺ I xs = O ∷ xs
dec⁺⁺ O 1ᵇ = 1ᵇ
dec⁺⁺ O (x ∷ xs) = I ∷ dec⁺⁺ x xs

dec⁺ : 𝔹⁺ → 𝔹
dec⁺ 1ᵇ = 0ᵇ
dec⁺ (x ∷ xs) = 0< dec⁺⁺ x xs

dec : 𝔹 → 𝔹
dec 0ᵇ = 0ᵇ
dec (0< x) = dec⁺ x
