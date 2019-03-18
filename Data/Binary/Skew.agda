{-# OPTIONS --without-K --safe #-}

module Data.Binary.Skew where

open import Data.List as List using (List; _∷_; [])
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product

𝔹 : Set
𝔹 = List ℕ

𝔹⁺ : Set
𝔹⁺ = ℕ × 𝔹

inc : 𝔹 → 𝔹⁺
inc [] = 0 , []
inc (x ∷ []) = 0 , x ∷ []
inc (x₁ ∷ zero ∷ xs) = suc x₁ , xs
inc (x₁ ∷ suc x₂ ∷ xs) = 0 , x₁ ∷ x₂ ∷ xs

dec : 𝔹⁺ → 𝔹
dec (suc x , xs) = x ∷ 0 ∷ xs
dec (zero , []) = []
dec (zero , x ∷ []) = x ∷ []
dec (zero , x₁ ∷ x₂ ∷ xs) = x₁ ∷ suc x₂ ∷ xs
