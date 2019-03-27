{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Definitions where

open import Function

infixr 5 0⁺∷_ 1⁺∷_
data 𝔹⁺ : Set where
  1⁺ : 𝔹⁺
  0⁺∷_ : 𝔹⁺ → 𝔹⁺
  1⁺∷_ : 𝔹⁺ → 𝔹⁺

infixr 5 0<_
data 𝔹 : Set where
  0ᵇ : 𝔹
  0<_ : 𝔹⁺ → 𝔹

infixr 5 0ᵇ∷_ 1ᵇ∷_
0ᵇ∷_ : 𝔹 → 𝔹
0ᵇ∷ 0ᵇ = 0ᵇ
0ᵇ∷ (0< xs) = 0< 0⁺∷ xs

1ᵇ∷_ : 𝔹 → 𝔹
1ᵇ∷ xs = 0< (case xs of λ { 0ᵇ → 1⁺ ; (0< x) → 1⁺∷ x})
