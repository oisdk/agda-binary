{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Definitions where

open import Function

data Bit : Set where O I : Bit

infixr 5 _⁺∷_ 0⁺∷_ 1⁺∷_
data 𝔹⁺ : Set where
  1⁺ : 𝔹⁺
  _⁺∷_ : Bit → 𝔹⁺ → 𝔹⁺

pattern 0⁺∷_ xs = O ⁺∷ xs
pattern 1⁺∷_ xs = I ⁺∷ xs

infixr 5 0<_
data 𝔹 : Set where
  0ᵇ : 𝔹
  0<_ : 𝔹⁺ → 𝔹
