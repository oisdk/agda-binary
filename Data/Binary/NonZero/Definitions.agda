{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Definitions where

open import Function
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using () renaming ([] to 1⁺; _∷_ to _⁺∷_) public

Bit : Set
Bit = Bool

pattern O = false
pattern I = true

infixr 5 0⁺∷_ 1⁺∷_

𝔹⁺ : Set
𝔹⁺ = Data.List.List Bit

pattern 0⁺∷_ xs = O ⁺∷ xs
pattern 1⁺∷_ xs = I ⁺∷ xs

infixr 5 0<_
data 𝔹 : Set where
  0ᵇ : 𝔹
  0<_ : 𝔹⁺ → 𝔹
