{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Definitions where

open import Function
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using () renaming ([] to 1⁺; _∷_ to _⁺∷_) public
open import Data.Maybe
open import Data.Product

Bit : Set
Bit = Bool

pattern O = false
pattern I = true

infixr 5 0⁺∷_ 1⁺∷_

𝔹⁺ : Set
𝔹⁺ = Data.List.List Bit

pattern 0⁺∷_ xs = O ⁺∷ xs
pattern 1⁺∷_ xs = I ⁺∷ xs

𝔹 : Set
𝔹 = Maybe 𝔹⁺

infixr 5 0<_
pattern 0ᵇ = nothing
pattern 0<_ x = just x

𝔹± : Set
𝔹± = Maybe (Bit × 𝔹⁺)
