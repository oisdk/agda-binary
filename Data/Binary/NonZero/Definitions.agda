{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Definitions where

open import Function
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (_∷_) renaming ([] to 1ᵇ) public
open import Data.Maybe
open import Data.Product

Bit : Set
Bit = Bool

pattern O = false
pattern I = true

𝔹⁺ : Set
𝔹⁺ = Data.List.List Bit

𝔹 : Set
𝔹 = Maybe 𝔹⁺

infixr 5 0<_
pattern 0ᵇ = nothing
pattern 0<_ x = just x

𝔹± : Set
𝔹± = Maybe (Bit × 𝔹⁺)
