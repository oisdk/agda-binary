{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Definitions where

open import Function
open import Data.List as List using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)

data Bit : Set where O I : Bit

infixr 5 0⁺∷_ 1⁺∷_
𝔹⁺ : Set
𝔹⁺ = List Bit

pattern 1⁺ = []
pattern 0⁺∷_ xs = O ∷ xs
pattern 1⁺∷_ xs = I ∷ xs

infixr 5 0<_

𝔹 : Set
𝔹 = Maybe 𝔹⁺

pattern 0ᵇ = nothing
pattern 0<_ x = just x

infixr 5 0ᵇ∷_ 1ᵇ∷_
0ᵇ∷_ : 𝔹 → 𝔹
0ᵇ∷ 0ᵇ = 0ᵇ
0ᵇ∷ (0< xs) = 0< 0⁺∷ xs

1ᵇ∷_ : 𝔹 → 𝔹
1ᵇ∷ xs = 0< (maybe 1⁺∷_ 1⁺ xs)
