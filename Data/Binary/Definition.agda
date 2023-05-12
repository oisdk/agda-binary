module Data.Binary.Definition where

infixr 8 1ᵇ_ 2ᵇ_
data 𝔹 : Set where
  0ᵇ : 𝔹
  1ᵇ_ 2ᵇ_ : 𝔹 → 𝔹
