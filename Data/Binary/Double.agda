module Data.Binary.Double where

open import Data.Binary.Definition

infixr 8 2×_
2×_ : 𝔹 → 𝔹
2× 0ᵇ    = 0ᵇ
2× 1ᵇ xs = 2ᵇ 2× xs
2× 2ᵇ xs = 2ᵇ 1ᵇ xs
