module Data.Binary.Decrement where

open import Data.Binary.Definition
open import Data.Binary.Double

dec : 𝔹 → 𝔹
dec 0ᵇ = 0ᵇ
dec (2ᵇ xs) = 1ᵇ xs
dec (1ᵇ xs) = 2× xs
