module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Double
open import Data.Binary.Addition
open import Data.Binary.Increment

-- x +2× y = x + (2 × y)
_+2×_ : 𝔹 → 𝔹 → 𝔹
0ᵇ      +2× ys = double ys
(1ᵇ xs) +2× ys = 1ᵇ (xs + ys)
(2ᵇ xs) +2× ys = 2ᵇ (xs + ys)

-- x +² y = 2 × (x + y)
_+²_ : 𝔹 → 𝔹 → 𝔹
0ᵇ +² ys = double ys
(1ᵇ xs) +² 0ᵇ = 2ᵇ double xs
(2ᵇ xs) +² 0ᵇ = 2ᵇ 1ᵇ xs
(2ᵇ xs) +² (2ᵇ ys) = 2ᵇ 1ᵇ add₁ xs ys
(2ᵇ xs) +² (1ᵇ ys) = 2ᵇ 2ᵇ (xs + ys)
(1ᵇ xs) +² (2ᵇ ys) = 2ᵇ 2ᵇ (xs + ys)
(1ᵇ xs) +² (1ᵇ ys) = 2ᵇ 1ᵇ (xs + ys)

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys = 0ᵇ
1ᵇ xs * ys = ys +2× (ys * xs)
2ᵇ xs * ys = ys +²  (ys * xs)
