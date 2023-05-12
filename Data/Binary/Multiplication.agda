module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Double
open import Data.Binary.Addition

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys = 0ᵇ
1ᵇ xs * ys = ys + double (ys * xs)
2ᵇ xs * ys = double (ys + ys * xs)
