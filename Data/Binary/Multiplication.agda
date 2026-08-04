module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Double
open import Data.Binary.Addition

infixl 6 _+2×_
_+2×_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    +2× ys = 2× ys
1ᵇ xs +2× ys = 1ᵇ (xs + ys)
2ᵇ xs +2× ys = 2ᵇ (xs + ys)

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys    = 0ᵇ
xs    * 0ᵇ    = 0ᵇ
1ᵇ xs * 1ᵇ ys = 1ᵇ ((xs + ys) +2× xs * ys)
1ᵇ xs * 2ᵇ ys = 2ᵇ (ys +2× (xs + xs * ys))
2ᵇ xs * 1ᵇ ys = 2ᵇ (xs +2× (ys + xs * ys))
2ᵇ xs * 2ᵇ ys = 2ᵇ 1ᵇ ((xs + ys) + xs * ys)
