module Data.Binary.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Double
open import Data.Binary.Addition
open import Data.Binary.Increment

infixl 6 _+2×_
-- x +2× y = x + (2 × y)
_+2×_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    +2× ys = 2× ys
1ᵇ xs +2× ys = 1ᵇ (xs + ys)
2ᵇ xs +2× ys = 2ᵇ (xs + ys)

2×[_+_] : 𝔹 → 𝔹 → 𝔹
2×[ 0ᵇ    + ys    ] = 2× ys
2×[ 1ᵇ xs + 0ᵇ    ] = 2ᵇ 2× xs
2×[ 2ᵇ xs + 0ᵇ    ] = 2ᵇ 1ᵇ xs
2×[ 2ᵇ xs + 2ᵇ ys ] = 2ᵇ 1ᵇ 1+[ xs + ys ]
2×[ 2ᵇ xs + 1ᵇ ys ] = 2ᵇ 2ᵇ (xs + ys)
2×[ 1ᵇ xs + 2ᵇ ys ] = 2ᵇ 2ᵇ (xs + ys)
2×[ 1ᵇ xs + 1ᵇ ys ] = 2ᵇ 1ᵇ (xs + ys)

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    * ys = 0ᵇ
1ᵇ xs * ys = ys +2× ys * xs
2ᵇ xs * ys = 2×[ ys + ys * xs ]
