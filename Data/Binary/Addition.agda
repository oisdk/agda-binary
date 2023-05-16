module Data.Binary.Addition where

open import Data.Binary.Definition
open import Data.Binary.Increment

1+[_+_] : 𝔹 → 𝔹 → 𝔹
2+[_+_] : 𝔹 → 𝔹 → 𝔹

1+[ 0ᵇ    + ys    ] = inc ys
1+[ 1ᵇ xs + 0ᵇ    ] = 2ᵇ xs
1+[ 2ᵇ xs + 0ᵇ    ] = 1ᵇ inc xs
1+[ 1ᵇ xs + 1ᵇ ys ] = 1ᵇ 1+[ xs + ys ]
1+[ 1ᵇ xs + 2ᵇ ys ] = 2ᵇ 1+[ xs + ys ]
1+[ 2ᵇ xs + 1ᵇ ys ] = 2ᵇ 1+[ xs + ys ]
1+[ 2ᵇ xs + 2ᵇ ys ] = 1ᵇ 2+[ xs + ys ]

2+[ 0ᵇ    + 0ᵇ    ] = 2ᵇ 0ᵇ
2+[ 0ᵇ    + 1ᵇ ys ] = 1ᵇ inc ys
2+[ 0ᵇ    + 2ᵇ ys ] = 2ᵇ inc ys
2+[ 1ᵇ xs + 0ᵇ    ] = 1ᵇ inc xs
2+[ 2ᵇ xs + 0ᵇ    ] = 2ᵇ inc xs
2+[ 1ᵇ xs + 1ᵇ ys ] = 2ᵇ 1+[ xs + ys ]
2+[ 1ᵇ xs + 2ᵇ ys ] = 1ᵇ 2+[ xs + ys ]
2+[ 2ᵇ xs + 1ᵇ ys ] = 1ᵇ 2+[ xs + ys ]
2+[ 2ᵇ xs + 2ᵇ ys ] = 2ᵇ 2+[ xs + ys ]

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ    + ys    = ys
1ᵇ xs + 0ᵇ    = 1ᵇ xs
2ᵇ xs + 0ᵇ    = 2ᵇ xs
1ᵇ xs + 1ᵇ ys = 2ᵇ (xs + ys)
1ᵇ xs + 2ᵇ ys = 1ᵇ 1+[ xs + ys ]
2ᵇ xs + 1ᵇ ys = 1ᵇ 1+[ xs + ys ]
2ᵇ xs + 2ᵇ ys = 2ᵇ 1+[ xs + ys ]
