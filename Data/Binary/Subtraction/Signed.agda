module Data.Binary.Subtraction.Signed where

open import Data.Binary.Definition
open import Data.Binary.Decrement

data ℤᵇ : Set where
  +[_]   : 𝔹 → ℤᵇ
  -1ᵇ    : ℤᵇ
  -2ᵇ    : ℤᵇ
  -[3+_] : 𝔹 → ℤᵇ

infixr 8 1ᵇ±_ 2ᵇ±_

1ᵇ±_ : ℤᵇ → ℤᵇ
1ᵇ± +[ x ]   = +[ 1ᵇ x ]
1ᵇ± -1ᵇ      = -1ᵇ
1ᵇ± -2ᵇ      = -[3+ 0ᵇ ]
1ᵇ± -[3+ x ] = -[3+ 2ᵇ x ]

2ᵇ±_ : ℤᵇ → ℤᵇ
2ᵇ± +[ x ]   = +[ 2ᵇ x ]
2ᵇ± -1ᵇ      = +[ 0ᵇ ]
2ᵇ± -2ᵇ      = -2ᵇ
2ᵇ± -[3+ x ] = -[3+ 1ᵇ x ]

dec± : 𝔹 → ℤᵇ
dec± 0ᵇ = -1ᵇ
dec± xs = +[ dec xs ]

mutual
  sub : 𝔹 → 𝔹 → ℤᵇ
  sub xs      0ᵇ      = +[ xs ]
  sub 0ᵇ      (1ᵇ ys) = 1ᵇ± sub₁ 0ᵇ ys
  sub 0ᵇ      (2ᵇ ys) = 2ᵇ± sub₂ 0ᵇ ys
  sub (1ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₁ xs ys
  sub (2ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₁ xs ys
  sub (2ᵇ xs) (1ᵇ ys) = 1ᵇ± sub  xs ys
  sub (1ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₁ xs ys

  sub₁ : 𝔹 → 𝔹 → ℤᵇ
  sub₁ xs      0ᵇ      = dec± xs
  sub₁ 0ᵇ      (1ᵇ ys) = 2ᵇ± sub₂ 0ᵇ ys
  sub₁ 0ᵇ      (2ᵇ ys) = 1ᵇ± sub₂ 0ᵇ ys
  sub₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ± sub₁ xs ys
  sub₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₁ xs ys
  sub₁ (2ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₁ xs ys
  sub₁ (1ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₂ xs ys

  sub₂ : 𝔹 → 𝔹 → ℤᵇ
  sub₂ 0ᵇ      0ᵇ      = -2ᵇ
  sub₂ (1ᵇ xs) 0ᵇ      = 1ᵇ± dec± xs
  sub₂ (2ᵇ xs) 0ᵇ      = 2ᵇ± dec± xs
  sub₂ 0ᵇ      (1ᵇ ys) = 1ᵇ± sub₂ 0ᵇ ys
  sub₂ 0ᵇ      (2ᵇ ys) = -[3+ 1ᵇ ys ]
  sub₂ (1ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₂ xs ys
  sub₂ (2ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₂ xs ys
  sub₂ (2ᵇ xs) (1ᵇ ys) = 1ᵇ± sub₁ xs ys
  sub₂ (1ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₂ xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → ℤᵇ
_-_ = sub
