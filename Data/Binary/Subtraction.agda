module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Data.Binary.Decrement

data 𝔹± : Set where
  neg  : 𝔹±
  -1ᵇ  : 𝔹±
  +[_] : 𝔹 → 𝔹±

infixr 8 1ᵇ±_ 2ᵇ±_

1ᵇ±_ : 𝔹± → 𝔹±
1ᵇ± neg    = neg
1ᵇ± -1ᵇ    = -1ᵇ
1ᵇ± +[ x ] = +[ 1ᵇ x ]

2ᵇ±_ : 𝔹± → 𝔹±
2ᵇ± neg    = neg
2ᵇ± -1ᵇ    = +[ 0ᵇ ]
2ᵇ± +[ x ] = +[ 2ᵇ x ]

dec± : 𝔹 → 𝔹±
dec± 0ᵇ = -1ᵇ
dec± xs = +[ dec xs ]

abs : 𝔹± → 𝔹
abs neg    = 0ᵇ
abs -1ᵇ    = 0ᵇ
abs +[ x ] = x

mutual
  sub : 𝔹 → 𝔹 → 𝔹±
  sub xs      0ᵇ      = +[ xs ]
  sub 0ᵇ      (1ᵇ 0ᵇ) = -1ᵇ
  sub 0ᵇ      _       = neg
  sub (1ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₁ xs ys
  sub (2ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₁ xs ys
  sub (2ᵇ xs) (1ᵇ ys) = 1ᵇ± sub  xs ys
  sub (1ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₁ xs ys

  sub₁ : 𝔹 → 𝔹 → 𝔹±
  sub₁ xs      0ᵇ      = dec± xs
  sub₁ 0ᵇ      _       = neg
  sub₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ± sub₁ xs ys
  sub₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₁ xs ys
  sub₁ (2ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₁ xs ys
  sub₁ (1ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₂ xs ys

  sub₂ : 𝔹 → 𝔹 → 𝔹±
  sub₂ 0ᵇ      _       = neg
  sub₂ (1ᵇ xs) 0ᵇ      = 1ᵇ± dec± xs
  sub₂ (2ᵇ xs) 0ᵇ      = 2ᵇ± dec± xs
  sub₂ (1ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₂ xs ys
  sub₂ (2ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₂ xs ys
  sub₂ (2ᵇ xs) (1ᵇ ys) = 1ᵇ± sub₁ xs ys
  sub₂ (1ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₂ xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = abs (sub n m)
