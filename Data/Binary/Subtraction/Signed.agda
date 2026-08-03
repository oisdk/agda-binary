module Data.Binary.Subtraction.Signed where

open import Data.Binary.Definition
open import Data.Binary.Decrement

data ℤᵇ : Set where
  +[_]   : 𝔹 → ℤᵇ
  -1ᵇ    : ℤᵇ
  -2ᵇ    : ℤᵇ
  -[3+_] : 𝔹 → ℤᵇ

infixr 8 1ᵇ±_ 2ᵇ±_ 1ᵇ∓_ 2ᵇ∓_

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

1ᵇ∓_ : ℤᵇ → ℤᵇ
1ᵇ∓ +[ x ]   = -[3+ 2ᵇ x ]
1ᵇ∓ -1ᵇ      = -[3+ 0ᵇ ]
1ᵇ∓ -2ᵇ      = -1ᵇ
1ᵇ∓ -[3+ x ] = +[ 1ᵇ x ]

2ᵇ∓_ : ℤᵇ → ℤᵇ
2ᵇ∓ +[ x ]   = -[3+ 1ᵇ x ]
2ᵇ∓ -1ᵇ      = -2ᵇ
2ᵇ∓ -2ᵇ      = +[ 0ᵇ ]
2ᵇ∓ -[3+ x ] = +[ 2ᵇ x ]

dec± : 𝔹 → ℤᵇ
dec± 0ᵇ = -1ᵇ
dec± xs = +[ dec xs ]

sub₁ : 𝔹 → 𝔹 → ℤᵇ
sub₁ xs      0ᵇ      = dec± xs
sub₁ 0ᵇ      (1ᵇ ys) = 2ᵇ∓ dec± ys
sub₁ 0ᵇ      (2ᵇ ys) = 1ᵇ∓ dec± ys
sub₁ (1ᵇ xs) (1ᵇ ys) = 1ᵇ± sub₁ xs ys
sub₁ (2ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₁ xs ys
sub₁ (2ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₁ xs ys
sub₁ (1ᵇ xs) (2ᵇ ys) = 2ᵇ∓ sub₁ ys xs

sub : 𝔹 → 𝔹 → ℤᵇ
sub xs      0ᵇ      = +[ xs ]
sub 0ᵇ      (1ᵇ ys) = 1ᵇ± sub₁ 0ᵇ ys
sub 0ᵇ      (2ᵇ ys) = 2ᵇ∓ dec± ys
sub (1ᵇ xs) (1ᵇ ys) = 2ᵇ± sub₁ xs ys
sub (2ᵇ xs) (2ᵇ ys) = 2ᵇ± sub₁ xs ys
sub (2ᵇ xs) (1ᵇ ys) = 1ᵇ± sub  xs ys
sub (1ᵇ xs) (2ᵇ ys) = 1ᵇ± sub₁ xs ys

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → ℤᵇ
_-_ = sub
