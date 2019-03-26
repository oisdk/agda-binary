{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Operations.Multiplication where

open import Data.Binary.Distrib.Definitions
open import Data.Binary.Distrib.Operations.Addition

2* : 𝔹 → 𝔹
2* 0ᵇ      = 0ᵇ
2* (2*s x) = 2*s (s2* x)
2* (s2* x) = 2*s (2* x)

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0ᵇ      * _       = 0ᵇ
(2*s _) * 0ᵇ      = 0ᵇ
(s2* _) * 0ᵇ      = 0ᵇ
(2*s x) * (2*s y) = 2* (2*s (x + (y + x * y)))
(2*s x) * (s2* y) = 2*s (x + y * (2*s x))
(s2* x) * (2*s y) = 2*s (y + x * (2*s y))
(s2* x) * (s2* y) = s2* (x + y * (s2* x))
