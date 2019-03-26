{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Operations.Addition where

open import Data.Binary.Distrib.Definitions
open import Data.Binary.Distrib.Operations.Unary

_+_ : 𝔹 → 𝔹 → 𝔹
0ᵇ + ys = ys
(2*s xs) + 0ᵇ = 2*s xs
(2*s xs) + (2*s ys) = 2*s (inc (xs + ys))
(2*s xs) + (s2* ys) = inc (2*s (xs + ys))
(s2* xs) + 0ᵇ = s2* xs
(s2* xs) + (2*s ys) = inc (2*s (xs + ys))
(s2* xs) + (s2* ys) = inc (s2* (xs + ys))
