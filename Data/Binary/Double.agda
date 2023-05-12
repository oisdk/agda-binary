module Data.Binary.Double where

open import Data.Binary.Definition

double : 𝔹 → 𝔹
double 0ᵇ      = 0ᵇ
double (1ᵇ xs) = 2ᵇ double xs
double (2ᵇ xs) = 2ᵇ 1ᵇ xs
