{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Multiplication where

open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Addition

mutual
  mul⁺ : Bit ⁺ → 𝔹⁺ → Bit ⁺
  mul⁺ (O & xs) ys = O & mul xs ys
  mul⁺ (I & xs) 1⁺ = I & xs
  mul⁺ (I & xs) (∹ ys) = head ys & ∹ add₀⁺ (mul⁺ ys xs) (tail ys)

  mul : 𝔹⁺ → 𝔹⁺ → 𝔹⁺
  mul [] ys = ys
  mul (∹ xs) ys = ∹ mul⁺ xs ys

_*_ :  𝔹 → 𝔹 → 𝔹
0ᵇ * ys = 0ᵇ
(0< xs) * 0ᵇ = 0ᵇ
(0< xs) * (0< ys) = 0< mul xs ys
