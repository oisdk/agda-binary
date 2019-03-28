{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Subtraction where

open import Data.Binary.NonZero.Definitions
open import Data.Product as Product using (map₁; map₂; proj₁; proj₂; _,_; _×_)
open import Data.Bool
import Data.Maybe as Maybe
import Data.Binary.NonZero.Operations.Addition as +
open import Data.Binary.NonZero.Operations.Unary

infixr 5 I_∷_ O∷_
I_∷_ : Bit → 𝔹± → 𝔹±
I s ∷ xs = 0< Maybe.maybe′ (map₂ (I ⁺∷_)) (s , 1⁺) xs

O∷_ : 𝔹± → 𝔹±
O∷_ = Maybe.map (map₂ (O ⁺∷_))

mutual
  sub₀ : 𝔹⁺ → 𝔹⁺ → 𝔹±
  sub₀ 1⁺ ys = Maybe.map (I ,_) (dec⁺ ys)
  sub₀ (x ⁺∷ xs) 1⁺ = Maybe.map (O ,_) (dec⁺ (x ⁺∷ xs))
  sub₀ (0⁺∷ xs) (0⁺∷ ys) = O∷ sub₀ xs ys
  sub₀ (0⁺∷ xs) (1⁺∷ ys) = I I ∷ sub₁ xs ys
  sub₀ (1⁺∷ xs) (0⁺∷ ys) = I O ∷ sub₀ xs ys
  sub₀ (1⁺∷ xs) (1⁺∷ ys) = O∷ sub₀ xs ys

  sub₁ : 𝔹⁺ → 𝔹⁺ → 𝔹±
  sub₁ 1⁺ ys = 0< (I , ys)
  sub₁ (0⁺∷ xs) (0⁺∷ ys) = I I ∷ sub₁ xs ys
  sub₁ (0⁺∷ xs) (1⁺∷ ys) = O∷ sub₁ xs ys
  sub₁ (0⁺∷ 1⁺) 1⁺ = 0ᵇ
  sub₁ (0⁺∷ x ⁺∷ xs) 1⁺ = 0< (O , 0⁺∷ dec⁺⁺ x xs)
  sub₁ (1⁺∷ xs) (0⁺∷ ys) = O∷ sub₀ xs ys
  sub₁ (1⁺∷ xs) (1⁺∷ ys) = I I ∷ sub₁ xs ys
  sub₁ (1⁺∷ 1⁺) 1⁺ = 0< (O , 1⁺)
  sub₁ (1⁺∷ x ⁺∷ xs) 1⁺ = 0< (O , 1⁺∷ dec⁺⁺ x xs)

_+_ : 𝔹± → 𝔹± → 𝔹±
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< (O , xs)) + (0< (O , ys)) = 0< (O , +.add₀ xs ys)
(0< (O , xs)) + (0< (I , ys)) = sub₀ xs ys
(0< (I , xs)) + (0< (O , ys)) = sub₀ ys xs
(0< (I , xs)) + (0< (I , ys)) = 0< (I , +.add₀ xs ys)
