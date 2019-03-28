{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Subtraction where

open import Data.Binary.NonZero.Definitions
open import Data.Product as Product using (map₁; map₂; proj₁; proj₂; _,_; _×_)
open import Data.Bool
import Data.Maybe as Maybe
import Data.Binary.NonZero.Operations.Addition as +
open import Data.Binary.NonZero.Operations.Unary

infixr 5 Is_∷_ O∷_
Is_∷_ : Bit → 𝔹± → 𝔹±
Is s ∷ xs = 0< Maybe.maybe′ (map₂ (I ∷_)) (s , 1ᵇ) xs

O∷_ : 𝔹± → 𝔹±
O∷_ = Maybe.map (map₂ (O ∷_))

mutual
  sub₀ : 𝔹⁺ → 𝔹⁺ → 𝔹±
  sub₀ 1ᵇ ys = Maybe.map (I ,_) (dec⁺ ys)
  sub₀ (x ∷ xs) 1ᵇ = Maybe.map (O ,_) (dec⁺ (x ∷ xs))
  sub₀ (O ∷ xs) (O ∷ ys) = O∷ sub₀ xs ys
  sub₀ (O ∷ xs) (I ∷ ys) = Is I ∷ sub₁ xs ys
  sub₀ (I ∷ xs) (O ∷ ys) = Is O ∷ sub₀ xs ys
  sub₀ (I ∷ xs) (I ∷ ys) = O∷ sub₀ xs ys

  sub₁ : 𝔹⁺ → 𝔹⁺ → 𝔹±
  sub₁ 1ᵇ ys = 0< (I , ys)
  sub₁ (O ∷ xs) (O ∷ ys) = Is I ∷ sub₁ xs ys
  sub₁ (O ∷ xs) (I ∷ ys) = O∷ sub₁ xs ys
  sub₁ (O ∷ 1ᵇ) 1ᵇ = 0ᵇ
  sub₁ (O ∷ x ∷ xs) 1ᵇ = 0< (O , O ∷ dec⁺⁺ x xs)
  sub₁ (I ∷ xs) (O ∷ ys) = O∷ sub₀ xs ys
  sub₁ (I ∷ xs) (I ∷ ys) = Is I ∷ sub₁ xs ys
  sub₁ (I ∷ 1ᵇ) 1ᵇ = 0< (O , 1ᵇ)
  sub₁ (I ∷ x ∷ xs) 1ᵇ = 0< (O , I ∷ dec⁺⁺ x xs)

_+_ : 𝔹± → 𝔹± → 𝔹±
0ᵇ + ys = ys
(0< xs) + 0ᵇ = 0< xs
(0< (O , xs)) + (0< (O , ys)) = 0< (O , +.add₀ xs ys)
(0< (O , xs)) + (0< (I , ys)) = sub₀ xs ys
(0< (I , xs)) + (0< (O , ys)) = sub₀ ys xs
(0< (I , xs)) + (0< (I , ys)) = 0< (I , +.add₀ xs ys)
