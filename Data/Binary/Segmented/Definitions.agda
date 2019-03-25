{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Definitions where

open import Data.Nat as ℕ using (ℕ; suc; zero)

infixr 5 _0&_ _1&_ B₀_ B₁_ 0<_

-- A "maybe"-like type, specialised here because I have a
-- suspicion it's more efficient.
data 0≤_ (A : Set) : Set where
  0₂  : 0≤ A
  0<_ : A → 0≤ A

mutual
  record 𝔹₀ : Set where
    constructor _0&_
    inductive
    field
      H₀ : ℕ
      T₀ : 𝔹₁

  record 𝔹₁ : Set where
    constructor _1&_
    inductive
    field
      H₁ : ℕ
      T₁ : 0≤  𝔹₀
open 𝔹₀ public
open 𝔹₁ public

data 𝔹⁺ : Set where
  B₀_ : 𝔹₀ → 𝔹⁺
  B₁_ : 𝔹₁ → 𝔹⁺

𝔹 : Set
𝔹 = 0≤ 𝔹⁺

infixr 5 suc₀_ suc₁_
suc₀_ : 𝔹₀ → 𝔹₀
H₀ (suc₀ xs) = suc (H₀ xs)
T₀ (suc₀ xs) = T₀ xs

suc₁_ : 𝔹₁ → 𝔹₁
H₁ (suc₁ xs) = suc (H₁ xs)
T₁ (suc₁ xs) = T₁ xs
