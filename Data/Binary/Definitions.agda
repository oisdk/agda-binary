{-# OPTIONS --without-K --safe #-}

module Data.Binary.Definitions where

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
      zeroes : ℕ
      tail₁ : 𝔹₁

  record 𝔹₁ : Set where
    constructor _1&_
    inductive
    field
      ones : ℕ
      tail₀ : 0≤  𝔹₀
open 𝔹₀ public
open 𝔹₁ public

data 𝔹⁺ : Set where
  B₀_ : 𝔹₀ → 𝔹⁺
  B₁_ : 𝔹₁ → 𝔹⁺

𝔹 : Set
𝔹 = 0≤ 𝔹⁺

infixr 5 suc₀_ suc₁_
suc₀_ : 𝔹₀ → 𝔹₀
zeroes (suc₀ xs) = suc (zeroes xs)
tail₁  (suc₀ xs) = tail₁ xs

suc₁_ : 𝔹₁ → 𝔹₁
ones  (suc₁ xs) = suc (ones xs)
tail₀ (suc₁ xs) = tail₀ xs
