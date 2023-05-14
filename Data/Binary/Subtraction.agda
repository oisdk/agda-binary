module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Data.Binary.Decrement
open import Data.Binary.Double
open import Data.Binary.Helpers

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

_+1×2^suc_ : 𝔹 → ℕ → 𝔹
xs +1×2^suc n = 2ᵇ ones n xs

_×2^suc_ : 𝔹 → ℕ → 𝔹
0ᵇ      ×2^suc n = 0ᵇ
(1ᵇ xs) ×2^suc n = double xs +1×2^suc n
(2ᵇ xs) ×2^suc n = xs +1×2^suc suc n

mutual
  -- subᵉ₁ n x y = (x - (y + 1)) × 2ⁿ⁺¹
  subᵉ₁ : ℕ → 𝔹 → 𝔹 → Maybe 𝔹
  subᵉ₁ n 0ᵇ      _       = nothing
  subᵉ₁ n (1ᵇ xs) 0ᵇ      = just (xs ×2^suc suc n)
  subᵉ₁ n (2ᵇ xs) 0ᵇ      = just (double xs +1×2^suc n)
  subᵉ₁ n (1ᵇ xs) (1ᵇ ys) = map-maybe (_+1×2^suc n) (subᵉ₁ 0 xs ys)
  subᵉ₁ n (2ᵇ xs) (2ᵇ ys) = map-maybe (_+1×2^suc n) (subᵉ₁ 0 xs ys)
  subᵉ₁ n (1ᵇ xs) (2ᵇ ys) = subᵉ₁ (suc n) xs ys
  subᵉ₁ n (2ᵇ xs) (1ᵇ ys) = subᵉ  (suc n) xs ys

  -- subᵉ n x y = (x - y) × 2ⁿ⁺¹
  subᵉ : ℕ → 𝔹 → 𝔹 → Maybe 𝔹
  subᵉ n xs      0ᵇ      = just (xs ×2^suc n)
  subᵉ _ 0ᵇ      (1ᵇ _)  = nothing
  subᵉ _ 0ᵇ      (2ᵇ _)  = nothing
  subᵉ n (1ᵇ xs) (1ᵇ ys) = subᵉ (suc n) xs ys
  subᵉ n (2ᵇ xs) (2ᵇ ys) = subᵉ (suc n) xs ys
  subᵉ n (1ᵇ xs) (2ᵇ ys) = map-maybe (_+1×2^suc n) (subᵉ₁ 0 xs ys)
  subᵉ n (2ᵇ xs) (1ᵇ ys) = map-maybe (_+1×2^suc n) (subᵉ  0 xs ys)

mutual
  -- sub₁ x y = x - (y + 1)
  sub₁ : 𝔹 → 𝔹 → Maybe 𝔹
  sub₁ 0ᵇ      _       = nothing
  sub₁ (1ᵇ xs) 0ᵇ      = just (double xs)
  sub₁ (2ᵇ xs) 0ᵇ      = just (1ᵇ xs)
  sub₁ (1ᵇ xs) (1ᵇ ys) = map-maybe 1ᵇ_ (sub₁ xs ys)
  sub₁ (2ᵇ xs) (2ᵇ ys) = map-maybe 1ᵇ_ (sub₁ xs ys)
  sub₁ (1ᵇ xs) (2ᵇ ys) = subᵉ₁ 0 xs ys
  sub₁ (2ᵇ xs) (1ᵇ ys) = subᵉ  0 xs ys

  -- sub x y = x - y
  sub : 𝔹 → 𝔹 → Maybe 𝔹
  sub xs      0ᵇ      = just xs
  sub 0ᵇ      (1ᵇ _)  = nothing
  sub 0ᵇ      (2ᵇ _)  = nothing
  sub (1ᵇ xs) (1ᵇ ys) = subᵉ 0 xs ys
  sub (2ᵇ xs) (2ᵇ ys) = subᵉ 0 xs ys
  sub (1ᵇ xs) (2ᵇ ys) = map-maybe 1ᵇ_ (sub₁ xs ys)
  sub (2ᵇ xs) (1ᵇ ys) = map-maybe 1ᵇ_ (sub  xs ys)

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = from-maybe 0ᵇ (sub n m)
