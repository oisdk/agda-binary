module Data.Binary.Subtraction where

open import Data.Binary.Definition
open import Data.Binary.Decrement
open import Data.Binary.Double
open import Data.Binary.Helpers

ones : ℕ → 𝔹 → 𝔹
ones zero    xs = xs
ones (suc n) xs = ones n (1ᵇ xs)

2ones : ℕ → 𝔹 → 𝔹
2ones n xs = 2ᵇ ones n xs

_×2^suc_ : 𝔹 → ℕ → 𝔹
0ᵇ      ×2^suc n = 0ᵇ
(1ᵇ xs) ×2^suc n = 2ᵇ ones n (double xs)
(2ᵇ xs) ×2^suc n = 2ᵇ ones (suc n) xs

_×2^_ : 𝔹 → ℕ → 𝔹
xs ×2^ zero  = xs
xs ×2^ suc n = xs ×2^suc n

_-1×2^suc_ : 𝔹 → ℕ → 𝔹
0ᵇ      -1×2^suc _ = 0ᵇ
(2ᵇ xs) -1×2^suc n = 2ᵇ ones n (double xs)
(1ᵇ xs) -1×2^suc n = xs ×2^suc suc n

mutual
  -- sube₁ n x y = (x - (y + 1)) × 2ⁿ⁺¹
  sube₁ : ℕ → 𝔹 → 𝔹 → Maybe 𝔹
  sube₁ n 0ᵇ      _       = nothing
  sube₁ n xs      0ᵇ      = just (xs -1×2^suc n)
  sube₁ n (1ᵇ xs) (1ᵇ ys) = map-maybe (2ones n) (sube₁ 0 xs ys)
  sube₁ n (2ᵇ xs) (2ᵇ ys) = map-maybe (2ones n) (sube₁ 0 xs ys)
  sube₁ n (1ᵇ xs) (2ᵇ ys) = sube₁ (suc n) xs ys
  sube₁ n (2ᵇ xs) (1ᵇ ys) = sube  (suc n) xs ys

  -- sube n x y = (x - y) × 2ⁿ⁺¹
  sube : ℕ → 𝔹 → 𝔹 → Maybe 𝔹
  sube n xs      0ᵇ      = just (xs ×2^suc n)
  sube _ 0ᵇ      _       = nothing
  sube n (1ᵇ xs) (1ᵇ ys) = sube (suc n) xs ys
  sube n (2ᵇ xs) (2ᵇ ys) = sube (suc n) xs ys
  sube n (1ᵇ xs) (2ᵇ ys) = map-maybe (2ones n) (sube₁ 0 xs ys)
  sube n (2ᵇ xs) (1ᵇ ys) = map-maybe (2ones n) (sube  0 xs ys)

mutual
  -- sub₁ x y = x - (y + 1)
  sub₁ : 𝔹 → 𝔹 → Maybe 𝔹
  sub₁ 0ᵇ      _       = nothing
  sub₁ xs      0ᵇ      = just (dec xs)
  sub₁ (1ᵇ xs) (1ᵇ ys) = map-maybe 1ᵇ_ (sub₁ xs ys)
  sub₁ (2ᵇ xs) (2ᵇ ys) = map-maybe 1ᵇ_ (sub₁ xs ys)
  sub₁ (1ᵇ xs) (2ᵇ ys) = sube₁ 0 xs ys
  sub₁ (2ᵇ xs) (1ᵇ ys) = sube  0 xs ys

  -- sub x y = x - y
  sub : 𝔹 → 𝔹 → Maybe 𝔹
  sub xs      0ᵇ      = just xs
  sub 0ᵇ      _       = nothing
  sub (1ᵇ xs) (1ᵇ ys) = sube 0 xs ys
  sub (2ᵇ xs) (2ᵇ ys) = sube 0 xs ys
  sub (1ᵇ xs) (2ᵇ ys) = map-maybe 1ᵇ_ (sub₁ xs ys)
  sub (2ᵇ xs) (1ᵇ ys) = map-maybe 1ᵇ_ (sub  xs ys)

infixl 6 _-_
_-_ : 𝔹 → 𝔹 → 𝔹
n - m = from-maybe 0ᵇ (sub n m)
