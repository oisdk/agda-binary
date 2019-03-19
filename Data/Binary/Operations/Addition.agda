{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Addition where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)

mutual
  0→⟨0?+0⟩ : 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0?+0⟩ 0₂ y₀ ys = y₀ 0& ys
  0→⟨0?+0⟩ (0< x₀ 0& xs) y₀ ys = 0→⟨0+0⟩ 0 x₀ xs y₀ ys

  0→⟨0+0⟩ : ℕ → ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0+0⟩ c zero     (x₁ 1& xs) zero     (y₁ 1& ys) = 0→⟨1+1⟩ (suc c) x₁ xs y₁ ys
  0→⟨0+0⟩ c zero     (x₁ 1& xs) (suc y₀) ys         = c 0& 0→⟨1+0⟩ 0 x₁ xs y₀ ys
  0→⟨0+0⟩ c (suc x₀) xs         zero     (y₁ 1& ys) = c 0& 0→⟨1+0⟩ 0 y₁ ys x₀ xs
  0→⟨0+0⟩ c (suc x₀) xs         (suc y₀) ys         = 0→⟨0+0⟩ (suc c) x₀ xs y₀ ys

  0→⟨1+0?⟩ : ℕ → ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  0→⟨1+0?⟩ c x₁ xs 0₂ = c ℕ.+ x₁ 1& xs
  0→⟨1+0?⟩ c x₁ xs (0< y₀ 0& ys) = 0→⟨1+0⟩ c x₁ xs y₀ ys

  0→⟨1+0⟩ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  0→⟨1+0⟩ c zero     xs zero     (y₁ 1& ys) = 0→⟨1+0?⟩ (suc c) y₁ ys xs
  0→⟨1+0⟩ c zero     xs (suc y₀) ys         = c 1& 0< 0→⟨0?+0⟩ xs y₀ ys
  0→⟨1+0⟩ c (suc x₁) xs zero     (y₁ 1& ys) = c 1& 0< 0→⟨1+1⟩ 0 x₁ xs y₁ ys
  0→⟨1+0⟩ c (suc x₁) xs (suc y₀) ys         = 0→⟨1+0⟩ (suc c) x₁ xs y₀ ys

  0→⟨1+1⟩ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₀
  0→⟨1+1⟩ c zero     xs zero     ys = c 0& 1→⟨0?+0?⟩ 0 xs ys
  0→⟨1+1⟩ c zero     xs (suc y₁) ys = 1→⟨1+0?⟩ (suc c) y₁ ys xs
  0→⟨1+1⟩ c (suc x₁) xs zero     ys = 1→⟨1+0?⟩ (suc c) x₁ xs ys
  0→⟨1+1⟩ c (suc x₁) xs (suc y₁) ys = c 0& 0→⟨1+1⟩′ 0 x₁ xs y₁ ys

  0→⟨1+1⟩′ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₁
  0→⟨1+1⟩′ c zero     xs zero     ys = 1→⟨0?+0?⟩ (suc c) xs ys
  0→⟨1+1⟩′ c zero     xs (suc y₁) ys = c 1& 0< 1→⟨1+0?⟩ 0 y₁ ys xs
  0→⟨1+1⟩′ c (suc x₁) xs zero     ys = c 1& 0< 1→⟨1+0?⟩ 0 x₁ xs ys
  0→⟨1+1⟩′ c (suc x₁) xs (suc y₁) ys = 0→⟨1+1⟩′ (suc c) x₁ xs y₁ ys

  1→⟨0?+0⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  1→⟨0?+0⟩ c 0₂ y₀ ys = carry c (y₀ 0& ys)
  1→⟨0?+0⟩ c (0< x₀ 0& xs) y₀ ys = 1→⟨0+0⟩ c x₀ xs y₀ ys

  1→⟨0?+0?⟩ : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  1→⟨0?+0?⟩ c 0₂ 0₂ = c 1& 0₂
  1→⟨0?+0?⟩ c 0₂ (0< xs) = carry c xs
  1→⟨0?+0?⟩ c (0< xs) 0₂ = carry c xs
  1→⟨0?+0?⟩ c (0< x₀ 0& xs) (0< y₀ 0& ys) = 1→⟨0+0⟩ c x₀ xs y₀ ys

  1→⟨0+0⟩ : ℕ → ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₁
  1→⟨0+0⟩ c zero     (x₁ 1& xs) zero     (y₁ 1& ys) = c 1& 0< 0→⟨1+1⟩ 0 x₁ xs y₁ ys
  1→⟨0+0⟩ c zero     (x₁ 1& xs) (suc y₀) ys         = 0→⟨1+0⟩ (suc c) x₁ xs y₀ ys
  1→⟨0+0⟩ c (suc x₀) xs         zero     (y₁ 1& ys) = 0→⟨1+0⟩ (suc c) y₁ ys x₀ xs
  1→⟨0+0⟩ c (suc x₀) xs         (suc y₀) ys         = c 1& 0< 0→⟨0+0⟩′ 0 x₀ xs y₀ ys

  0→⟨0+0⟩′ : ℕ → ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0+0⟩′ c zero     (x₁ 1& xs) zero     (y₁ 1& ys) = 0→⟨1+1⟩ (suc c) x₁ xs y₁ ys
  0→⟨0+0⟩′ c zero     (x₁ 1& xs) (suc y₀) ys         = c 0& 0→⟨1+0⟩ 0 x₁ xs y₀ ys
  0→⟨0+0⟩′ c (suc x₀) xs         zero     (y₁ 1& ys) = c 0& 0→⟨1+0⟩ 0 y₁ ys x₀ xs
  0→⟨0+0⟩′ c (suc x₀) xs         (suc y₀) ys         = 0→⟨0+0⟩′ (suc c) x₀ xs y₀ ys

  1→⟨1+0?⟩ : ℕ → ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₀
  1→⟨1+0?⟩ c x xs 0₂ = (c ℕ.+ x) 0& inc₁ xs
  1→⟨1+0?⟩ c x xs (0< y₀ 0& ys) = 1→⟨1+0⟩ c x xs y₀ ys

  1→⟨1+0⟩ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  1→⟨1+0⟩ c zero     xs zero     (y₁ 1& ys) = 1→⟨1+0?⟩ (suc c) y₁ ys xs
  1→⟨1+0⟩ c zero     xs (suc y₀) ys         = c 0& 1→⟨0?+0⟩ 0 xs y₀ ys
  1→⟨1+0⟩ c (suc x₁) xs zero     (y₁ 1& ys) = c 0& 1→⟨1+1⟩ 0 x₁ xs y₁ ys
  1→⟨1+0⟩ c (suc x₁) xs (suc y₀) ys         = 1→⟨1+0⟩ (suc c) x₁ xs y₀ ys

  1→⟨1+1⟩ : ℕ → ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₁
  1→⟨1+1⟩ c zero     xs zero     ys = 1→⟨0?+0?⟩ (suc c) xs ys
  1→⟨1+1⟩ c zero     xs (suc y₁) ys = c 1& 0< 1→⟨1+0?⟩ 0 y₁ ys xs
  1→⟨1+1⟩ c (suc x₁) xs zero     ys = c 1& 0< 1→⟨1+0?⟩ 0 x₁ xs ys
  1→⟨1+1⟩ c (suc x₁) xs (suc y₁) ys = 1→⟨1+1⟩ (suc c) x₁ xs y₁ ys

  carry : ℕ → 𝔹₀ → 𝔹₁
  carry n (zero  0& y 1& xs) = suc (n ℕ.+ y) 1& xs
  carry n (suc x 0& y 1& xs) = n 1& 0< x 0& y 1& xs

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0₂               + ys               = ys
(0< xs)          + 0₂               = 0< xs
(0< B₀ x₀ 0& xs) + (0< B₀ y₀ 0& ys) = 0< B₀ 0→⟨0+0⟩ 0 x₀ xs y₀ ys
(0< B₀ x₀ 0& xs) + (0< B₁ y₁ 1& ys) = 0< B₁ 0→⟨1+0⟩ 0 y₁ ys x₀ xs
(0< B₁ x₁ 1& xs) + (0< B₀ y₀ 0& ys) = 0< B₁ 0→⟨1+0⟩ 0 x₁ xs y₀ ys
(0< B₁ x₁ 1& xs) + (0< B₁ y₁ 1& ys) = 0< B₀ 0→⟨1+1⟩ 0 x₁ xs y₁ ys
