{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Addition where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)

mutual
  0→⟨0?+0⟩ : 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0?+0⟩ 0₂ y₀ ys = y₀ 0& ys
  0→⟨0?+0⟩ (0< x₀ 0& xs) y₀ ys = 0→⟨0+0⟩ x₀ xs y₀ ys

  0→⟨0+0⟩ : ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0+0⟩ zero     (x₁ 1& xs) zero     (y₁ 1& ys) = suc₀ 0→⟨1+1⟩ x₁ xs y₁ ys
  0→⟨0+0⟩ zero     (x₁ 1& xs) (suc y₀) ys         = 0 0& 0→⟨1+0⟩ x₁ xs y₀ ys
  0→⟨0+0⟩ (suc x₀) xs         zero     (y₁ 1& ys) = 0 0& 0→⟨1+0⟩ y₁ ys x₀ xs
  0→⟨0+0⟩ (suc x₀) xs         (suc y₀) ys         = suc₀ 0→⟨0+0⟩ x₀ xs y₀ ys

  0→⟨1+0?⟩ : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  0→⟨1+0?⟩ x₁ xs 0₂ = x₁ 1& xs
  0→⟨1+0?⟩ x₁ xs (0< y₀ 0& ys) = 0→⟨1+0⟩ x₁ xs y₀ ys

  0→⟨1+0⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  0→⟨1+0⟩ zero     xs zero     (y₁ 1& ys) = suc₁ 0→⟨1+0?⟩ y₁ ys xs
  0→⟨1+0⟩ zero     xs (suc y₀) ys         = 0 1& 0< 0→⟨0?+0⟩ xs y₀ ys
  0→⟨1+0⟩ (suc x₁) xs zero     (y₁ 1& ys) = 0 1& 0< 0→⟨1+1⟩ x₁ xs y₁ ys
  0→⟨1+0⟩ (suc x₁) xs (suc y₀) ys         = suc₁ 0→⟨1+0⟩ x₁ xs y₀ ys

  0→⟨1+1⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₀
  0→⟨1+1⟩ zero     xs zero     ys = 0 0& 1→⟨0?+0?⟩ xs ys
  0→⟨1+1⟩ zero     xs (suc y₁) ys = suc₀ 1→⟨1+0?⟩ y₁ ys xs
  0→⟨1+1⟩ (suc x₁) xs zero     ys = suc₀ 1→⟨1+0?⟩ x₁ xs ys
  0→⟨1+1⟩ (suc x₁) xs (suc y₁) ys = 0 0& 0→⟨1+1⟩′ x₁ xs y₁ ys

  0→⟨1+1⟩′ : ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₁
  0→⟨1+1⟩′ zero     xs zero     ys = suc₁ 1→⟨0?+0?⟩ xs ys
  0→⟨1+1⟩′ zero     xs (suc y₁) ys = 0 1& 0< 1→⟨1+0?⟩ y₁ ys xs
  0→⟨1+1⟩′ (suc x₁) xs zero     ys = 0 1& 0< 1→⟨1+0?⟩ x₁ xs ys
  0→⟨1+1⟩′ (suc x₁) xs (suc y₁) ys = suc₁ 0→⟨1+1⟩′ x₁ xs y₁ ys

  1→⟨0?+0⟩ : 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  1→⟨0?+0⟩ 0₂ y₀ ys = carry 0 (y₀ 0& ys)
  1→⟨0?+0⟩ (0< x₀ 0& xs) y₀ ys = 1→⟨0+0⟩ x₀ xs y₀ ys

  1→⟨0?+0?⟩ : 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  1→⟨0?+0?⟩ 0₂ 0₂ = 0 1& 0₂
  1→⟨0?+0?⟩ 0₂ (0< xs) = carry 0 xs
  1→⟨0?+0?⟩ (0< xs) 0₂ = carry 0 xs
  1→⟨0?+0?⟩ (0< x₀ 0& xs) (0< y₀ 0& ys) = 1→⟨0+0⟩ x₀ xs y₀ ys

  1→⟨0+0⟩ : ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₁
  1→⟨0+0⟩ zero     (x₁ 1& xs) zero     (y₁ 1& ys) = 0 1& 0< 0→⟨1+1⟩ x₁ xs y₁ ys
  1→⟨0+0⟩ zero     (x₁ 1& xs) (suc y₀) ys         = suc₁ 0→⟨1+0⟩ x₁ xs y₀ ys
  1→⟨0+0⟩ (suc x₀) xs         zero     (y₁ 1& ys) = suc₁ 0→⟨1+0⟩ y₁ ys x₀ xs
  1→⟨0+0⟩ (suc x₀) xs         (suc y₀) ys         = 0 1& 0< 0→⟨0+0⟩′ x₀ xs y₀ ys

  0→⟨0+0⟩′ : ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0+0⟩′ zero     (x₁ 1& xs) zero     (y₁ 1& ys) = suc₀ 0→⟨1+1⟩ x₁ xs y₁ ys
  0→⟨0+0⟩′ zero     (x₁ 1& xs) (suc y₀) ys         = 0 0& 0→⟨1+0⟩ x₁ xs y₀ ys
  0→⟨0+0⟩′ (suc x₀) xs         zero     (y₁ 1& ys) = 0 0& 0→⟨1+0⟩ y₁ ys x₀ xs
  0→⟨0+0⟩′ (suc x₀) xs         (suc y₀) ys         = suc₀ 0→⟨0+0⟩′ x₀ xs y₀ ys

  1→⟨1+0?⟩ : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₀
  1→⟨1+0?⟩ x xs 0₂ = x 0& inc₁ xs
  1→⟨1+0?⟩ x xs (0< y₀ 0& ys) = 1→⟨1+0⟩ x xs y₀ ys

  1→⟨1+0⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  1→⟨1+0⟩ zero     xs zero     (y₁ 1& ys) = suc₀ 1→⟨1+0?⟩ y₁ ys xs
  1→⟨1+0⟩ zero     xs (suc y₀) ys         = 0 0& 1→⟨0?+0⟩ xs y₀ ys
  1→⟨1+0⟩ (suc x₁) xs zero     (y₁ 1& ys) = 0 0& 1→⟨1+1⟩ x₁ xs y₁ ys
  1→⟨1+0⟩ (suc x₁) xs (suc y₀) ys         = suc₀ 1→⟨1+0⟩ x₁ xs y₀ ys

  1→⟨1+1⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₁
  1→⟨1+1⟩ zero     xs zero     ys = suc₁ 1→⟨0?+0?⟩ xs ys
  1→⟨1+1⟩ zero     xs (suc y₁) ys = 0 1& 0< 1→⟨1+0?⟩ y₁ ys xs
  1→⟨1+1⟩ (suc x₁) xs zero     ys = 0 1& 0< 1→⟨1+0?⟩ x₁ xs ys
  1→⟨1+1⟩ (suc x₁) xs (suc y₁) ys = suc₁ 1→⟨1+1⟩ x₁ xs y₁ ys

  carry : ℕ → 𝔹₀ → 𝔹₁
  carry c (zero   0& x₁ 1& xs) = suc (c ℕ.+ x₁) 1& xs
  carry c (suc x₀ 0& x₁ 1& xs) = c 1& 0< x₀ 0& x₁ 1& xs

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0₂               + ys               = ys
(0< xs)          + 0₂               = 0< xs
(0< B₀ x₀ 0& xs) + (0< B₀ y₀ 0& ys) = 0< B₀ 0→⟨0+0⟩ x₀ xs y₀ ys
(0< B₀ x₀ 0& xs) + (0< B₁ y₁ 1& ys) = 0< B₁ 0→⟨1+0⟩ y₁ ys x₀ xs
(0< B₁ x₁ 1& xs) + (0< B₀ y₀ 0& ys) = 0< B₁ 0→⟨1+0⟩ x₁ xs y₀ ys
(0< B₁ x₁ 1& xs) + (0< B₁ y₁ 1& ys) = 0< B₀ 0→⟨1+1⟩ x₁ xs y₁ ys
