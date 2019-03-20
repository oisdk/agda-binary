{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Addition where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)

mutual
  0→⟨0?+0⟩ : 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0?+0⟩ 0₂ y₀ ys = y₀ 0& ys
  0→⟨0?+0⟩ (0< xs) y₀ ys = 0→⟨0+0⟩ (H₀ xs) (T₀ xs) y₀ ys

  0→⟨0+0⟩ : ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₀
  0→⟨0+0⟩ zero     xs zero     ys = suc₀ 0→⟨1+1⟩ (H₁ xs) (T₁ xs) (H₁ ys) (T₁ ys)
  0→⟨0+0⟩ zero     xs (suc y₀) ys = 0 0& 0→⟨1+0⟩ (H₁ xs) (T₁ xs) y₀ ys
  0→⟨0+0⟩ (suc x₀) xs zero     ys = 0 0& 0→⟨1+0⟩ (H₁ ys) (T₁ ys) x₀ xs
  0→⟨0+0⟩ (suc x₀) xs (suc y₀) ys = suc₀ 0→⟨0+0⟩ x₀ xs y₀ ys

  0→⟨1+0?⟩ : 𝔹₁ → 0≤ 𝔹₀ → 𝔹₁
  0→⟨1+0?⟩ xs 0₂ = xs
  0→⟨1+0?⟩ xs (0< ys) = 0→⟨1+0⟩ (H₁ xs) (T₁ xs) (H₀ ys) (T₀ ys)

  0→⟨1+0⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₁
  0→⟨1+0⟩ zero     xs zero     ys = suc₁ 0→⟨1+0?⟩ ys xs
  0→⟨1+0⟩ zero     xs (suc y₀) ys = 0 1& 0< 0→⟨0?+0⟩ xs y₀ ys
  0→⟨1+0⟩ (suc x₁) xs zero     ys = 0 1& 0< 0→⟨1+1⟩ x₁ xs (H₁ ys) (T₁ ys)
  0→⟨1+0⟩ (suc x₁) xs (suc y₀) ys = suc₁ 0→⟨1+0⟩ x₁ xs y₀ ys

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
  1→⟨0?+0⟩ 0₂ = carry
  1→⟨0?+0⟩ (0< xs) = 1→⟨0+0⟩ (H₀ xs) (T₀ xs)

  1→⟨0?+0?⟩ : 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  1→⟨0?+0?⟩ 0₂ 0₂ = 0 1& 0₂
  1→⟨0?+0?⟩ 0₂ (0< xs) = carry (H₀ xs) (T₀ xs)
  1→⟨0?+0?⟩ (0< xs) 0₂ = carry (H₀ xs) (T₀ xs)
  1→⟨0?+0?⟩ (0< xs) (0< ys) = 1→⟨0+0⟩ (H₀ xs) (T₀ xs) (H₀ ys) (T₀ ys)

  1→⟨0+0⟩ : ℕ → 𝔹₁ → ℕ → 𝔹₁ → 𝔹₁
  1→⟨0+0⟩ zero     xs zero     ys = 0 1& 0< 0→⟨1+1⟩ (H₁ xs) (T₁ xs) (H₁ ys) (T₁ ys)
  1→⟨0+0⟩ zero     xs (suc y₀) ys = suc₁ 0→⟨1+0⟩ (H₁ xs) (T₁ xs) y₀ ys
  1→⟨0+0⟩ (suc x₀) xs zero     ys = suc₁ 0→⟨1+0⟩ (H₁ ys) (T₁ ys) x₀ xs
  1→⟨0+0⟩ (suc x₀) xs (suc y₀) ys = 0 1& 0< 0→⟨0+0⟩ x₀ xs y₀ ys

  1→⟨1+0?⟩ : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₀
  1→⟨1+0?⟩ x xs 0₂ = x 0& inc≤ xs
  1→⟨1+0?⟩ x xs (0< ys) = 1→⟨1+0⟩ x xs (H₀ ys) (T₀ ys)

  1→⟨1+0⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 𝔹₁ → 𝔹₀
  1→⟨1+0⟩ zero     xs zero     ys = suc₀ 1→⟨1+0?⟩ (H₁ ys) (T₁ ys) xs
  1→⟨1+0⟩ zero     xs (suc y₀) ys = 0 0& 1→⟨0?+0⟩ xs y₀ ys
  1→⟨1+0⟩ (suc x₁) xs zero     ys = 0 0& 1→⟨1+1⟩ x₁ xs (H₁ ys) (T₁ ys)
  1→⟨1+0⟩ (suc x₁) xs (suc y₀) ys = suc₀ 1→⟨1+0⟩ x₁ xs y₀ ys

  1→⟨1+1⟩ : ℕ → 0≤ 𝔹₀ → ℕ → 0≤ 𝔹₀ → 𝔹₁
  1→⟨1+1⟩ zero     xs zero     ys = suc₁ 1→⟨0?+0?⟩ xs ys
  1→⟨1+1⟩ zero     xs (suc y₁) ys = 0 1& 0< 1→⟨1+0?⟩ y₁ ys xs
  1→⟨1+1⟩ (suc x₁) xs zero     ys = 0 1& 0< 1→⟨1+0?⟩ x₁ xs ys
  1→⟨1+1⟩ (suc x₁) xs (suc y₁) ys = suc₁ 1→⟨1+1⟩ x₁ xs y₁ ys

  carry : ℕ → 𝔹₁ → 𝔹₁
  carry zero     xs = suc₁ xs
  carry (suc x₀) xs = 0 1& 0< x₀ 0& xs

infixl 6 _+_
_+_ : 𝔹 → 𝔹 → 𝔹
0₂         + ys         = ys
(0< xs)    + 0₂         = 0< xs
(0< B₀ xs) + (0< B₀ ys) = 0< B₀ 0→⟨0+0⟩ (H₀ xs) (T₀ xs) (H₀ ys) (T₀ ys)
(0< B₀ xs) + (0< B₁ ys) = 0< B₁ 0→⟨1+0⟩ (H₁ ys) (T₁ ys) (H₀ xs) (T₀ xs)
(0< B₁ xs) + (0< B₀ ys) = 0< B₁ 0→⟨1+0⟩ (H₁ xs) (T₁ xs) (H₀ ys) (T₀ ys)
(0< B₁ xs) + (0< B₁ ys) = 0< B₀ 0→⟨1+1⟩ (H₁ xs) (T₁ xs) (H₁ ys) (T₁ ys)
