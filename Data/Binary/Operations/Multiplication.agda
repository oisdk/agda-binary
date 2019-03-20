{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Multiplication where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition
open import Data.Nat as ℕ using (ℕ; suc; zero)

mutual
  ⟨1*0⟩ : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  ⟨1*0⟩ zero     0₂ ys = 0 1& ys
  ⟨1*0⟩ zero     (0< xs) ys = 0 1& 0< 0→⟨0?+0⟩ ys (H₀ xs) (⟨1*0⟩ (H₁ (T₀ xs)) (T₁ (T₀ xs)) ys)
  ⟨1*0⟩ (suc x₁) xs ys = suc₁ 0→⟨1+0?⟩ (⟨1*0⟩ x₁ xs ys) ys

  ⟨1*s⟩ : ℕ → 0≤ 𝔹₀ →  ℕ → 0≤ 𝔹₀ → 𝔹₁
  ⟨1*s⟩ zero     0₂      y₁ ys = suc y₁ 1& ys
  ⟨1*s⟩ zero     (0< xs) y₁ ys = suc₁ 0→⟨1+0⟩ y₁ ys (H₀ xs) (⟨1*s⟩ (H₁ (T₀ xs)) (T₁ (T₀ xs)) y₁ ys)
  ⟨1*s⟩ (suc x₁) xs      y₁ ys = 0 1& 0< 0→⟨1+1⟩ (H₁ zs) (T₁ zs) y₁ ys
    where
    zs : 𝔹₁
    zs = ⟨1*s⟩ x₁ xs y₁ ys

  ⟨1*1⟩ : ℕ → 0≤ 𝔹₀ → 𝔹₁ → 𝔹₁
  ⟨1*1⟩ zero     ys xs = ⟨1*0⟩ (H₁ xs) (T₁ xs) ys
  ⟨1*1⟩ (suc y₁) ys xs = ⟨1*s⟩ (H₁ xs) (T₁ xs) y₁ ys

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0₂         * ys = 0₂
(0< xs)    * 0₂ = 0₂
(0< B₀ xs) * (0< B₀ ys) = 0< B₀ (suc (H₀ xs ℕ.+ H₀ ys)) 0& ⟨1*1⟩ (H₁ (T₀ ys)) (T₁ (T₀ ys)) (T₀ xs)
(0< B₀ xs) * (0< B₁ ys) = 0< B₀ (H₀ xs) 0& ⟨1*1⟩ (H₁ ys) (T₁ ys) (T₀ xs)
(0< B₁ xs) * (0< B₀ ys) = 0< B₀ H₀ ys 0& ⟨1*1⟩ (H₁ (T₀ ys)) (T₁ (T₀ ys)) xs
(0< B₁ xs) * (0< B₁ ys) = 0< B₁ ⟨1*1⟩ (H₁ ys) (T₁ ys) xs
