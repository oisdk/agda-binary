{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Multiplication where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition
open import Data.Nat as ℕ using (ℕ; suc; zero)

mutual
  ⟨1*0⟩ : ℕ → 0≤ 𝔹₀ → 0≤ 𝔹₀ → 𝔹₁
  ⟨1*0⟩ zero 0₂ ys = 0 1& ys
  ⟨1*0⟩ zero (0< x₀ 0& x₁ 1& xs) ys = 0 1& 0< 0→⟨0?+0⟩ ys x₀ (⟨1*0⟩ x₁ xs ys)
  ⟨1*0⟩ (suc x₁) xs ys with ⟨1*0⟩ x₁ xs ys
  ... | z₁ 1& zs = 0→⟨1+0?⟩ 1 z₁ zs ys

  ⟨1*s⟩ : ℕ → 0≤ 𝔹₀ →  ℕ → 0≤ 𝔹₀ → 𝔹₁
  ⟨1*s⟩ zero 0₂ y₁ ys                  = suc y₁ 1& ys
  ⟨1*s⟩ zero (0< x₀ 0& x₁ 1& xs) y₁ ys = 0→⟨1+0⟩ 1 y₁ ys x₀ (⟨1*s⟩ x₁ xs y₁ ys)
  ⟨1*s⟩ (suc x₁) xs y₁ ys with ⟨1*s⟩ x₁ xs y₁ ys
  ... | z₁ 1& zs = 0 1& 0< 0→⟨1+1⟩ 0 z₁ zs y₁ ys

  ⟨1*1⟩ : 𝔹₁ → 𝔹₁ → 𝔹₁
  ⟨1*1⟩ (x₁ 1& xs) (zero   1& ys) = ⟨1*0⟩ x₁ xs ys
  ⟨1*1⟩ (x₁ 1& xs) (suc y₁ 1& ys) = ⟨1*s⟩ x₁ xs y₁ ys

infixl 7 _*_
_*_ : 𝔹 → 𝔹 → 𝔹
0₂               * ys = 0₂
(0< xs)          * 0₂ = 0₂
(0< B₀ x₀ 0& xs) * (0< B₀ y₀ 0& ys) = 0< B₀ (suc (x₀ ℕ.+ y₀)) 0& ⟨1*1⟩ xs ys
(0< B₀ x₀ 0& xs) * (0<       B₁ ys) = 0< B₀ x₀ 0& ⟨1*1⟩ xs ys
(0<       B₁ xs) * (0< B₀ y₀ 0& ys) = 0< B₀ y₀ 0& ⟨1*1⟩ xs ys
(0<       B₁ xs) * (0<       B₁ ys) = 0< B₁ ⟨1*1⟩ xs ys
