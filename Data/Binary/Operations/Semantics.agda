{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Semantics where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0₂
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

2^_+1 : ℕ → ℕ
2^ zero  +1 = 2
2^ suc n +1 = 2 ℕ.* 2^ n +1

mutual
  ⟦_⇓⟧≤ : 0≤ 𝔹₀ → ℕ
  ⟦ 0₂ ⇓⟧≤ = 0
  ⟦ 0< xs ⇓⟧≤ = ⟦ xs ⇓⟧₀

  ⟦_⇓⟧₁⁺¹ : 𝔹₁ → ℕ
  ⟦ xs ⇓⟧₁⁺¹ = 2^ H₁ xs +1 ℕ.* suc ⟦ T₁ xs ⇓⟧≤

  ⟦_⇓⟧₀ : 𝔹₀ → ℕ
  ⟦ xs ⇓⟧₀ = 2^ H₀ xs +1 ℕ.* ℕ.pred ⟦ T₀ xs ⇓⟧₁⁺¹

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ B₀ xs ⇓⟧⁺ = ⟦ xs ⇓⟧₀
⟦ B₁ xs ⇓⟧⁺ = ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0₂ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺
