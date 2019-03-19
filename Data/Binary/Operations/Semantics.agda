{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Semantics where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0₂
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

mutual
  ⟦_⇓⟧≤ : 0≤ 𝔹₀ → ℕ
  ⟦ 0₂ ⇓⟧≤ = 0
  ⟦ 0< xs ⇓⟧≤ = ⟦ xs ⇓⟧₀

  ⟦_⇓⟧₁⁺¹ : 𝔹₁ → ℕ
  ⟦ x 1& xs ⇓⟧₁⁺¹ = 2 ℕ.^ suc x ℕ.* suc ⟦ xs ⇓⟧≤

  ⟦_⇓⟧₀ : 𝔹₀ → ℕ
  ⟦ x 0& xs ⇓⟧₀ = 2 ℕ.^ suc x ℕ.* ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ B₀ xs ⇓⟧⁺ = ⟦ xs ⇓⟧₀
⟦ B₁ xs ⇓⟧⁺ = ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0₂ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺
