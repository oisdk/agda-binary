{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Semantics where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0₂
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

infixr 5 2*_
2*_ : ℕ → ℕ
2* x = x ℕ.+ x

infixr 5 2^_*_
2^_*_ : ℕ → ℕ → ℕ
2^ zero  * x = x
2^ suc n * x = 2* 2^ n * x

⟨2^_*_⟩−1 : ℕ → ℕ → ℕ
⟨2^ zero  * x ⟩−1 = x
⟨2^ suc n * x ⟩−1 = suc (2* ⟨2^ n * x ⟩−1)

mutual
  ⟦_⇓⟧≤ : 0≤ 𝔹₀ → ℕ
  ⟦ 0₂ ⇓⟧≤ = 0
  ⟦ 0< xs ⇓⟧≤ = ⟦ xs ⇓⟧₀

  ⟦_⇓⟧₁ : 𝔹₁ → ℕ
  ⟦ xs ⇓⟧₁ = suc (2* ⟨2^ H₁ xs * ⟦ T₁ xs ⇓⟧≤ ⟩−1)

  ⟦_⇓⟧₀ : 𝔹₀ → ℕ
  ⟦ xs ⇓⟧₀ = 2* 2^ H₀ xs * ⟦ T₀ xs ⇓⟧₁

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ B₀ xs ⇓⟧⁺ = ⟦ xs ⇓⟧₀
⟦ B₁ xs ⇓⟧⁺ = ⟦ xs ⇓⟧₁

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0₂ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺
