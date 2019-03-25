{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Semantics where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary

2*_ : ℕ → ℕ
2* x = x ℕ.+ x

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ 1⁺ ⇓⟧⁺ = 1
⟦ 0⁺∷ xs ⇓⟧⁺ = 2* ⟦ xs ⇓⟧⁺
⟦ 1⁺∷ xs ⇓⟧⁺ = suc (2* ⟦ xs ⇓⟧⁺)

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
