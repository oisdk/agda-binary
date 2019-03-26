{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Operations.Semantics where

open import Data.Binary.Distrib.Definitions
open import Data.Binary.Distrib.Operations.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)

infixr 5 2*_
2*_ : ℕ → ℕ
2* x = x ℕ.+ x

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧ = 0
⟦ 2*s xs ⇓⟧ = 2* suc ⟦ xs ⇓⟧
⟦ s2* xs ⇓⟧ = suc (2* ⟦ xs ⇓⟧)

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
