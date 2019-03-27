{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Semantics where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary
import Data.List as List

2*_ : ℕ → ℕ
2* x = x ℕ.+ x
{-# INLINE 2*_ #-}

_∷⇓_ : Bit → ℕ → ℕ
O ∷⇓ xs = 2* xs
I ∷⇓ xs = suc (2* xs)
{-# INLINE _∷⇓_ #-}

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦_⇓⟧⁺ = List.foldr _∷⇓_ 1
{-# INLINE ⟦_⇓⟧⁺ #-}
-- ⟦ 1⁺ ⇓⟧⁺ = 1
-- ⟦ 0⁺∷ xs ⇓⟧⁺ = 2* ⟦ xs ⇓⟧⁺
-- ⟦ 1⁺∷ xs ⇓⟧⁺ = suc (2* ⟦ xs ⇓⟧⁺)

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0ᵇ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
