{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Operations.Semantics where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Unary
open import Data.List.Kleene using (foldr⋆)
open import Data.Maybe as Maybe using (maybe)

2*_ : ℕ → ℕ
2* x = x ℕ.+ x

_∷⇓_ : Bit → ℕ → ℕ
O ∷⇓ xs = 2* xs
I ∷⇓ xs = suc (2* xs)

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦_⇓⟧⁺ = foldr⋆ _∷⇓_ 1

⟦_⇓⟧ : 𝔹 → ℕ
⟦_⇓⟧ = maybe ⟦_⇓⟧⁺ 0

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧
