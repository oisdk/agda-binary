{-# OPTIONS --without-K --safe #-}

module Data.Binary.Conversion where

open import Data.Binary.Definition
open import Data.Binary.Increment

open import Agda.Builtin.Nat using (Nat; suc; zero)
import Agda.Builtin.Nat as ℕ

⟦_⇑⟧ : Nat → 𝔹
⟦ zero  ⇑⟧ = 0ᵇ
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

⟦_⇓⟧ : 𝔹 → Nat
⟦ 0ᵇ ⇓⟧ = 0
⟦ 1ᵇ xs ⇓⟧ = 1 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2
⟦ 2ᵇ xs ⇓⟧ = 2 ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2
