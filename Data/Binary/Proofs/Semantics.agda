{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Semantics where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Operations.Unary
open import Data.Binary.Proofs.Unary
open import Data.Binary.Definitions
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function
open import Data.Nat.Reasoning

2*-distrib : ∀ x y → 2* (x ℕ.+ y) ≡ 2* x ℕ.+ 2* y
2*-distrib x y =
  begin
    2* (x ℕ.+ y)
  ≡⟨⟩
    (x ℕ.+ y) ℕ.+ (x ℕ.+ y)
  ≡⟨ ℕ.+-assoc x y (x ℕ.+ y)  ⟩
    x ℕ.+ (y ℕ.+ (x ℕ.+ y))
  ≡⟨ x +≫ ℕ.+-comm y (x ℕ.+ y) ⟩
    x ℕ.+ ((x ℕ.+ y) ℕ.+ y)
  ≡⟨ x +≫ ℕ.+-assoc x y y ⟩
    x ℕ.+ (x ℕ.+ (y ℕ.+ y))
  ≡˘⟨ ℕ.+-assoc x x _ ⟩
    2* x ℕ.+ 2* y
  ∎

s2*-distrib : ∀ x y → I ∷⇓ (x ℕ.+ y) ≡ suc (2* x ℕ.+ 2* y)
s2*-distrib x y = cong suc (2*-distrib x y)
