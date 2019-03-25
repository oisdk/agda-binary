{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Derived where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality

open import Data.Binary.Definitions
open import Data.Binary.Proofs.Addition using (+-homo)
open import Data.Binary.Proofs.Multiplication using (*-homo)
open import Data.Binary.Proofs.Unary using (inc-homo)
open import Data.Binary.Proofs.Semantics using (𝔹↔ℕ)
open import Data.Binary.Operations.Multiplication using (_*_)
open import Data.Binary.Operations.Addition       using (_+_)
open import Data.Binary.Operations.Semantics      using (⟦_⇓⟧)
open import Function.Bijection
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Nat.Reasoning

open Bijection 𝔹↔ℕ

import Data.Nat.Properties as ℕ

open import Function

+-comm : ∀ x y → x + y ≡ y + x
+-comm x y = injective (+-homo x y ⟨ trans ⟩
                        ℕ.+-comm ⟦ x ⇓⟧ ⟦ y ⇓⟧ ⟨ trans ⟩
                        sym (+-homo y x))

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc x y z = injective $
  begin
    ⟦ (x + y) + z ⇓⟧
  ≡⟨ +-homo (x + y) z ⟩
    ⟦ x + y ⇓⟧ ℕ.+ ⟦ z ⇓⟧
  ≡⟨ ⟦ z ⇓⟧ ≪+ +-homo x y ⟩
    ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧ ℕ.+ ⟦ z ⇓⟧
  ≡⟨ ℕ.+-assoc ⟦ x ⇓⟧ ⟦ y ⇓⟧ ⟦ z ⇓⟧ ⟩
    ⟦ x ⇓⟧ ℕ.+ (⟦ y ⇓⟧ ℕ.+ ⟦ z ⇓⟧)
  ≡⟨ +-homo x () ⟩
    ⟦ x + y ⇓⟧ ℕ.+ ⟦ z ⇓⟧
  ≡⟨ ⟦ z ⇓⟧ ≪+ +-homo x y ⟩
  ≡⟨ {!!} ⟩
    ⟦ x + (y + z) ⇓⟧
  ∎


