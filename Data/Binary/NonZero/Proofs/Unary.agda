{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Proofs.Unary where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.NonZero.Operations.Unary
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ

inc″-homo : ∀ xs → ⟦ inc″ xs ⇓⟧⁺ ≡ suc ⟦ xs ⇓⟧⁺
inc″-homo 1⁺ = refl
inc″-homo (0⁺∷ xs) = refl
inc″-homo (1⁺∷ xs) =
  begin
    2* ⟦ inc″ xs ⇓⟧⁺
  ≡⟨ cong 2*_ (inc″-homo xs) ⟩
    2* (suc ⟦ xs ⇓⟧⁺)
  ≡⟨⟩
    (suc ⟦ xs ⇓⟧⁺) ℕ.+ suc ⟦ xs ⇓⟧⁺
  ≡⟨ ℕ.+-suc (suc ⟦ xs ⇓⟧⁺) ⟦ xs ⇓⟧⁺ ⟩
    suc (suc (2* ⟦ xs ⇓⟧⁺))
  ∎

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0ᵇ = refl
inc-homo (0< xs) = inc″-homo xs
