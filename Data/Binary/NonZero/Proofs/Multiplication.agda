{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Proofs.Multiplication where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.NonZero.Operations.Unary
open import Data.Binary.NonZero.Operations.Addition
open import Data.Binary.NonZero.Operations.Multiplication
open import Data.Binary.NonZero.Proofs.Unary
open import Data.Binary.NonZero.Proofs.Addition
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function
open import Data.Nat.Reasoning

mul-homo : ∀ xs ys → ⟦ mul xs ys ⇓⟧⁺ ≡ ⟦ xs ⇓⟧⁺ ℕ.* ⟦ ys ⇓⟧⁺
mul-homo 1⁺ ys = sym (ℕ.+-identityʳ _)
mul-homo (0⁺∷ xs) ys = cong 2*_ (mul-homo xs ys) ⟨ trans ⟩ sym (ℕ.*-distribʳ-+ ⟦ ys ⇓⟧⁺ ⟦ xs ⇓⟧⁺ _)
mul-homo (1⁺∷ xs) ys =
  begin
    ⟦ add₀ (0⁺∷ mul ys xs) ys ⇓⟧⁺
  ≡⟨ add₀-homo (0⁺∷ mul ys xs) ys ⟩
    2* ⟦ mul ys xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺
  ≡⟨ ⟦ ys ⇓⟧⁺ ≪+ cong 2*_ (mul-homo ys xs) ⟩
    2* (⟦ ys ⇓⟧⁺ ℕ.* ⟦ xs ⇓⟧⁺) ℕ.+ ⟦ ys ⇓⟧⁺
  ≡⟨ ℕ.+-comm _ ⟦ ys ⇓⟧⁺ ⟩
    ⟦ ys ⇓⟧⁺ ℕ.+ 2* (⟦ ys ⇓⟧⁺ ℕ.* ⟦ xs ⇓⟧⁺)
  ≡˘⟨ ⟦ ys ⇓⟧⁺ +≫ ℕ.*-distribˡ-+ ⟦ ys ⇓⟧⁺ _ _ ⟩
    ⟦ ys ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺ ℕ.* (2* ⟦ xs ⇓⟧⁺)
  ≡⟨ ⟦ ys ⇓⟧⁺ +≫ ℕ.*-comm ⟦ ys ⇓⟧⁺ _ ⟩
    ⟦ ys ⇓⟧⁺ ℕ.+ (2* ⟦ xs ⇓⟧⁺) ℕ.* ⟦ ys ⇓⟧⁺
  ∎

*-homo : ∀ xs ys → ⟦ xs * ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* ⟦ ys ⇓⟧
*-homo 0ᵇ ys = refl
*-homo (0< x) 0ᵇ = sym (ℕ.*-zeroʳ ⟦ x ⇓⟧⁺)
*-homo (0< xs) (0< ys) = mul-homo xs ys
