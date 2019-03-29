{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Addition where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Operations.Unary
open import Data.Binary.Operations.Addition
open import Data.Binary.Proofs.Unary
open import Data.Binary.Proofs.Semantics
open import Data.Binary.Definitions
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function
open import Data.Nat.Reasoning

mutual
  add₀-homo : ∀ xs ys → ⟦ add O xs ys ⇓⟧⁺ ≡ ⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺
  add₀-homo 1ᵇ 1ᵇ = refl
  add₀-homo 1ᵇ (O ∷ ys) = refl
  add₀-homo 1ᵇ (I ∷ ys) = cong 2* (inc⁺⁺-homo ys) ⟨ trans ⟩ ℕ.+-suc (suc ⟦ ys ⇓⟧⁺) _
  add₀-homo (O ∷ xs) 1ᵇ = ℕ.+-comm 1 _
  add₀-homo (O ∷ xs) (O ∷ ys) = cong 2* (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺
  add₀-homo (O ∷ xs) (I ∷ ys) = cong suc (cong 2* (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺) ⟨ trans ⟩ sym (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) (2* ⟦ ys ⇓⟧⁺))
  add₀-homo (I ∷ xs) 1ᵇ = inc⁺⁺-homo (I ∷ xs) ⟨ trans ⟩ cong suc (ℕ.+-comm 1 _)
  add₀-homo (I ∷ xs) (O ∷ ys) = cong suc (cong 2* (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)
  add₀-homo (I ∷ xs) (I ∷ ys) = cong 2* (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)) _ ⟨ trans ⟩
                                cong suc (cong suc (2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺))) ⟨ trans ⟩
                                sym (cong suc (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) _))

  add₁-homo : ∀ xs ys → ⟦ add I xs ys ⇓⟧⁺ ≡ suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)
  add₁-homo 1ᵇ 1ᵇ = refl
  add₁-homo 1ᵇ (O ∷ ys) = cong 2* (inc⁺⁺-homo ys) ⟨ trans ⟩ ℕ.+-suc (suc ⟦ ys ⇓⟧⁺) _
  add₁-homo 1ᵇ (I ∷ ys) = cong suc (cong 2* (inc⁺⁺-homo ys) ⟨ trans ⟩ ℕ.+-suc (suc ⟦ ys ⇓⟧⁺) _)
  add₁-homo (O ∷ xs) 1ᵇ = cong 2* (inc⁺⁺-homo xs) ⟨ trans ⟩ (ℕ.+-suc (suc ⟦ xs ⇓⟧⁺) _ ⟨ trans ⟩ cong suc (ℕ.+-comm 1 _))
  add₁-homo (O ∷ xs) (O ∷ ys) = cong suc (cong 2* (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)
  add₁-homo (O ∷ xs) (I ∷ ys) = cong 2* (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)) _ ⟨ trans ⟩ (cong suc (cong suc ((2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺))) ⟨ trans ⟩ cong suc (sym (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) _)) ))
  add₁-homo (I ∷ xs) 1ᵇ = cong suc (cong 2* (inc⁺⁺-homo xs) ⟨ trans ⟩ cong suc (ℕ.+-suc ⟦ xs ⇓⟧⁺ _ ⟨ trans ⟩ ℕ.+-comm 1 _))
  add₁-homo (I ∷ xs) (O ∷ ys) = cong 2* (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)) _ ⟨ trans ⟩ cong suc (cong suc (2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)))
  add₁-homo (I ∷ xs) (I ∷ ys) = cong suc (cong 2* (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺) ) _ ⟨ trans ⟩ cong suc (cong suc (2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)) ⟨ trans ⟩ cong suc (sym (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) _)) ))

+-homo : ∀ xs ys → ⟦ xs + ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧
+-homo 0ᵇ ys = refl
+-homo (0< x) 0ᵇ = sym (ℕ.+-identityʳ _)
+-homo (0< xs) (0< ys) = add₀-homo xs ys
