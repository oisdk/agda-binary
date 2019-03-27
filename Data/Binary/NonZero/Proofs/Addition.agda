{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Proofs.Addition where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.NonZero.Operations.Unary
open import Data.Binary.NonZero.Operations.Addition
open import Data.Binary.NonZero.Proofs.Unary
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics
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

mutual
  add₀-homo : ∀ xs ys → ⟦ add₀ xs ys ⇓⟧⁺ ≡ ⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺
  add₀-homo 1⁺ 1⁺ = refl
  add₀-homo 1⁺ (0⁺∷ ys) = refl
  add₀-homo 1⁺ (1⁺∷ ys) = cong 2*_ (inc″-homo ys) ⟨ trans ⟩ ℕ.+-suc (suc ⟦ ys ⇓⟧⁺) _
  add₀-homo (0⁺∷ xs) 1⁺ = ℕ.+-comm 1 _
  add₀-homo (0⁺∷ xs) (0⁺∷ ys) = cong 2*_ (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺
  add₀-homo (0⁺∷ xs) (1⁺∷ ys) = cong suc (cong 2*_ (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺) ⟨ trans ⟩ sym (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) (2* ⟦ ys ⇓⟧⁺))
  add₀-homo (1⁺∷ xs) 1⁺ = inc″-homo (1⁺∷ xs) ⟨ trans ⟩ cong suc (ℕ.+-comm 1 _)
  add₀-homo (1⁺∷ xs) (0⁺∷ ys) = cong suc (cong 2*_ (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)
  add₀-homo (1⁺∷ xs) (1⁺∷ ys) = cong 2*_ (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)) _ ⟨ trans ⟩
                                cong suc (cong suc (2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺))) ⟨ trans ⟩
                                sym (cong suc (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) _))

  add₁-homo : ∀ xs ys → ⟦ add₁ xs ys ⇓⟧⁺ ≡ suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)
  add₁-homo 1⁺ 1⁺ = refl
  add₁-homo 1⁺ (0⁺∷ ys) = cong 2*_ (inc″-homo ys) ⟨ trans ⟩ ℕ.+-suc (suc ⟦ ys ⇓⟧⁺) _
  add₁-homo 1⁺ (1⁺∷ ys) = cong suc (cong 2*_ (inc″-homo ys) ⟨ trans ⟩ ℕ.+-suc (suc ⟦ ys ⇓⟧⁺) _)
  add₁-homo (0⁺∷ xs) 1⁺ = cong 2*_ (inc″-homo xs) ⟨ trans ⟩ (ℕ.+-suc (suc ⟦ xs ⇓⟧⁺) _ ⟨ trans ⟩ cong suc (ℕ.+-comm 1 _))
  add₁-homo (0⁺∷ xs) (0⁺∷ ys) = cong suc (cong 2*_ (add₀-homo xs ys) ⟨ trans ⟩ 2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)
  add₁-homo (0⁺∷ xs) (1⁺∷ ys) = cong 2*_ (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)) _ ⟨ trans ⟩ (cong suc (cong suc ((2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺))) ⟨ trans ⟩ cong suc (sym (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) _)) ))
  add₁-homo (1⁺∷ xs) 1⁺ = cong suc (cong 2*_ (inc″-homo xs) ⟨ trans ⟩ cong suc (ℕ.+-suc ⟦ xs ⇓⟧⁺ _ ⟨ trans ⟩ ℕ.+-comm 1 _))
  add₁-homo (1⁺∷ xs) (0⁺∷ ys) = cong 2*_ (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺)) _ ⟨ trans ⟩ cong suc (cong suc (2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)))
  add₁-homo (1⁺∷ xs) (1⁺∷ ys) = cong suc (cong 2*_ (add₁-homo xs ys) ⟨ trans ⟩ (ℕ.+-suc (suc (⟦ xs ⇓⟧⁺ ℕ.+ ⟦ ys ⇓⟧⁺) ) _ ⟨ trans ⟩ cong suc (cong suc (2*-distrib ⟦ xs ⇓⟧⁺ ⟦ ys ⇓⟧⁺)) ⟨ trans ⟩ cong suc (sym (ℕ.+-suc (2* ⟦ xs ⇓⟧⁺) _)) ))

+-homo : ∀ xs ys → ⟦ xs + ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧
+-homo 0ᵇ ys = refl
+-homo (0< x) 0ᵇ = sym (ℕ.+-identityʳ _)
+-homo (0< xs) (0< ys) = add₀-homo xs ys
