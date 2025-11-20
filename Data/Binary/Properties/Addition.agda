{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Addition where

open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ
open import Data.Binary.Properties.Isomorphism
open import Data.Binary.Properties.Helpers
open import Data.Binary.Helpers


+-cong  : ∀ x y → ⟦ x + y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧
+₁-cong : ∀ x y → ⟦ 1+[ x + y ] ⇓⟧ ≡ 1 ℕ.+ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧
+₂-cong : ∀ x y → ⟦ 2+[ x + y ] ⇓⟧ ≡ 2 ℕ.+ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧

lemma₁ : ∀ x y → ⟦ 1+[  x + y ] ⇓⟧ ℕ.* 2 ≡ ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ (2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2)
lemma₁ x y =
  ⟦ 1+[ x + y ] ⇓⟧ ℕ.* 2               ≡⟨ cong (ℕ._* 2) (+₁-cong x y) ⟩
  2 ℕ.+ (⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧) ℕ.* 2      ≡⟨ cong (2 ℕ.+_ ) (+-*-distrib ⟦ x ⇓⟧ ⟦ y ⇓⟧ 2) ⟩
  2 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2  ≡⟨ cong (ℕ._+ (⟦ y ⇓⟧ ℕ.* 2)) (+-comm 2 (⟦ x ⇓⟧ ℕ.* 2)) ⟩
  ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ 2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2  ≡⟨ +-assoc (⟦ x ⇓⟧ ℕ.* 2) 2 (⟦ y ⇓⟧ ℕ.* 2) ⟩
  ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ (2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2) ∎

lemma₂ : ∀ x y → ⟦ 1+[ x + y ] ⇓⟧ ℕ.* 2 ≡ (1 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2) ℕ.+ (1 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2)
lemma₂ x y =
  ⟦ 1+[ x + y ] ⇓⟧ ℕ.* 2              ≡⟨ cong (ℕ._* 2) (+₁-cong x y) ⟩
  (1 ℕ.+ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧) ℕ.* 2     ≡⟨ +-*-distrib (1 ℕ.+ ⟦ x ⇓⟧) ⟦ y ⇓⟧ 2 ⟩
  2 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2 ≡˘⟨ +-suc (1 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2) (⟦ y ⇓⟧ ℕ.* 2) ⟩
  (1 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2) ℕ.+ (1 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2) ∎

lemma₃ : ∀ x y → ⟦ 2+[ x + y ] ⇓⟧ ℕ.* 2 ≡ 2 ℕ.+ (⟦ x ⇓⟧ ℕ.* 2 ℕ.+ (2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2))
lemma₃ x y =
  ⟦ 2+[ x + y ] ⇓⟧ ℕ.* 2                    ≡⟨ cong (ℕ._* 2) (+₂-cong x y) ⟩
  (2 ℕ.+ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧) ℕ.* 2           ≡˘⟨ cong (ℕ._* 2) (+-suc (1 ℕ.+ ⟦ x ⇓⟧) ⟦ y ⇓⟧) ⟩
  ((1 ℕ.+ ⟦ x ⇓⟧) ℕ.+ (1 ℕ.+ ⟦ y ⇓⟧)) ℕ.* 2 ≡⟨ +-*-distrib (1 ℕ.+ ⟦ x ⇓⟧) (1 ℕ.+ ⟦ y ⇓⟧) 2 ⟩
  2 ℕ.+ (⟦ x ⇓⟧ ℕ.* 2 ℕ.+ (2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2)) ∎

lemma₄ : ∀ x y → 2 ℕ.+ ⟦ x + y ⇓⟧ ℕ.* 2 ≡ 1 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ (1 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2)
lemma₄ x y =
  2 ℕ.+ ⟦ x + y ⇓⟧ ℕ.* 2                ≡⟨ cong (λ xy → 2 ℕ.+ xy ℕ.* 2) (+-cong x y) ⟩
  2 ℕ.+ (⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧) ℕ.* 2       ≡⟨ cong (2 ℕ.+_) (+-*-distrib ⟦ x ⇓⟧ ⟦ y ⇓⟧ 2) ⟩
  2 ℕ.+ (⟦ x ⇓⟧ ℕ.* 2 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2) ≡˘⟨ cong suc (+-suc (⟦ x ⇓⟧ ℕ.* 2) (⟦ y ⇓⟧ ℕ.* 2)) ⟩
  1 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2 ℕ.+ (1 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2) ∎

+₁-cong 0ᵇ y = inc-suc y
+₁-cong (1ᵇ x) 0ᵇ = cong (2 ℕ.+_) (sym (+-idʳ (⟦ x ⇓⟧ ℕ.* 2)))
+₁-cong (2ᵇ x) 0ᵇ = cong suc (cong (ℕ._* 2) (inc-suc x) ∙ cong (2 ℕ.+_) (sym (+-idʳ (⟦ x ⇓⟧ ℕ.* 2))))
+₁-cong (1ᵇ x) (1ᵇ y) = cong suc (lemma₂ x y)
+₁-cong (1ᵇ x) (2ᵇ y) = cong (2 ℕ.+_) (lemma₁ x y)
+₁-cong (2ᵇ x) (1ᵇ y) = cong (2 ℕ.+_) (lemma₂ x y)
+₁-cong (2ᵇ x) (2ᵇ y) = cong (1 ℕ.+_) (lemma₃ x y)

+₂-cong 0ᵇ 0ᵇ = refl
+₂-cong 0ᵇ (1ᵇ y) = cong (1 ℕ.+_) (cong (ℕ._* 2) (inc-suc y))
+₂-cong 0ᵇ (2ᵇ y) = cong (2 ℕ.+_) (cong (ℕ._* 2) (inc-suc y))
+₂-cong (1ᵇ x) 0ᵇ = cong (1 ℕ.+_) ((cong (ℕ._* 2) (inc-suc x)) ∙ cong (2 ℕ.+_) (sym (+-idʳ _)))
+₂-cong (2ᵇ x) 0ᵇ = cong (2 ℕ.+_) ((cong (ℕ._* 2) (inc-suc x)) ∙ cong (2 ℕ.+_) (sym (+-idʳ _)))
+₂-cong (1ᵇ x) (1ᵇ y) = cong (2 ℕ.+_ ) (lemma₂ x y)
+₂-cong (1ᵇ x) (2ᵇ y) = cong (1 ℕ.+_) (lemma₃ x y)
+₂-cong (2ᵇ x) (1ᵇ y) = cong (1 ℕ.+_) (lemma₃ x y ∙ +-suc (2 ℕ.+ ⟦ x ⇓⟧ ℕ.* 2) (1 ℕ.+ ⟦ y ⇓⟧ ℕ.* 2))
+₂-cong (2ᵇ x) (2ᵇ y) = cong (2 ℕ.+_) (lemma₃ x y)

+-cong 0ᵇ y = refl
+-cong (1ᵇ x) 0ᵇ = cong suc (sym (+-idʳ (⟦ x ⇓⟧ ℕ.* 2)))
+-cong (2ᵇ x) 0ᵇ = cong (λ r → suc (suc r)) (sym (+-idʳ (⟦ x ⇓⟧ ℕ.* 2)))
+-cong (1ᵇ x) (1ᵇ y) = lemma₄ x y
+-cong (1ᵇ x) (2ᵇ y) = cong suc (lemma₁ x y)
+-cong (2ᵇ x) (1ᵇ y) = cong suc (lemma₂ x y)
+-cong (2ᵇ x) (2ᵇ y) = cong (2 ℕ.+_) (lemma₁ x y)
