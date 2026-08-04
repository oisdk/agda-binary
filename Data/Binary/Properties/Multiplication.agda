{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Properties.Addition using (+-cong)
open import Data.Binary.Multiplication
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ

open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Properties.Double
open import Data.Binary.Double

+2×-cong : ∀ x y → ⟦ x +2× y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧ ℕ.* 2
+2×-cong 0ᵇ     y = double-cong y
+2×-cong (1ᵇ x) y = cong (λ z → suc (z ℕ.* 2)) (+-cong x y) ∙ cong suc (+-*-distrib ⟦ x ⇓⟧ ⟦ y ⇓⟧ 2)
+2×-cong (2ᵇ x) y = cong (λ z → 2 ℕ.+ z ℕ.* 2) (+-cong x y) ∙ cong (2 ℕ.+_) (+-*-distrib ⟦ x ⇓⟧ ⟦ y ⇓⟧ 2)

shuffle : ∀ x y z → (x ℕ.+ y) ℕ.+ z ≡ y ℕ.+ (x ℕ.+ z)
shuffle x y z = cong (ℕ._+ z) (+-comm x y) ∙ +-assoc y x z

4ab : ∀ a b → a ℕ.* b ℕ.* 2 ℕ.* 2 ≡ a ℕ.* 2 ℕ.* (b ℕ.* 2)
4ab a b =
  a ℕ.* b ℕ.* 2 ℕ.* 2     ≡⟨ *-assoc (a ℕ.* b) 2 2 ⟩
  a ℕ.* b ℕ.* 4           ≡⟨ *-assoc a b 4 ⟩
  a ℕ.* (b ℕ.* 4)         ≡˘⟨ cong (a ℕ.*_) (*-assoc b 2 2) ⟩
  a ℕ.* (b ℕ.* 2 ℕ.* 2)   ≡⟨ cong (a ℕ.*_) (*-comm (b ℕ.* 2) 2) ⟩
  a ℕ.* (2 ℕ.* (b ℕ.* 2)) ≡˘⟨ *-assoc a 2 (b ℕ.* 2) ⟩
  a ℕ.* 2 ℕ.* (b ℕ.* 2)   ∎

exp₁₁ : ∀ a b → suc (((a ℕ.+ b) ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2) ≡ suc (a ℕ.* 2) ℕ.* suc (b ℕ.* 2)
exp₁₁ a b =
  suc (((a ℕ.+ b) ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2)                   ≡⟨ cong suc (+-*-distrib (a ℕ.+ b) (a ℕ.* b ℕ.* 2) 2) ⟩
  suc ((a ℕ.+ b) ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)               ≡⟨ cong (λ z → suc (z ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)) (+-*-distrib a b 2) ⟩
  suc (a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)           ≡⟨ cong (λ z → suc (a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ z)) (4ab a b) ⟩
  suc (a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))         ≡⟨ cong suc (shuffle (a ℕ.* 2) (b ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  suc (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2)))       ≡⟨ cong (λ z → suc (b ℕ.* 2 ℕ.+ z)) (*-suc (a ℕ.* 2) (b ℕ.* 2)) ⟩
  suc (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (b ℕ.* 2))                 ∎

exp₁₂ : ∀ a b → 2 ℕ.+ (b ℕ.+ (a ℕ.+ a ℕ.* b) ℕ.* 2) ℕ.* 2 ≡ suc (a ℕ.* 2) ℕ.* (2 ℕ.+ b ℕ.* 2)
exp₁₂ a b =
  2 ℕ.+ (b ℕ.+ (a ℕ.+ a ℕ.* b) ℕ.* 2) ℕ.* 2                                 ≡⟨ cong (2 ℕ.+_) (+-*-distrib b ((a ℕ.+ a ℕ.* b) ℕ.* 2) 2) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.+ a ℕ.* b) ℕ.* 2 ℕ.* 2)                           ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ z ℕ.* 2)) (+-*-distrib a (a ℕ.* b) 2) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2)                     ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ z)) (+-*-distrib (a ℕ.* 2) (a ℕ.* b ℕ.* 2) 2) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2))               ≡˘⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ (z ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2))) (double-plus (a ℕ.* 2)) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2))         ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ z))) (4ab a b) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2)))       ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ z)) (+-assoc (a ℕ.* 2) (a ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))))     ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ z))) (*-suc (a ℕ.* 2) (b ℕ.* 2)) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (b ℕ.* 2)))               ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ z)) (*-suc (a ℕ.* 2) (suc (b ℕ.* 2))) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (suc (b ℕ.* 2)))                       ∎

exp₂₁ : ∀ a b → 2 ℕ.+ (a ℕ.+ (b ℕ.+ a ℕ.* b) ℕ.* 2) ℕ.* 2 ≡ (2 ℕ.+ a ℕ.* 2) ℕ.* suc (b ℕ.* 2)
exp₂₁ a b =
  2 ℕ.+ (a ℕ.+ (b ℕ.+ a ℕ.* b) ℕ.* 2) ℕ.* 2                                   ≡⟨ cong (2 ℕ.+_) (+-*-distrib a ((b ℕ.+ a ℕ.* b) ℕ.* 2) 2) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.+ a ℕ.* b) ℕ.* 2 ℕ.* 2)                             ≡⟨ cong (λ z → 2 ℕ.+ (a ℕ.* 2 ℕ.+ z ℕ.* 2)) (+-*-distrib b (a ℕ.* b) 2) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2)                       ≡⟨ cong (λ z → 2 ℕ.+ (a ℕ.* 2 ℕ.+ z)) (+-*-distrib (b ℕ.* 2) (a ℕ.* b ℕ.* 2) 2) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2))                 ≡˘⟨ cong (λ z → 2 ℕ.+ (a ℕ.* 2 ℕ.+ (z ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2))) (double-plus (b ℕ.* 2)) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2))           ≡⟨ cong (λ z → 2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ z))) (4ab a b) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2)))         ≡⟨ cong (λ z → 2 ℕ.+ (a ℕ.* 2 ℕ.+ z)) (+-assoc (b ℕ.* 2) (b ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))))       ≡˘⟨ cong (2 ℕ.+_) (+-assoc (a ℕ.* 2) (b ℕ.* 2) (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  2 ℕ.+ (a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2)))         ≡⟨ cong (2 ℕ.+_) (shuffle (a ℕ.* 2) (b ℕ.* 2) (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))))       ≡˘⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ z)) (+-assoc (a ℕ.* 2) (b ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2)))         ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ z)) (shuffle (a ℕ.* 2) (b ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))))       ≡⟨ cong (λ z → 2 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ z))) (*-suc (a ℕ.* 2) (b ℕ.* 2)) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (b ℕ.* 2)))                 ≡˘⟨ cong suc (+-suc (b ℕ.* 2) (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (b ℕ.* 2))) ⟩
  suc (b ℕ.* 2 ℕ.+ suc (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (b ℕ.* 2)))               ∎

exp₂₂ : ∀ a b → 2 ℕ.+ suc (((a ℕ.+ b) ℕ.+ a ℕ.* b) ℕ.* 2) ℕ.* 2 ≡ (2 ℕ.+ a ℕ.* 2) ℕ.* (2 ℕ.+ b ℕ.* 2)
exp₂₂ a b =
  2 ℕ.+ suc (((a ℕ.+ b) ℕ.+ a ℕ.* b) ℕ.* 2) ℕ.* 2                                     ≡⟨ cong (λ z → 4 ℕ.+ z ℕ.* 2) (+-*-distrib (a ℕ.+ b) (a ℕ.* b) 2) ⟩
  4 ℕ.+ ((a ℕ.+ b) ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2                                     ≡⟨ cong (λ z → 4 ℕ.+ (z ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2) (+-*-distrib a b 2) ⟩
  4 ℕ.+ (a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2) ℕ.* 2                                 ≡⟨ cong (4 ℕ.+_) (+-*-distrib (a ℕ.* 2 ℕ.+ b ℕ.* 2) (a ℕ.* b ℕ.* 2) 2) ⟩
  4 ℕ.+ ((a ℕ.* 2 ℕ.+ b ℕ.* 2) ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)                         ≡⟨ cong (λ z → 4 ℕ.+ (z ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)) (+-*-distrib (a ℕ.* 2) (b ℕ.* 2) 2) ⟩
  4 ℕ.+ (a ℕ.* 2 ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)                     ≡˘⟨ cong (λ z → 4 ℕ.+ (z ℕ.+ b ℕ.* 2 ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)) (double-plus (a ℕ.* 2)) ⟩
  4 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.* 2 ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)               ≡˘⟨ cong (λ z → 4 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ z ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)) (double-plus (b ℕ.* 2)) ⟩
  4 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2) ℕ.+ a ℕ.* b ℕ.* 2 ℕ.* 2)       ≡⟨ cong (λ z → 4 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2) ℕ.+ z)) (4ab a b) ⟩
  4 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2) ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))     ≡⟨ cong (4 ℕ.+_) (shuffle (a ℕ.* 2 ℕ.+ a ℕ.* 2) (b ℕ.* 2 ℕ.+ b ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  4 ℕ.+ (b ℕ.* 2 ℕ.+ b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2)))     ≡⟨ cong (4 ℕ.+_) (+-assoc (b ℕ.* 2) (b ℕ.* 2) (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))))   ≡⟨ cong (λ z → 4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ z))) (+-assoc (a ℕ.* 2) (a ℕ.* 2) (a ℕ.* 2 ℕ.* (b ℕ.* 2))) ⟩
  4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* (b ℕ.* 2))))) ≡⟨ cong (λ z → 4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ z)))) (*-suc (a ℕ.* 2) (b ℕ.* 2)) ⟩
  4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ (a ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (b ℕ.* 2))))           ≡⟨ cong (λ z → 4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ z))) (*-suc (a ℕ.* 2) (suc (b ℕ.* 2))) ⟩
  4 ℕ.+ (b ℕ.* 2 ℕ.+ (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (suc (b ℕ.* 2))))                   ≡˘⟨ cong (λ z → 3 ℕ.+ z) (+-suc (b ℕ.* 2) (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (suc (b ℕ.* 2)))) ⟩
  3 ℕ.+ (b ℕ.* 2 ℕ.+ suc (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (suc (b ℕ.* 2))))               ≡˘⟨ cong (λ z → 2 ℕ.+ z) (+-suc (b ℕ.* 2) (suc (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (suc (b ℕ.* 2))))) ⟩
  2 ℕ.+ (b ℕ.* 2 ℕ.+ suc (suc (b ℕ.* 2 ℕ.+ a ℕ.* 2 ℕ.* suc (suc (b ℕ.* 2)))))         ∎

*-cong : ∀ xs ys → ⟦ xs * ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* ⟦ ys ⇓⟧
*-cong 0ᵇ      ys      = refl
*-cong (1ᵇ xs) 0ᵇ      = sym (*-zeroʳ ⟦ 1ᵇ xs ⇓⟧)
*-cong (2ᵇ xs) 0ᵇ      = sym (*-zeroʳ ⟦ 2ᵇ xs ⇓⟧)
*-cong (1ᵇ xs) (1ᵇ ys) =
  cong (λ z → suc (z ℕ.* 2))
    (+2×-cong (xs + ys) (xs * ys) ∙ cong₂ ℕ._+_ (+-cong xs ys) (cong (ℕ._* 2) (*-cong xs ys)))
  ∙ exp₁₁ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
*-cong (1ᵇ xs) (2ᵇ ys) =
  cong (λ z → 2 ℕ.+ z ℕ.* 2)
    (+2×-cong ys (xs + xs * ys) ∙ cong (λ z → ⟦ ys ⇓⟧ ℕ.+ z ℕ.* 2) (+-cong xs (xs * ys) ∙ cong (⟦ xs ⇓⟧ ℕ.+_) (*-cong xs ys)))
  ∙ exp₁₂ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
*-cong (2ᵇ xs) (1ᵇ ys) =
  cong (λ z → 2 ℕ.+ z ℕ.* 2)
    (+2×-cong xs (ys + xs * ys) ∙ cong (λ z → ⟦ xs ⇓⟧ ℕ.+ z ℕ.* 2) (+-cong ys (xs * ys) ∙ cong (⟦ ys ⇓⟧ ℕ.+_) (*-cong xs ys)))
  ∙ exp₂₁ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
*-cong (2ᵇ xs) (2ᵇ ys) =
  cong (λ z → 2 ℕ.+ suc (z ℕ.* 2) ℕ.* 2)
    (+-cong (xs + ys) (xs * ys) ∙ cong₂ ℕ._+_ (+-cong xs ys) (*-cong xs ys))
  ∙ exp₂₂ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
