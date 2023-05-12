{-# OPTIONS --cubical #-}

module Data.Binary.Properties.Multiplication where

open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Properties.Addition using (+-cong)
open import Data.Binary.Multiplication
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ

open import Data.Binary.Properties.Isomorphism

open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Double

double-cong : ∀ xs → ⟦ double xs ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* 2
double-cong 0ᵇ i = zero
double-cong (1ᵇ xs) i = 2 ℕ.+ double-cong xs i ℕ.* 2
double-cong (2ᵇ xs) i = ⟦ 2ᵇ 1ᵇ xs ⇓⟧

double-plus : ∀ x → x ℕ.+ x ≡ x ℕ.* 2
double-plus x = cong (x ℕ.+_) (sym (+-idʳ x)) ∙ *-comm 2 x

lemma₁ : ∀ x y → x ℕ.* y ℕ.* 2 ≡ y ℕ.* 2 ℕ.* x
lemma₁ x y =
  x ℕ.* y ℕ.* 2 ≡⟨ *-assoc x y 2 ⟩
  x ℕ.* (y ℕ.* 2) ≡⟨ *-comm x (y ℕ.* 2) ⟩
  y ℕ.* 2 ℕ.* x ∎

lemma₂ : ∀ x y → (x ℕ.+ x ℕ.* y) ℕ.* 2 ≡ x ℕ.+ (x ℕ.+ y ℕ.* 2 ℕ.* x)
lemma₂ x y =
  (x ℕ.+ x ℕ.* y) ℕ.* 2 ≡⟨ +-*-distrib x (x ℕ.* y) 2 ⟩
  x ℕ.* 2 ℕ.+ x ℕ.* y ℕ.* 2 ≡⟨ cong₂ ℕ._+_ (sym (double-plus x)) (lemma₁ x y) ⟩
  x ℕ.+ x ℕ.+ y ℕ.* 2 ℕ.* x ≡⟨ +-assoc x x (y ℕ.* 2 ℕ.* x) ⟩
  x ℕ.+ (x ℕ.+ y ℕ.* 2 ℕ.* x) ∎

*-cong : ∀ xs ys → ⟦ xs * ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.* ⟦ ys ⇓⟧
*-cong 0ᵇ ys = refl
*-cong (1ᵇ xs) ys =
  ⟦ ys + double (ys * xs) ⇓⟧ ≡⟨ +-cong ys (double (ys * xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ double (ys * xs) ⇓⟧ ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_)  (double-cong (ys * xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ ys * xs ⇓⟧ ℕ.* 2 ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_)  (cong (ℕ._* 2) (*-cong ys xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ ys ⇓⟧ ℕ.* ⟦ xs ⇓⟧ ℕ.* 2 ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_) (lemma₁ ⟦ ys ⇓⟧ ⟦ xs ⇓⟧) ⟩
  ⟦ ys ⇓⟧ ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.* ⟦ ys ⇓⟧ ∎
*-cong (2ᵇ xs) ys =
  ⟦ double (ys + ys * xs) ⇓⟧ ≡⟨ double-cong (ys + ys * xs) ⟩
  ⟦ ys + ys * xs ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._* 2) (+-cong ys (ys * xs)) ⟩
  (⟦ ys ⇓⟧ ℕ.+ ⟦ ys * xs ⇓⟧) ℕ.* 2 ≡⟨ cong (ℕ._* 2) (cong (⟦ ys ⇓⟧ ℕ.+_) (*-cong ys xs)) ⟩
  (⟦ ys ⇓⟧ ℕ.+ ⟦ ys ⇓⟧ ℕ.* ⟦ xs ⇓⟧) ℕ.* 2 ≡⟨ lemma₂ ⟦ ys ⇓⟧ ⟦ xs ⇓⟧  ⟩
  ⟦ ys ⇓⟧ ℕ.+ (⟦ ys ⇓⟧ ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.* ⟦ ys ⇓⟧) ∎
