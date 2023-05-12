{-# OPTIONS --cubical #-}

module Data.Binary.Properties.Helpers where

private variable A B : Set

open import Cubical.Foundations.Everything
  using (_≡_; cong; refl; _∙_; Iso; sym; cong₂)
  public

open Iso public

import Agda.Builtin.Nat as ℕ
open import Data.Binary.Helpers

infixr 2 ≡˘⟨⟩-syntax _≡⟨⟩_ ≡⟨∙⟩-syntax

≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≡ z → y ≡ x → x ≡ z
≡˘⟨⟩-syntax _ y≡z y≡x = sym y≡x ∙ y≡z

syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨∙⟩-syntax _ y≡z x≡y = x≡y ∙ y≡z

syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_≡⟨⟩_ : ∀ (x : A) {y} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infix 2.5 _∎
_∎ : (x : A) → x ≡ x
_∎ x = refl

+-suc : ∀ x y → x ℕ.+ suc y ≡ suc (x ℕ.+ y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-idʳ : ∀ x → x ℕ.+ 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-comm : ∀ x y → x ℕ.+ y ≡ y ℕ.+ x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ∙ cong suc (+-comm x y)

+-assoc : ∀ x y z → (x ℕ.+ y) ℕ.+ z ≡ x ℕ.+ (y ℕ.+ z)
+-assoc zero     y z = refl
+-assoc (suc x)  y z = cong suc (+-assoc x y z)

+-*-distrib : ∀ x y z → (x ℕ.+ y) ℕ.* z ≡ x ℕ.* z ℕ.+ y ℕ.* z
+-*-distrib zero y z = refl
+-*-distrib (suc x) y z = cong (z ℕ.+_) (+-*-distrib x y z) ∙ sym (+-assoc z (x ℕ.* z) (y ℕ.* z))
