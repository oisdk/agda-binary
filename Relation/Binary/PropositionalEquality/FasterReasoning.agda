{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.FasterReasoning {a} {A : Set a} where

open import Relation.Binary.PropositionalEquality

infix  3 _∎
infixr 2 _≡⟨⟩_ step-≡ step-≡˘
infix  1 begin_

begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

step-≡ : (x {y z} : A) → y ≡ z → x ≡ y → x ≡ z
step-≡ _ y≡z x≡y = trans x≡y y≡z

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_∎ : (x : A) → x ≡ x
_∎ _ = refl

step-≡˘ : (x {y z} : A) → y ≡ z → y ≡ x → x ≡ z
step-≡˘ _ y≡z y≡x = trans (sym y≡x) y≡z

syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z
