{-# OPTIONS --cubical --guardedness #-}

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
open import Data.Binary.Properties.Double
open import Data.Binary.Double
open import Data.Binary.Increment

+0ᵇ : ∀ x → x + 0ᵇ ≡ x
+0ᵇ 0ᵇ = refl
+0ᵇ (1ᵇ x) = refl
+0ᵇ (2ᵇ x) = refl

+2ᵇ : ∀ x y → x + 2ᵇ y ≡ 1+[ x + 1ᵇ y ]
+2ᵇ 0ᵇ y = refl
+2ᵇ (1ᵇ x) y = refl
+2ᵇ (2ᵇ x) y = refl

1ᵇ-double : ∀ x → 1ᵇ x ≡ inc (2× x)
1ᵇ-double 0ᵇ = refl
1ᵇ-double (1ᵇ x) = cong 1ᵇ_ (1ᵇ-double x)
1ᵇ-double (2ᵇ x) = refl

2ᵇ-double : ∀ x → 2ᵇ x ≡ 2× (inc x)
2ᵇ-double 0ᵇ = refl
2ᵇ-double (1ᵇ x) = refl
2ᵇ-double (2ᵇ x) = cong 2ᵇ_ (2ᵇ-double x)

add-inc : ∀ x → 1+[ x + 0ᵇ ] ≡ inc x
add-inc 0ᵇ = refl
add-inc (1ᵇ x) = refl
add-inc (2ᵇ x) = refl

+2ᵇ₂ : ∀ x y → 1+[  x + 2ᵇ y ] ≡ 2+[  x + 1ᵇ y ]
+2ᵇ₂ 0ᵇ y = refl
+2ᵇ₂ (1ᵇ x) y = refl
+2ᵇ₂ (2ᵇ x) y = refl

+1ᵇ₂ : ∀ x y → 1+[ x + 1ᵇ y ] ≡ 2+[ x + 2× y ]
+1ᵇ₂ 0ᵇ 0ᵇ = refl
+1ᵇ₂ 0ᵇ (1ᵇ y) = cong 2ᵇ_ (1ᵇ-double y)
+1ᵇ₂ 0ᵇ (2ᵇ y) = refl
+1ᵇ₂ (1ᵇ x) 0ᵇ = cong 1ᵇ_ (add-inc x)
+1ᵇ₂ (1ᵇ x) (1ᵇ y) = cong 1ᵇ_ (+1ᵇ₂ x y)
+1ᵇ₂ (1ᵇ x) (2ᵇ y) = cong 1ᵇ_ (+2ᵇ₂ x y)
+1ᵇ₂ (2ᵇ x) 0ᵇ = cong 2ᵇ_ (add-inc x)
+1ᵇ₂ (2ᵇ x) (1ᵇ y) = cong 2ᵇ_ (+1ᵇ₂ x y)
+1ᵇ₂ (2ᵇ x) (2ᵇ y) = cong 2ᵇ_ (+2ᵇ₂ x y)

+1ᵇ : ∀ x y → x + 1ᵇ y ≡ 1+[  x + 2× y ]
+1ᵇ 0ᵇ y = 1ᵇ-double y
+1ᵇ (1ᵇ x) 0ᵇ = cong 2ᵇ_ (+0ᵇ x)
+1ᵇ (1ᵇ x) (1ᵇ y) = cong 2ᵇ_ (+1ᵇ x y)
+1ᵇ (1ᵇ x) (2ᵇ y) = cong 2ᵇ_ (+2ᵇ x y)
+1ᵇ (2ᵇ x) 0ᵇ = cong 1ᵇ_ (add-inc x)
+1ᵇ (2ᵇ x) (1ᵇ y) = cong 1ᵇ_ (+1ᵇ₂ x y)
+1ᵇ (2ᵇ x) (2ᵇ y) = cong 1ᵇ_ (+2ᵇ₂ x y)

+2×-lemma : ∀ x y → x +2× y ≡ x + 2× y
+2×-lemma 0ᵇ y = refl
+2×-lemma (1ᵇ x) 0ᵇ = cong 1ᵇ_ (+0ᵇ x)
+2×-lemma (2ᵇ x) 0ᵇ = cong 2ᵇ_ (+0ᵇ x)
+2×-lemma (1ᵇ x) (1ᵇ y) = cong 1ᵇ_ (+1ᵇ x y)
+2×-lemma (1ᵇ x) (2ᵇ y) = cong 1ᵇ_ (+2ᵇ x y)
+2×-lemma (2ᵇ x) (1ᵇ y) = cong 2ᵇ_ (+1ᵇ x y)
+2×-lemma (2ᵇ x) (2ᵇ y) = cong 2ᵇ_ (+2ᵇ x y)

2ᵇ-double-+₂ : ∀ x y → 2ᵇ 1+[ x + y ] ≡ 2× 2+[ x + y ]
2ᵇ-double-+₂ 0ᵇ 0ᵇ = refl
2ᵇ-double-+₂ 0ᵇ (1ᵇ y) = cong 2ᵇ_ (2ᵇ-double y)
2ᵇ-double-+₂ 0ᵇ (2ᵇ y) = refl
2ᵇ-double-+₂ (1ᵇ x) 0ᵇ = cong 2ᵇ_ (2ᵇ-double x)
2ᵇ-double-+₂ (1ᵇ x) (1ᵇ y) = refl
2ᵇ-double-+₂ (1ᵇ x) (2ᵇ y) = cong 2ᵇ_ (2ᵇ-double-+₂ x y)
2ᵇ-double-+₂ (2ᵇ x) 0ᵇ = refl
2ᵇ-double-+₂ (2ᵇ x) (1ᵇ y) = cong 2ᵇ_ (2ᵇ-double-+₂ x y)
2ᵇ-double-+₂ (2ᵇ x) (2ᵇ y) = refl

2ᵇ-double-+ : ∀ x y → 2ᵇ (x + y) ≡ 2× 1+[ x + y ]
2ᵇ-double-+ 0ᵇ y = 2ᵇ-double y
2ᵇ-double-+ (1ᵇ x) 0ᵇ = refl
2ᵇ-double-+ (1ᵇ x) (1ᵇ y) = cong 2ᵇ_ (2ᵇ-double-+ x y)
2ᵇ-double-+ (1ᵇ x) (2ᵇ y) = refl
2ᵇ-double-+ (2ᵇ x) 0ᵇ = cong 2ᵇ_ (2ᵇ-double x)
2ᵇ-double-+ (2ᵇ x) (1ᵇ y) = refl
2ᵇ-double-+ (2ᵇ x) (2ᵇ y) = cong 2ᵇ_ (2ᵇ-double-+₂ x y)

+²-lemma : ∀ x y → 2×[ x + y ] ≡ 2× (x + y)
+²-lemma 0ᵇ y = refl
+²-lemma (1ᵇ x) 0ᵇ = refl
+²-lemma (2ᵇ x) 0ᵇ = refl
+²-lemma (1ᵇ x) (1ᵇ y) = refl
+²-lemma (2ᵇ x) (2ᵇ y) = refl
+²-lemma (1ᵇ x) (2ᵇ y) = cong 2ᵇ_ (2ᵇ-double-+ x y)
+²-lemma (2ᵇ x) (1ᵇ y) = cong 2ᵇ_ (2ᵇ-double-+ x y)

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
  ⟦ ys +2× (ys * xs) ⇓⟧ ≡⟨ cong ⟦_⇓⟧ (+2×-lemma ys (ys * xs)) ⟩
  ⟦ ys + 2× (ys * xs) ⇓⟧ ≡⟨ +-cong ys (2× (ys * xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ 2× (ys * xs) ⇓⟧ ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_)  (double-cong (ys * xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ ys * xs ⇓⟧ ℕ.* 2 ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_)  (cong (ℕ._* 2) (*-cong ys xs)) ⟩
  ⟦ ys ⇓⟧  ℕ.+ ⟦ ys ⇓⟧ ℕ.* ⟦ xs ⇓⟧ ℕ.* 2 ≡⟨ cong (⟦ ys ⇓⟧ ℕ.+_) (lemma₁ ⟦ ys ⇓⟧ ⟦ xs ⇓⟧) ⟩
  ⟦ ys ⇓⟧ ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.* ⟦ ys ⇓⟧ ∎
*-cong (2ᵇ xs) ys =
  ⟦ 2×[ ys + ys * xs ] ⇓⟧ ≡⟨ cong ⟦_⇓⟧ (+²-lemma ys (ys * xs)) ⟩
  ⟦ 2× (ys + ys * xs) ⇓⟧ ≡⟨ double-cong (ys + ys * xs) ⟩
  ⟦ ys + ys * xs ⇓⟧ ℕ.* 2 ≡⟨ cong (ℕ._* 2) (+-cong ys (ys * xs)) ⟩
  (⟦ ys ⇓⟧ ℕ.+ ⟦ ys * xs ⇓⟧) ℕ.* 2 ≡⟨ cong (ℕ._* 2) (cong (⟦ ys ⇓⟧ ℕ.+_) (*-cong ys xs)) ⟩
  (⟦ ys ⇓⟧ ℕ.+ ⟦ ys ⇓⟧ ℕ.* ⟦ xs ⇓⟧) ℕ.* 2 ≡⟨ lemma₂ ⟦ ys ⇓⟧ ⟦ xs ⇓⟧  ⟩
  ⟦ ys ⇓⟧ ℕ.+ (⟦ ys ⇓⟧ ℕ.+ ⟦ xs ⇓⟧ ℕ.* 2 ℕ.* ⟦ ys ⇓⟧) ∎
