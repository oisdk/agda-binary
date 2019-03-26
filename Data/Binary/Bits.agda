{-# OPTIONS --without-K --safe #-}

module Data.Binary.Bits where

open import Data.Binary.Segmented.Definitions
open import Data.List.Kleene
open import Data.Nat as ℕ using (ℕ; suc; zero)

data Bit : Set where O I : Bit

mutual
  toBits₀ : ℕ → 𝔹₁ → Bit ⁺
  toBits₀ zero    xs = I & toBits₁ (H₁ xs) (T₁ xs)
  toBits₀ (suc x) xs = O & ∹ toBits₀ x xs

  toBits₁ : ℕ → 0≤ 𝔹₀ → Bit ⋆
  toBits₁ zero 0₂ = []
  toBits₁ zero (0< xs) = ∹ O & ∹ toBits₀ (H₀ xs) (T₀ xs)
  toBits₁ (suc x) xs = ∹ I & toBits₁ x xs

toBits⁺ : 𝔹⁺ → Bit ⁺
toBits⁺ (B₀ xs) = O & ∹ toBits₀ (H₀ xs) (T₀ xs)
toBits⁺ (B₁ xs) = I & toBits₁ (H₁ xs) (T₁ xs)

toBits : 𝔹 → Bit ⋆
toBits 0₂ = []
toBits (0< xs) = ∹ toBits⁺ xs

open import Relation.Binary.PropositionalEquality hiding ([_])

-- [∙]-inj : ∀ {a} {A : Set a} → {x y : A ⁺} → [ x ] ≡ [ y ] → x ≡ y
-- [∙]-inj refl = refl

-- mutual
--   inj₀ : ∀ x xs y ys → toBits₀ x xs ≡ toBits₀ y ys → x 0& xs ≡ y 0& ys
--   inj₀ zero xs zero ys xs≡ys = cong (0 0&_) (inj₁ (H₁ xs) (T₁ xs) (H₁ ys) (T₁ ys) (cong tail xs≡ys))
--   inj₀ zero xs (suc y) ys ()
--   inj₀ (suc x) xs zero ys ()
--   inj₀ (suc x) xs (suc y) ys xs≡ys = cong suc₀_ (inj₀ x xs y ys ([∙]-inj (cong tail xs≡ys)))

--   inj₁ : ∀ x xs y ys → toBits₁ x xs ≡ toBits₁ y ys → x 1& xs ≡ y 1& ys
--   inj₁ zero 0₂ zero 0₂ xs≡ys = refl
--   inj₁ zero 0₂ zero (0< x) ()
--   inj₁ zero (0< x) zero 0₂ ()
--   inj₁ zero (0< x₀ 0& xs) zero (0< y₀ 0& ys) xs≡ys = cong (λ z → 0 1& 0< z) (inj₀ x₀ xs y₀ ys ([∙]-inj (cong tail ([∙]-inj xs≡ys))))
--   inj₁ zero 0₂ (suc y) ys ()
--   inj₁ zero (0< x) (suc y) ys ()
--   inj₁ (suc x) xs zero 0₂ ()
--   inj₁ (suc x) xs zero (0< x₁) ()
--   inj₁ (suc x) xs (suc y) ys xs≡ys = cong suc₁_ (inj₁ x xs y ys (cong tail ([∙]-inj xs≡ys)))

-- toBits-injective : ∀ xs ys → toBits xs ≡ toBits ys → xs ≡ ys
-- toBits-injective 0₂ 0₂ bxs≡bys = refl
-- toBits-injective 0₂ (0< x) ()
-- toBits-injective (0< x) 0₂ ()
-- toBits-injective (0< B₀ x₀ 0& xs) (0< B₀ y₀ 0& ys) bxs≡bys = cong (λ z → 0< B₀ z) (inj₀ x₀ xs y₀ ys ([∙]-inj (cong tail ([∙]-inj bxs≡bys))))
-- toBits-injective (0< B₀ x) (0< B₁ x₁) ()
-- toBits-injective (0< B₁ x) (0< B₀ x₁) ()
-- toBits-injective (0< B₁ x₁ 1& xs) (0< B₁ y₁ 1& ys) bxs≡bys = cong (λ z → 0< B₁ z) (inj₁ x₁ xs y₁ ys (cong tail ([∙]-inj bxs≡bys)))

-- data Ordering : Set where
--   lt eq gt : Ordering

-- _∙_ : Ordering → Ordering → Ordering
-- lt ∙ y = lt
-- eq ∙ y = y
-- gt ∙ y = gt

-- cmpBit : Bit → Bit → Ordering
-- cmpBit O O = eq
-- cmpBit O I = lt
-- cmpBit I O = gt
-- cmpBit I I = eq

-- compare : Bit ⋆ → Bit ⋆ → Ordering
-- compare [] [] = eq
-- compare [] [ x ] = lt
-- compare [ x ] [] = gt
-- compare [ xs ] [ ys ] = compare (tail xs) (tail ys) ∙ cmpBit (head xs) (head ys)

-- ∙-inj : ∀ x → x ∙ eq ≡ x
-- ∙-inj lt = refl
-- ∙-inj eq = refl
-- ∙-inj gt = refl

-- lt-not-eq : ∀ x → x ∙ lt ≢ eq
-- lt-not-eq lt = λ ()
-- lt-not-eq eq = λ ()
-- lt-not-eq gt = λ ()

-- gt-not-eq : ∀ x → x ∙ gt ≢ eq
-- gt-not-eq lt = λ ()
-- gt-not-eq eq = λ ()
-- gt-not-eq gt = λ ()

-- open import Function
-- open import Data.Empty

-- cmp-eq : ∀ xs ys → compare xs ys ≡ eq → xs ≡ ys
-- cmp-eq [] [] xs≡ys = refl
-- cmp-eq [] [ x ] ()
-- cmp-eq [ x ] [] ()
-- cmp-eq [ O & xs ] [ O & ys ] xs≡ys = cong (λ z → [ O & z ] ) (cmp-eq xs ys (sym (∙-inj _) ⟨ trans ⟩ xs≡ys))
-- cmp-eq [ O & xs ] [ I & ys ] xs≡ys = ⊥-elim (lt-not-eq _ xs≡ys)
-- cmp-eq [ I & xs ] [ O & ys ] xs≡ys = ⊥-elim (gt-not-eq _ xs≡ys)
-- cmp-eq [ I & xs ] [ I & ys ] xs≡ys = cong (λ z → [ I & z ] ) (cmp-eq xs ys (sym (∙-inj _) ⟨ trans ⟩ xs≡ys))
