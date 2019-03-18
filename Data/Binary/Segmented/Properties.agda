{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Properties where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Segmented
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary
open import Function

dec-inc : ∀ x → dec⁺ (inc⁺ x) ≡ x
dec-inc 0₂                         = refl
dec-inc (0< B₁ _ 1& 0₂           ) = refl
dec-inc (0< B₁ _ 1& 0< zero  0& _) = refl
dec-inc (0< B₁ _ 1& 0< suc _ 0& _) = refl
dec-inc (0< B₀ zero  0& _        ) = refl
dec-inc (0< B₀ suc _ 0& _        ) = refl

inc-dec : ∀ x → inc⁺ (dec⁺ x) ≡ x
inc-dec (     B₁ zero  1& 0₂  ) = refl
inc-dec (     B₁ zero  1& 0< _) = refl
inc-dec (     B₁ suc _ 1& _   ) = refl
inc-dec (B₀ _ 0& zero  1& 0₂  ) = refl
inc-dec (B₀ _ 0& zero  1& 0< _) = refl
inc-dec (B₀ _ 0& suc _ 1& _   ) = refl

mutual
  infix 4 _≟₀_ _≟₁_ _≟≤_
  _≟₀_ : Decidable (_≡_ {A = Bits₀})
  x 0& xs ≟₀ y 0& ys with x ℕ.≟ y
  x 0& xs ≟₀ y 0& ys | no ¬p = no λ { refl → ¬p refl }
  x 0& xs ≟₀ y 0& ys | yes p with xs ≟₁ ys
  x 0& xs ≟₀ y 0& ys | yes p | no ¬p = no λ { refl → ¬p refl }
  x 0& xs ≟₀ .x 0& .xs | yes refl | yes refl = yes refl

  _≟₁_ : Decidable (_≡_ {A = Bits₁})
  x 1& xs ≟₁ y 1& ys with x ℕ.≟ y
  x 1& xs ≟₁ y 1& ys | no ¬p = no λ { refl → ¬p refl }
  x 1& xs ≟₁ y 1& ys | yes p with xs ≟≤ ys
  x 1& xs ≟₁ y 1& ys | yes p | no ¬p = no λ { refl → ¬p refl }
  x 1& xs ≟₁ y 1& ys | yes refl | yes refl = yes refl

  _≟≤_ : Decidable (_≡_ {A = 0≤ Bits₀})
  0₂ ≟≤ 0₂ = yes refl
  0₂ ≟≤ 0< _ = no (λ ())
  0< _ ≟≤ 0₂ = no (λ ())
  0< xs ≟≤ 0< ys with xs ≟₀ ys
  ... | yes refl = yes refl
  ... | no ¬p = no λ { refl → ¬p refl }

infix 4 _≟_
_≟_ : Decidable (_≡_ {A = Bits})
0₂ ≟ 0₂ = yes refl
0₂ ≟ (0< x) = no (λ ())
(0< x) ≟ 0₂ = no (λ ())
(0< B₀ xs) ≟ (0< B₀ ys) with xs ≟₀ ys
(0< B₀ xs ≟ 0< B₀ .xs) | yes refl = yes refl
(0< B₀ xs ≟ 0< B₀ ys) | no ¬p = no λ { refl → ¬p refl }
(0< B₀ xs) ≟ (0< B₁ ys) = no (λ ())
(0< B₁ x) ≟ (0< B₀ x₁) = no (λ ())
(0< B₁ xs) ≟ (0< B₁ ys) with xs ≟₁ ys
(0< B₁ x ≟ 0< B₁ x₁) | yes refl = yes refl
(0< B₁ x ≟ 0< B₁ x₁) | no ¬p = no λ { refl → ¬p refl }

open ≡-Reasoning
import Data.Nat.Properties as ℕ-Prop
open import Data.Empty

lemma₁ : ∀ x {y} → x ≢ 0 → x ℕ.+ y ≢ 0
lemma₁ zero = λ z _ → z refl
lemma₁ (suc x) = λ _ ()

lemma₂ : ∀ {x} → x ≢ 0 → suc (2 ℕ.* ℕ.pred x) ≡ ℕ.pred (2 ℕ.* x)
lemma₂ {zero} p = ⊥-elim (p refl)
lemma₂ {suc x} _ = sym (ℕ-Prop.+-suc _ _)

lemma₄ : ∀ x → 2 ℕ.^ x ≢ 0
lemma₄ zero = λ ()
lemma₄ (suc x) = lemma₁ _ (lemma₄ x)

lemma₃ : ∀ x → ⟦ x ⇓⟧₁⁺¹ ≢ 0
lemma₃ (zero 1& 0₂) = λ ()
lemma₃ (suc x 1& 0₂) = lemma₁ ((2 ℕ.^ x) ℕ.+ ((2 ℕ.^ x) ℕ.+ zero)) (lemma₁ (2 ℕ.^ x) (lemma₄ x))
lemma₃ (x 1& 0< xs) p = lemma₁ (2 ℕ.^ suc x) (lemma₄ (suc x)) (ℕ-Prop.*-comm (suc ⟦ xs ⇓⟧₀) ((2 ℕ.^ x) ℕ.+ ((2 ℕ.^ x) ℕ.+ zero)) ⟨ trans ⟩ p)

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0₂                      = refl
inc-homo (0< B₀ zero  0& y 1& 0₂) =
  begin
    ℕ.pred (2 ℕ.* (2 ℕ.^ suc y))
  ≡⟨ sym (lemma₂ (lemma₄ (suc y))) ⟩
    suc (2 ℕ.* ℕ.pred (2 ℕ.^ suc y))
  ≡⟨⟩
    suc ⟦ zero 0& y 1& 0₂ ⇓⟧₀
  ∎
inc-homo (0< B₀ zero  0& y 1& 0< xs) =
  begin
    ℕ.pred ⟦ suc y 1& 0< xs ⇓⟧₁⁺¹
  ≡⟨⟩
    ℕ.pred (2 ℕ.^ suc (suc y) ℕ.* suc ⟦  xs ⇓⟧₀ )
  ≡⟨⟩
    ℕ.pred ((2 ℕ.* 2 ℕ.^ suc y) ℕ.* suc ⟦  xs ⇓⟧₀ )
  ≡⟨ cong ℕ.pred (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc y) _) ⟩
    ℕ.pred (2 ℕ.* (2 ℕ.^ suc y ℕ.* suc ⟦  xs ⇓⟧₀) )
  ≡⟨⟩
    ℕ.pred (2 ℕ.* ⟦ y 1& 0< xs ⇓⟧₁⁺¹)
  ≡⟨ sym (lemma₂ (lemma₃ (y 1& 0< xs))) ⟩
    suc (2 ℕ.* ℕ.pred ⟦ y 1& 0< xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc ⟦ 0 0& y 1& 0< xs ⇓⟧₀
  ∎
inc-homo (0< B₀ suc x 0& y 1& xs) =
  begin
    (2 ℕ.^ suc x) ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹ ℕ.+ suc ((2 ℕ.^ suc x) ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹ ℕ.+ zero)
  ≡⟨ ℕ-Prop.+-suc _ _ ⟩
    suc ((2 ℕ.^ suc x) ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹ ℕ.+ ((2 ℕ.^ suc x) ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹ ℕ.+ zero))
  ≡⟨⟩
    suc (2 ℕ.* ((2 ℕ.^ suc x) ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹))
  ≡⟨ cong suc (sym (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc x) _)) ⟩
    suc ( 2 ℕ.^ suc (suc x) ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc ⟦ suc x 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₁ x 1& 0₂) =
  begin
    ⟦ x 0& 0 1& 0₂ ⇓⟧₀
  ≡⟨⟩
    (2 ℕ.^ suc x) ℕ.* 1
  ≡⟨ ℕ-Prop.*-identityʳ _ ⟩
    2 ℕ.^ suc x
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₄ (suc x))) ⟩
    suc (ℕ.pred (2 ℕ.^ suc x))
  ∎
inc-homo (0< B₁ x 1& 0< zero  0& z 1& 0₂) =
  begin
    ⟦ x 0& suc z 1& 0₂ ⇓⟧₀
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* ℕ.pred (2 ℕ.^ suc (suc z))
  ≡⟨ {!!} ⟩
    suc (ℕ.pred (2 ℕ.^ suc x ℕ.* suc ⟦ 0 0& z 1& 0₂ ⇓⟧₀))
  ∎
inc-homo (0< B₁ x 1& 0< zero  0& z 1& 0< xs) =
  begin
    ⟦ x 0& suc z 1& 0< xs ⇓⟧₀
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* ℕ.pred ⟦ suc z 1& 0< xs ⇓⟧₁⁺¹
  ≡⟨ {!!} ⟩
    suc (ℕ.pred ((2 ℕ.^ suc x) ℕ.* suc (2 ℕ.* ℕ.pred ⟦ z 1& 0< xs ⇓⟧₁⁺¹)))
  ∎
inc-homo (0< B₁ x 1& 0< suc y 0& z 1& xs) = {!!}

homo : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
homo zero = refl
homo (suc n) = inc-homo ⟦ n ⇑⟧ ⟨ trans ⟩ cong suc (homo n)

open import Data.List as List using (List; _∷_)

private
  roundTrip : ℕ → Set
  roundTrip n = ⟦ ⟦ n ⇑⟧ ⇓⟧  ≡ n

  _ : roundTrip 50
  _ = refl

  upTo : ∀ {a} {A : Set a} → ℕ → (A → A) → A → List A
  upTo zero    f x = List.[]
  upTo (suc n) f x = x ∷ upTo n f (f x)

  suc-correct : ℕ → Set
  suc-correct n = List.map ⟦_⇓⟧ (upTo n inc 0₂) ≡ List.upTo n

  _ : suc-correct 100
  _ = refl
