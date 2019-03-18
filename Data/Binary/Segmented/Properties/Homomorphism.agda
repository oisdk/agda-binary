{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Properties.Homomorphism where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Segmented
open import Data.Nat as ℕ using (ℕ; suc; zero)

open ≡-Reasoning
import Data.Nat.Properties as ℕ-Prop
open import Data.Empty

lemma₁ : ∀ x {y} → x ≢ 0 → x ℕ.+ y ≢ 0
lemma₁ zero = λ z _ → z refl
lemma₁ (suc x) = λ _ ()

lemma₂ : ∀ {x} → x ≢ 0 → ℕ.pred (2 ℕ.* x) ≡ suc (2 ℕ.* ℕ.pred x)
lemma₂ {zero} p = ⊥-elim (p refl)
lemma₂ {suc x} _ = ℕ-Prop.+-suc _ _

lemma₄ : ∀ x → 2 ℕ.^ x ≢ 0
lemma₄ zero = λ ()
lemma₄ (suc x) = lemma₁ _ (lemma₄ x)

lemma₅ : ∀ x y → x ≢ 0 → y ≢ 0 → x ℕ.* y ≢ 0
lemma₅ zero y x≢0 y≢0 = λ _ → x≢0 refl
lemma₅ (suc x) zero x≢0 y≢0 = λ _ → y≢0 refl
lemma₅ (suc x) (suc y) x≢0 y≢0 = λ ()

lemma₃ : ∀ x → ⟦ x ⇓⟧₁⁺¹ ≢ 0
lemma₃ (x 1& xs) = lemma₅ (2 ℕ.^ suc x) (suc ⟦ xs ⇓⟧≤) (lemma₄ (suc x)) λ ()

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0₂ = refl
inc-homo (0< B₀ zero  0& y 1& xs) =
  begin
    ℕ.pred ⟦ suc y 1& xs ⇓⟧₁⁺¹
  ≡⟨⟩
    ℕ.pred (2 ℕ.^ suc (suc y) ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨⟩
    ℕ.pred (2 ℕ.* 2 ℕ.^ suc y ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨ cong ℕ.pred (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc y) _) ⟩
    ℕ.pred (2 ℕ.* (2 ℕ.^ suc y ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    ℕ.pred (2 ℕ.* ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨ lemma₂ (lemma₃ (y 1& xs)) ⟩
    suc (2 ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc (2 ℕ.^ 1 ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc ⟦ 0 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₀ suc x 0& y 1& xs) =
  begin
    (2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+
      suc ((2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+ zero)
  ≡⟨ ℕ-Prop.+-suc _ _ ⟩
    suc (2 ℕ.* ((2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤)))
  ≡⟨ cong suc (sym (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc x) _)) ⟩
    suc ((2 ℕ.^ suc (suc x)) ℕ.* ℕ.pred ((2 ℕ.^ suc y) ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    suc ⟦ suc x 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₁ x 1& 0₂) =
  begin
    ⟦ x 0& 0 1& 0₂ ⇓⟧₀
  ≡⟨⟩
    ⟦ x 1& 0₂ ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₃ (x 1& 0₂))) ⟩
    suc (ℕ.pred ⟦ x 1& 0₂ ⇓⟧₁⁺¹)
  ∎
inc-homo (0< B₁ x 1& 0< zero  0& z 1& xs) =
  begin
    ⟦ x 0& suc z 1& xs ⇓⟧₀
  ≡⟨⟩
    (2 ℕ.^ suc x) ℕ.* ℕ.pred ((2 ℕ.* 2 ℕ.^ suc z) ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (cong ℕ.pred (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc z) _)) ⟩
    (2 ℕ.^ suc x) ℕ.* ℕ.pred (2 ℕ.* (2 ℕ.^ suc z ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    (2 ℕ.^ suc x) ℕ.* ℕ.pred (2 ℕ.* ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (lemma₂ (lemma₃ (z 1& xs))) ⟩
    (2 ℕ.^ suc x) ℕ.* suc (2 ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    ⟦ x 1& 0< zero 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₃ (x 1& 0< 0 0& z 1& xs))) ⟩
    suc (ℕ.pred ⟦ x 1& 0< zero 0& z 1& xs ⇓⟧₁⁺¹)
  ∎
inc-homo (0< B₁ x 1& 0< suc y 0& z 1& xs) =
  begin
    ⟦ x 0& 0 1& 0< y 0& z 1& xs ⇓⟧₀
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* ℕ.pred ⟦ 0 1& 0< y 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* ℕ.pred (2 ℕ.* suc ⟦ y 0& z 1& xs ⇓⟧₀)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (lemma₂ {x = suc ⟦ y 0& z 1& xs ⇓⟧₀} λ ()) ⟩
    2 ℕ.^ suc x ℕ.* suc (2 ℕ.* ⟦ y 0& z 1& xs ⇓⟧₀)
  ≡⟨ cong ((2 ℕ.^ suc x) ℕ.*_) (cong suc (sym (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc y) _))) ⟩
    2 ℕ.^ suc x ℕ.* suc (2 ℕ.* 2 ℕ.^ suc y ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* suc (2 ℕ.^ suc (suc y) ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    2 ℕ.^ suc x ℕ.* suc ⟦ suc y 0& z 1& xs ⇓⟧₀
  ≡⟨⟩
    ⟦ x 1& 0< suc y 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (lemma₃ (x 1& 0< suc y 0& z 1& xs))) ⟩
    suc (ℕ.pred ⟦ x 1& 0< suc y 0& z 1& xs ⇓⟧₁⁺¹)
  ∎
