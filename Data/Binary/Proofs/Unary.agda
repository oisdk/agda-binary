{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Unary where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Operations.Unary
open import Data.Binary.Definitions
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Empty
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Nat.Properties as ℕ-Prop
open import Data.Binary.Operations.Semantics
open import Data.Binary.Proofs.Lemmas

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

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0₂ = refl
inc-homo (0< B₀ zero  0& y 1& xs) =
  begin
    ℕ.pred ⟦ suc y 1& xs ⇓⟧₁⁺¹
  ≡⟨⟩
    ℕ.pred (2^ suc y +1 ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨⟩
    ℕ.pred (2 ℕ.* 2^ y +1 ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨ cong ℕ.pred (ℕ-Prop.*-assoc 2 (2^ y +1) _) ⟩
    ℕ.pred (2 ℕ.* (2^ y +1 ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    ℕ.pred (2 ℕ.* ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨ pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (y 1& xs)) ⟩
    suc (2 ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc (2 ℕ.^ 1 ℕ.* ℕ.pred ⟦ y 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    suc ⟦ 0 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₀ suc x 0& y 1& xs) =
  begin
    (2^ x +1) ℕ.* ℕ.pred ((2^ y +1) ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+
      suc ((2^ x +1) ℕ.* ℕ.pred ((2^ y +1) ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+ zero)
  ≡⟨ ℕ-Prop.+-suc _ _ ⟩
    suc (2 ℕ.* ((2^ x +1) ℕ.* ℕ.pred ((2^ y +1) ℕ.* suc ⟦ xs ⇓⟧≤)))
  ≡˘⟨ cong suc (ℕ-Prop.*-assoc 2 (2^ x +1) _) ⟩
    suc ((2^ suc x +1) ℕ.* ℕ.pred ((2^ y +1) ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    suc ⟦ suc x 0& y 1& xs ⇓⟧₀
  ∎
inc-homo (0< B₁ x 1& 0₂) =
  begin
    ⟦ x 0& 0 1& 0₂ ⇓⟧₀
  ≡⟨⟩
    ⟦ x 1& 0₂ ⇓⟧₁⁺¹
  ≡⟨ sym (ℕ-Prop.m≢0⇒suc[pred[m]]≡m (⟦x⇓⟧₁⁺¹≢0 (x 1& 0₂))) ⟩
    suc (ℕ.pred ⟦ x 1& 0₂ ⇓⟧₁⁺¹)
  ∎
inc-homo (0< B₁ x 1& 0< zero  0& z 1& xs) =
  begin
    ⟦ x 0& suc z 1& xs ⇓⟧₀
  ≡⟨⟩
    (2^ x +1) ℕ.* ℕ.pred ((2 ℕ.* 2^ z +1) ℕ.* suc ⟦ xs ⇓⟧≤)
  ≡⟨ cong ((2^ x +1) ℕ.*_) (cong ℕ.pred (ℕ-Prop.*-assoc 2 (2^ z +1) _)) ⟩
    (2^ x +1) ℕ.* ℕ.pred (2 ℕ.* (2^ z +1 ℕ.* suc ⟦ xs ⇓⟧≤))
  ≡⟨⟩
    (2^ x +1) ℕ.* ℕ.pred (2 ℕ.* ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨ cong ((2^ x +1) ℕ.*_) (pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (z 1& xs))) ⟩
    (2^ x +1) ℕ.* suc (2 ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    ⟦ x 1& 0< zero 0& z 1& xs ⇓⟧₁⁺¹
  ≡˘⟨ ℕ-Prop.m≢0⇒suc[pred[m]]≡m (⟦x⇓⟧₁⁺¹≢0 (x 1& 0< 0 0& z 1& xs)) ⟩
    suc (ℕ.pred ⟦ x 1& 0< zero 0& z 1& xs ⇓⟧₁⁺¹)
  ∎
inc-homo (0< B₁ x 1& 0< suc y 0& z 1& xs) =
  begin
    ⟦ x 0& 0 1& 0< y 0& z 1& xs ⇓⟧₀
  ≡⟨⟩
    2^ x +1 ℕ.* ℕ.pred ⟦ 0 1& 0< y 0& z 1& xs ⇓⟧₁⁺¹
  ≡⟨⟩
    2^ x +1 ℕ.* ℕ.pred (2 ℕ.* suc ⟦ y 0& z 1& xs ⇓⟧₀)
  ≡⟨ cong ((2^ x +1) ℕ.*_) (pred-distrib-2* {x = suc ⟦ y 0& z 1& xs ⇓⟧₀} λ ()) ⟩
    2^ x +1 ℕ.* suc (2 ℕ.* ⟦ y 0& z 1& xs ⇓⟧₀)
  ≡˘⟨ cong ((2^ x +1) ℕ.*_) (cong suc (ℕ-Prop.*-assoc 2 (2^ y +1) _)) ⟩
    2^ x +1 ℕ.* suc (2 ℕ.* 2^ y +1 ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    2^ x +1 ℕ.* suc (2^ suc y +1 ℕ.* ℕ.pred ⟦ z 1& xs ⇓⟧₁⁺¹)
  ≡⟨⟩
    2^ x +1 ℕ.* suc ⟦ suc y 0& z 1& xs ⇓⟧₀
  ≡⟨⟩
    ⟦ x 1& 0< suc y 0& z 1& xs ⇓⟧₁⁺¹
  ≡˘⟨ ℕ-Prop.m≢0⇒suc[pred[m]]≡m (⟦x⇓⟧₁⁺¹≢0 (x 1& 0< suc y 0& z 1& xs)) ⟩
    suc (ℕ.pred ⟦ x 1& 0< suc y 0& z 1& xs ⇓⟧₁⁺¹)
  ∎
