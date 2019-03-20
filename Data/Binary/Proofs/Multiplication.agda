{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Multiplication where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ-Prop
open import Function
open import Data.Binary.Operations.Unary
open import Data.Binary.Operations.Multiplication
open import Data.Binary.Proofs.Unary
open import Data.Nat.Reasoning
open import Data.Binary.Proofs.Lemmas
open import Data.Binary.Proofs.Addition

2^-homo : ∀ n x → 2^ n * x ≡ 2 ℕ.^ n ℕ.* x
2^-homo zero x = sym (ℕ-Prop.*-identityˡ x)
2^-homo (suc n) x =
  begin
    2^ suc n * x
  ≡⟨⟩
    2* 2^ n * x
  ≡⟨⟩
    (2^ n * x) ℕ.+ (2^ n * x)
  ≡˘⟨ ℕ-Prop.+-identityʳ _ ⟩
    (2^ n * x) ℕ.+ (2^ n * x) ℕ.+ 0
  ≡⟨ ℕ-Prop.+-assoc (2^ n * x) _ 0 ⟩
    2 ℕ.* (2^ n * x)
  ≡⟨ 2 *≫ 2^-homo n x ⟩
    2 ℕ.* ((2 ℕ.^ n) ℕ.* x)
  ≡˘⟨ ℕ-Prop.*-assoc 2 (2 ℕ.^ n) x ⟩
    (2 ℕ.* 2 ℕ.^ n) ℕ.* x
  ≡⟨⟩
    (2 ℕ.^ suc n) ℕ.* x
  ∎

2*-homo : ∀ x → 2* x ≡ 2 ℕ.* x
2*-homo x =
  begin
    2* x
  ≡⟨⟩
    x ℕ.+ x
  ≡˘⟨ ℕ-Prop.+-identityʳ _ ⟩
    x ℕ.+ x ℕ.+ 0
  ≡⟨ ℕ-Prop.+-assoc x x 0 ⟩
    x ℕ.+ (x ℕ.+ 0)
  ≡⟨⟩
    2 ℕ.* x
  ∎

mutual
  ⟨1*0⟩-homo : ∀ x₁ xs ys → ⟦ ⟨1*0⟩ x₁ xs ys ⇓⟧₁ ≡ ⟦ x₁ 1& xs ⇓⟧₁ ℕ.* suc (2* ⟦ ys ⇓⟧≤)
  ⟨1*0⟩-homo zero 0₂ ys = cong suc (sym (ℕ-Prop.+-identityʳ _))
  ⟨1*0⟩-homo zero (0< xs) ys = {!!}
  ⟨1*0⟩-homo (suc x₁) xs ys =
    let
      x′ = ⟦ x₁ 1& xs ⇓⟧₁
      y′ = ⟦ ys ⇓⟧≤
    in
    begin
      ⟦ suc₁ 0→⟨1+0?⟩ (⟨1*0⟩ x₁ xs ys) ys ⇓⟧₁
    ≡⟨⟩
      suc (2* ⟦ 0→⟨1+0?⟩ (⟨1*0⟩ x₁ xs ys) ys ⇓⟧₁)
    ≡⟨ cong suc (cong 2*_ (0→⟨1+0?⟩-homo (⟨1*0⟩ x₁ xs ys) ys)) ⟩
      suc (2* (⟦ ys ⇓⟧≤ ℕ.+ ⟦ ⟨1*0⟩ x₁ xs ys ⇓⟧₁))
    ≡⟨ cong suc (cong 2*_ (⟦ ys ⇓⟧≤ +≫ ⟨1*0⟩-homo x₁ xs ys )) ⟩
      suc (2* (⟦ ys ⇓⟧≤ ℕ.+ (⟦ x₁ 1& xs ⇓⟧₁ ℕ.* (suc (2* ⟦ ys ⇓⟧≤)))))
    ≡⟨⟩
      suc (2* (y′ ℕ.+ (x′ ℕ.* (suc (2* y′)))))
    ≡⟨ cong suc (cong 2*_ (y′ +≫ x′ *≫ cong suc (2*-homo y′))) ⟩
      suc (2* (y′ ℕ.+ (x′ ℕ.* (suc (2 ℕ.* y′)))))
    ≡⟨ cong suc (2*-homo (y′ ℕ.+ (x′ ℕ.* (suc (2 ℕ.* y′))))) ⟩
      1 ℕ.+ (2 ℕ.* (y′ ℕ.+ (x′ ℕ.* (1 ℕ.+ (2 ℕ.* y′)))))
    ≡⟨ 1 +≫ ℕ-Prop.*-distribˡ-+ 2 y′ _ ⟩
      1 ℕ.+ (2 ℕ.* y′ ℕ.+ 2 ℕ.* (x′ ℕ.* (1 ℕ.+ (2 ℕ.* y′))))
    ≡˘⟨ 1 +≫ 2 ℕ.* y′ +≫ ℕ-Prop.*-assoc 2 x′ _ ⟩
      1 ℕ.+ (2 ℕ.* y′ ℕ.+ (2 ℕ.* x′) ℕ.* (1 ℕ.+ (2 ℕ.* y′)))
    ≡˘⟨ ℕ-Prop.+-assoc 1 (2 ℕ.* y′) _ ⟩
      (1 ℕ.+ 2 ℕ.* y′) ℕ.+ (2 ℕ.* x′) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡˘⟨ _ ≪+ ℕ-Prop.*-identityˡ (1 ℕ.+ 2 ℕ.* y′) ⟩
      1 ℕ.* (1 ℕ.+ 2 ℕ.* y′) ℕ.+ (2 ℕ.* x′) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡˘⟨ ℕ-Prop.*-distribʳ-+ (1 ℕ.+ 2 ℕ.* y′) 1 (2 ℕ.* x′) ⟩
      (1 ℕ.+ 2 ℕ.* x′) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡⟨⟩
      suc (2 ℕ.* x′) ℕ.* suc (2 ℕ.* y′)
    ≡˘⟨ suc (2 ℕ.* y′) ≪* cong suc (2*-homo x′ )⟩
      suc (2* x′) ℕ.* suc (2 ℕ.* y′)
    ≡˘⟨ suc (2* x′) *≫ cong suc (2*-homo y′) ⟩
      suc (2* x′) ℕ.* suc (2* y′)
    ≡⟨⟩
      suc (2* ⟦ x₁ 1& xs ⇓⟧₁) ℕ.* suc (2* ⟦ ys ⇓⟧≤)
    ≡⟨⟩
      suc (2* ⟦ x₁ 1& xs ⇓⟧₁) ℕ.* ⟦ 0 1& ys ⇓⟧₁
    ∎

  ⟨1*s⟩-homo : ∀ x₁ xs y₁ ys → ⟦ ⟨1*s⟩ x₁ xs y₁ ys ⇓⟧₁ ≡ ⟦ x₁ 1& xs ⇓⟧₁ ℕ.* suc (2* ⟦ y₁ 1& ys ⇓⟧₁)
  ⟨1*s⟩-homo zero xs y₁ ys = {!!}
  ⟨1*s⟩-homo (suc x₁) xs y₁ ys = {!!}

  ⟨1*1⟩-homo : ∀ y₁ ys xs → ⟦ ⟨1*1⟩ y₁ ys xs ⇓⟧₁ ≡ ⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁
  ⟨1*1⟩-homo zero ys xs = ⟨1*0⟩-homo (H₁ xs) (T₁ xs) ys
  ⟨1*1⟩-homo (suc y₁) ys xs = ⟨1*s⟩-homo (H₁ xs) (T₁ xs) y₁ ys

*-homo : ∀ x y → ⟦ x * y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.* ⟦ y ⇓⟧
*-homo 0₂ y = refl
*-homo (0< xs) 0₂ = sym (ℕ-Prop.*-zeroʳ ⟦ 0< xs ⇓⟧)
*-homo (0< B₁ xs) (0< B₁ y₁ 1& ys) = ⟨1*1⟩-homo y₁ ys xs
*-homo (0< B₁ xs) (0< B₀ y₀ 0& y₁ 1& ys) =
  begin
    ⟦ (0< B₁ xs) * (0< B₀ y₀ 0& y₁ 1& ys) ⇓⟧
  ≡⟨⟩
    2^ suc y₀ * ⟦ ⟨1*1⟩ y₁ ys xs ⇓⟧₁
  ≡⟨ cong (2^ suc y₀ *_) (⟨1*1⟩-homo y₁ ys xs) ⟩
    2^ suc y₀ * (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡⟨ 2^-homo (suc y₀) _ ⟩
    2 ℕ.^ suc y₀ ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡˘⟨ ℕ-Prop.*-assoc (2 ℕ.^ suc y₀) ⟦ xs ⇓⟧₁ _ ⟩
    2 ℕ.^ suc y₀ ℕ.* ⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁
  ≡⟨ _ ≪* ℕ-Prop.*-comm (2 ℕ.^ suc y₀) ⟦ xs ⇓⟧₁ ⟩
    ⟦ xs ⇓⟧₁ ℕ.* 2 ℕ.^ suc y₀ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁
  ≡⟨ ℕ-Prop.*-assoc ⟦ xs ⇓⟧₁ (2 ℕ.^ suc y₀) _ ⟩
    ⟦ xs ⇓⟧₁ ℕ.* (2 ℕ.^ suc y₀ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡˘⟨ ⟦ xs ⇓⟧₁ *≫ 2^-homo (suc y₀) _ ⟩
    ⟦ xs ⇓⟧₁ ℕ.* (2^ suc y₀ * ⟦ y₁ 1& ys ⇓⟧₁)
  ≡⟨⟩
    ⟦ 0< B₁ xs ⇓⟧ ℕ.* ⟦ 0< B₀ y₀ 0& y₁ 1& ys ⇓⟧
  ∎
*-homo (0< B₀ x₀ 0& xs) (0< B₁ y₁ 1& ys) =
  begin
    ⟦ (0< B₀ x₀ 0& xs) * (0< B₁ y₁ 1& ys) ⇓⟧
  ≡⟨⟩
    2^ suc x₀ * ⟦ ⟨1*1⟩ y₁ ys xs ⇓⟧₁
  ≡⟨ cong (2^ suc x₀ *_) (⟨1*1⟩-homo y₁ ys xs) ⟩
    2^ suc x₀ * ⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁
  ≡⟨ 2^-homo (suc x₀) _ ⟩
    2 ℕ.^ suc x₀ ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡˘⟨ ℕ-Prop.*-assoc (2 ℕ.^ suc x₀) ⟦ xs ⇓⟧₁ _ ⟩
    2 ℕ.^ suc x₀ ℕ.* ⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁
  ≡˘⟨ _ ≪* 2^-homo (suc x₀) _ ⟩
    ⟦ 0< B₀ x₀ 0& xs ⇓⟧ ℕ.* ⟦ 0< B₁ y₁ 1& ys ⇓⟧
  ∎
*-homo (0< B₀ x₀ 0& xs) (0< B₀ y₀ 0& y₁ 1& ys) = {!!}
