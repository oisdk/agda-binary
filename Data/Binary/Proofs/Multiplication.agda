{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Multiplication where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition
open import Data.Binary.Operations.Semantics as Bin
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
  ⟨1*0⟩-homo : ∀ x₁ xs ys → ⟦ ⟨1*0⟩ x₁ xs ys ⇓⟧₁ ≡ ⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ 0 1& ys ⇓⟧₁
  ⟨1*0⟩-homo zero 0₂ ys = cong suc (sym (ℕ-Prop.+-identityʳ _))
  ⟨1*0⟩-homo zero (0< x₀ 0& x₁ 1& xs) ys =
    let x′ = ⟦ x₁ 1& xs ⇓⟧₁
        y′ = ⟦ ys ⇓⟧≤
    in
    begin
      ⟦ 0 1& 0< 0→⟨0?+0⟩ ys x₀ (⟨1*0⟩ x₁ xs ys) ⇓⟧₁
    ≡⟨⟩
      suc (2* ⟦ 0→⟨0?+0⟩ ys x₀ (⟨1*0⟩ x₁ xs ys) ⇓⟧₀)
    ≡⟨ cong suc (cong 2*_ (0→⟨0?+0⟩-homo ys x₀ (⟨1*0⟩ x₁ xs ys))) ⟩
      suc (2* ⟦ ys ⇓⟧≤ ℕ.+ ⟦ x₀ 0& (⟨1*0⟩ x₁ xs ys) ⇓⟧₀)
    ≡⟨⟩
      suc (2* ⟦ ys ⇓⟧≤ ℕ.+ (2^ suc x₀ * ⟦ ⟨1*0⟩ x₁ xs ys ⇓⟧₁))
    ≡⟨ cong suc (cong 2*_ (⟦ ys ⇓⟧≤ +≫ cong (2^ suc x₀ *_) (⟨1*0⟩-homo x₁ xs ys))) ⟩
      suc (2* ⟦ ys ⇓⟧≤ ℕ.+ (2^ suc x₀ * ⟦ x₁ 1& xs ⇓⟧₁ ℕ.* suc (2* ⟦ ys ⇓⟧≤)))
    ≡⟨⟩
      suc (2* y′ ℕ.+ (2^ suc x₀ * x′ ℕ.* suc (2* y′)))
    ≡⟨ cong suc (2*-homo (y′ ℕ.+ (2^ suc x₀ * x′ ℕ.* suc (2* y′)))) ⟩
      suc (2 ℕ.* (y′ ℕ.+ (2^ suc x₀ * x′ ℕ.* suc (2* y′))))
    ≡⟨⟩
      1 ℕ.+ (2 ℕ.* (y′ ℕ.+ (2^ suc x₀ * x′ ℕ.* (1 ℕ.+ (2* y′)))))
    ≡⟨ 1 +≫ 2 *≫ y′ +≫ 2^-homo (suc x₀) _ ⟩
      1 ℕ.+ (2 ℕ.* (y′ ℕ.+ (2 ℕ.^ suc x₀ ℕ.* (x′ ℕ.* (1 ℕ.+ (2* y′))))))
    ≡⟨ 1 +≫ 2 *≫ y′ +≫ (2 ℕ.^ suc x₀) *≫ x′ *≫ 1 +≫ 2*-homo y′ ⟩
      1 ℕ.+ (2 ℕ.* (y′ ℕ.+ (2 ℕ.^ suc x₀ ℕ.* (x′ ℕ.* (1 ℕ.+ (2 ℕ.* y′))))))
    ≡⟨ 1 +≫ ℕ-Prop.*-distribˡ-+ 2 y′ _ ⟩
      1 ℕ.+ (2 ℕ.* y′ ℕ.+ 2 ℕ.* (2 ℕ.^ suc x₀ ℕ.* (x′ ℕ.* (1 ℕ.+ (2 ℕ.* y′)))))
    ≡˘⟨ ℕ-Prop.+-assoc 1 (2 ℕ.* y′) _ ⟩
      (1 ℕ.+ 2 ℕ.* y′) ℕ.+ 2 ℕ.* (2 ℕ.^ suc x₀ ℕ.* (x′ ℕ.* (1 ℕ.+ 2 ℕ.* y′)))
    ≡˘⟨ (1 ℕ.+ 2 ℕ.* y′) +≫ (ℕ-Prop.*-assoc (2 ℕ.* 2 ℕ.^ suc x₀) x′ _ ⟨ trans ⟩ ℕ-Prop.*-assoc 2 (2 ℕ.^ suc x₀) _) ⟩
      (1 ℕ.+ 2 ℕ.* y′) ℕ.+ (2 ℕ.* 2 ℕ.^ suc x₀ ℕ.* x′) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡˘⟨ _ ≪+ ℕ-Prop.*-identityˡ (1 ℕ.+ 2 ℕ.* y′) ⟩
      1 ℕ.* (1 ℕ.+ 2 ℕ.* y′) ℕ.+ (2 ℕ.* 2 ℕ.^ suc x₀ ℕ.* x′) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡˘⟨ ℕ-Prop.*-distribʳ-+ (1 ℕ.+ 2 ℕ.* y′) 1 (2 ℕ.* 2 ℕ.^ suc x₀ ℕ.* x′) ⟩
      (1 ℕ.+ 2 ℕ.* 2 ℕ.^ suc x₀ ℕ.* x′) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡⟨ (1 ℕ.+ 2 ℕ.* y′) ≪* 1 +≫ (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc x₀) _ ⟨ trans ⟩ sym (2 *≫ 2^-homo (suc x₀) x′)) ⟩
      (1 ℕ.+ 2 ℕ.* (2^ suc x₀ * x′)) ℕ.* (1 ℕ.+ 2 ℕ.* y′)
    ≡⟨⟩
      suc (2 ℕ.* (2^ suc x₀ * x′)) ℕ.* suc (2 ℕ.* y′)
    ≡˘⟨ suc (2 ℕ.* (2^ suc x₀ * x′)) *≫ cong suc (2*-homo y′) ⟩
      suc (2 ℕ.* (2^ suc x₀ * x′)) ℕ.* suc (2* y′)
    ≡˘⟨ suc (2* y′) ≪* cong suc (2*-homo (2^ suc x₀ * x′)) ⟩
      suc (2* 2^ suc x₀ * x′) ℕ.* suc (2* y′)
    ≡⟨⟩
      ⟦ 0 1& 0< x₀ 0& x₁ 1& xs ⇓⟧₁ ℕ.* suc (2* ⟦ ys ⇓⟧≤)
    ∎
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

  ⟨1*s⟩-homo : ∀ x₁ xs y₁ ys → ⟦ ⟨1*s⟩ x₁ xs y₁ ys ⇓⟧₁ ≡ ⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁
  ⟨1*s⟩-homo zero 0₂ y₁ ys =
    begin
      ⟦ ⟨1*s⟩ zero 0₂ y₁ ys ⇓⟧₁
    ≡⟨⟩
      ⟦ suc₁ (⟨0*s⟩ 0₂ y₁ ys) ⇓⟧₁
    ≡⟨⟩
      ⟦ suc₁ (y₁ 1& ys) ⇓⟧₁
    ≡⟨⟩
      ⟦ suc y₁ 1& ys ⇓⟧₁
    ≡˘⟨ ℕ-Prop.*-identityˡ _ ⟩
      1 ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁
    ≡⟨⟩
      ⟦ zero 1& 0₂ ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁
    ∎
  ⟨1*s⟩-homo zero (0< x₀ 0& x₁ 1& xs) y₁ ys =
    let x′ = ⟦ x₁ 1& xs ⇓⟧₁
        y′ = ⟦ y₁ 1& ys ⇓⟧₁
    in
    begin
      ⟦ ⟨1*s⟩ zero (0< x₀ 0& x₁ 1& xs) y₁ ys ⇓⟧₁
    ≡⟨⟩
      ⟦ suc₁ (0→⟨1+0⟩ y₁ ys x₀ (⟨1*s⟩ x₁ xs y₁ ys)) ⇓⟧₁
    ≡⟨⟩
      suc (2* ⟦ 0→⟨1+0⟩ y₁ ys x₀ (⟨1*s⟩ x₁ xs y₁ ys) ⇓⟧₁)
    ≡⟨ cong suc (cong 2*_ (0→⟨1+0⟩-homo y₁ ys x₀ (⟨1*s⟩ x₁ xs y₁ ys))) ⟩
      suc (2* ⟦ y₁ 1& ys ⇓⟧₁ ℕ.+ ⟦ x₀ 0& (⟨1*s⟩ x₁ xs y₁ ys) ⇓⟧₀)
    ≡⟨⟩
      suc (2* ⟦ y₁ 1& ys ⇓⟧₁ ℕ.+ (2^ suc x₀ * ⟦ ⟨1*s⟩ x₁ xs y₁ ys ⇓⟧₁))
    ≡⟨ cong suc (cong 2*_ (⟦ y₁ 1& ys ⇓⟧₁ +≫ cong (2^ suc x₀ *_) (⟨1*s⟩-homo x₁ xs y₁ ys))) ⟩
      suc (2* y′ ℕ.+ (2^ suc x₀ * ⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁))
    ≡⟨⟩
      suc (2* y′ ℕ.+ (2^ suc x₀ * x′ ℕ.* suc (2* y′)))
    ≡⟨ cong suc (cong 2*_ (y′ +≫ 2^-homo (suc x₀) _)) ⟩
      suc (2* (y′ ℕ.+ (2 ℕ.^ suc x₀ ℕ.* (x′ ℕ.* suc (2* y′)))))
    ≡˘⟨ cong suc (cong 2*_ (y′ +≫ ℕ-Prop.*-assoc (2 ℕ.^ suc x₀) x′ _)) ⟩
      suc (2* (y′ ℕ.+ (2 ℕ.^ suc x₀ ℕ.* x′ ℕ.* suc (2* y′))))
    ≡˘⟨ cong suc (cong 2*_ (y′ +≫ suc (2* y′) ≪* 2^-homo (suc x₀) x′)) ⟩
      suc (2* (y′ ℕ.+ ((2^ suc x₀ * x′) ℕ.* suc (2* y′))))
    ≡⟨ cong suc (double-distrib-+ y′ _) ⟩
      suc ((2* y′) ℕ.+ (2* ((2^ suc x₀ * x′) ℕ.* suc (2* y′))))
    ≡⟨⟩
      1 ℕ.+ ((2* y′) ℕ.+ (2* ((2^ suc x₀ * x′) ℕ.* (1 ℕ.+ (2* y′)))))
    ≡˘⟨ ℕ-Prop.+-assoc 1 (2* y′) _ ⟩
      1 ℕ.+ (2* y′) ℕ.+ (2* ((2^ suc x₀ * x′) ℕ.* (1 ℕ.+ (2* y′))))
    ≡⟨ (1 ℕ.+ (2* y′) +≫ 2*-homo ((2^ suc x₀ * x′) ℕ.* (1 ℕ.+ (2* y′)))) ⟩
      1 ℕ.+ (2* y′) ℕ.+ (2 ℕ.* ((2^ suc x₀ * x′) ℕ.* (1 ℕ.+ (2* y′))))
    ≡˘⟨ (1 ℕ.+ (2* y′)) +≫ ℕ-Prop.*-assoc 2 (2^ suc x₀ * x′) _ ⟩
      1 ℕ.+ (2* y′) ℕ.+ ((2 ℕ.* (2^ suc x₀ * x′)) ℕ.* (1 ℕ.+ (2* y′)))
    ≡˘⟨ _ ≪+ ℕ-Prop.*-identityˡ (1 ℕ.+ (2* y′)) ⟩
      1 ℕ.* (1 ℕ.+ (2* y′)) ℕ.+ ((2 ℕ.* (2^ suc x₀ * x′)) ℕ.* (1 ℕ.+ (2* y′)))
    ≡˘⟨ ℕ-Prop.*-distribʳ-+ (1 ℕ.+ (2* y′)) 1 (2 ℕ.* (2^ suc x₀ * x′)) ⟩
      (1 ℕ.+ (2 ℕ.* (2^ suc x₀ * x′))) ℕ.* (1 ℕ.+ (2* y′))
    ≡⟨⟩
      suc (2 ℕ.* (2^ suc x₀ * x′)) ℕ.* (suc (2* y′))
    ≡˘⟨ suc (2* y′) ≪* cong suc (2*-homo (2^ suc x₀ * x′)) ⟩
      suc (2* (2^ suc x₀ * x′)) ℕ.* suc (2* y′)
    ≡⟨⟩
      ⟦ zero 1& 0< x₀ 0& x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁
    ∎
  ⟨1*s⟩-homo (suc x₁) xs y₁ ys =
    let zs = ⟨1*s⟩ x₁ xs y₁ ys
    in
    begin
      ⟦ ⟨1*s⟩ (suc x₁) xs y₁ ys ⇓⟧₁
    ≡⟨⟩
      ⟦ 0 1& 0< 0→⟨1+1⟩ (H₁ zs) (T₁ zs) y₁ ys ⇓⟧₁
    ≡⟨⟩
      suc (2* ⟦ 0→⟨1+1⟩ (H₁ zs) (T₁ zs) y₁ ys ⇓⟧₀)
    ≡⟨ cong suc (cong 2*_ (0→⟨1+1⟩-homo (H₁ zs) (T₁ zs) y₁ ys)) ⟩
      suc (2* ⟦ zs ⇓⟧₁ ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁)
    ≡⟨ cong suc (cong 2*_ (⟦ y₁ 1& ys ⇓⟧₁ ≪+ ⟨1*s⟩-homo x₁ xs y₁ ys)) ⟩
      suc (2* (⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁) ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁)
    ≡⟨ cong suc (2*-homo (⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁ ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁)) ⟩
      suc (2 ℕ.* (⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁ ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁))
    ≡⟨ cong suc (ℕ-Prop.*-distribˡ-+ 2 (⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁) ⟦ y₁ 1& ys ⇓⟧₁) ⟩
      suc (2 ℕ.* (⟦ x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁) ℕ.+ 2 ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
    ≡⟨ {!!} ⟩
      ⟦ suc x₁ 1& xs ⇓⟧₁ ℕ.* ⟦ suc y₁ 1& ys ⇓⟧₁
    ∎

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
*-homo (0< B₀ x₀ 0& xs) (0< B₀ y₀ 0& y₁ 1& ys) =
  begin
    ⟦ (0< B₀ x₀ 0& xs) * (0< B₀ y₀ 0& y₁ 1& ys) ⇓⟧
  ≡⟨⟩
    2^ suc (suc x₀ ℕ.+ y₀) * ⟦ ⟨1*1⟩ y₁ ys xs ⇓⟧₁
  ≡⟨ cong (2^ suc (suc x₀ ℕ.+ y₀) *_) (⟨1*1⟩-homo y₁ ys xs) ⟩
    2^ suc (suc x₀ ℕ.+ y₀) * ⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁
  ≡⟨ 2^-homo (suc (suc x₀ ℕ.+ y₀)) _ ⟩
    2 ℕ.^ suc (suc x₀ ℕ.+ y₀) ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡˘⟨ cong (λ p → 2 ℕ.^ suc p ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)) (ℕ-Prop.+-suc x₀ y₀) ⟩
    2 ℕ.^ suc (x₀ ℕ.+ suc y₀) ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡⟨ _ ≪* ℕ-Prop.^-distribˡ-+-* 2 (suc x₀) (suc y₀) ⟩
    (2 ℕ.^ suc x₀ ℕ.* 2 ℕ.^ suc y₀) ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡⟨ ℕ-Prop.*-assoc (2 ℕ.^ suc x₀) (2 ℕ.^ suc y₀) _ ⟩
    2 ℕ.^ suc x₀ ℕ.* (2 ℕ.^ suc y₀ ℕ.* (⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁))
  ≡˘⟨ 2 ℕ.^ suc x₀ *≫ ℕ-Prop.*-assoc (2 ℕ.^ suc y₀) ⟦ xs ⇓⟧₁ _ ⟩
    2 ℕ.^ suc x₀ ℕ.* (2 ℕ.^ suc y₀ ℕ.* ⟦ xs ⇓⟧₁ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡⟨ 2 ℕ.^ suc x₀ *≫ ⟦ y₁ 1& ys ⇓⟧₁ ≪* ℕ-Prop.*-comm (2 ℕ.^ suc y₀) ⟦ xs ⇓⟧₁ ⟩
    2 ℕ.^ suc x₀ ℕ.* (⟦ xs ⇓⟧₁ ℕ.* 2 ℕ.^ suc y₀ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡⟨ 2 ℕ.^ suc x₀ *≫ ℕ-Prop.*-assoc ⟦ xs ⇓⟧₁ (2 ℕ.^ suc y₀) _ ⟩
    2 ℕ.^ suc x₀ ℕ.* (⟦ xs ⇓⟧₁ ℕ.* (2 ℕ.^ suc y₀ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁))
  ≡˘⟨ ℕ-Prop.*-assoc (2 ℕ.^ suc x₀) ⟦ xs ⇓⟧₁ _ ⟩
    (2 ℕ.^ suc x₀ ℕ.* ⟦ xs ⇓⟧₁) ℕ.* (2 ℕ.^ suc y₀ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡˘⟨ _ ≪* 2^-homo (suc x₀) ⟦ xs ⇓⟧₁ ⟩
    ⟦ x₀ 0& xs ⇓⟧₀ ℕ.* (2 ℕ.^ suc y₀ ℕ.* ⟦ y₁ 1& ys ⇓⟧₁)
  ≡˘⟨ ⟦ x₀ 0& xs ⇓⟧₀ *≫ 2^-homo (suc y₀) ⟦ y₁ 1& ys ⇓⟧₁ ⟩
    ⟦ 0< B₀ x₀ 0& xs ⇓⟧ ℕ.* ⟦ 0< B₀ y₀ 0& y₁ 1& ys ⇓⟧
  ∎
