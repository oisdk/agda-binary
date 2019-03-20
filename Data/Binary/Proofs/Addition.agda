{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Addition where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕ-Prop
open import Function
open import Data.Binary.Operations.Unary
open import Data.Binary.Proofs.Unary
open import Data.Nat.Reasoning
open import Data.Binary.Proofs.Lemmas

suc₀-homo : ∀ xs → ⟦ suc₀ xs ⇓⟧₀ ≡ 2 ℕ.* ⟦ xs ⇓⟧₀
suc₀-homo xs = ℕ-Prop.*-assoc 2 (2^ H₀ xs +1) _

suc₁-homo : ∀ xs → ⟦ suc₁ xs ⇓⟧₁⁺¹ ≡ 2 ℕ.* ⟦ xs ⇓⟧₁⁺¹
suc₁-homo xs = ℕ-Prop.*-assoc 2 (2^ H₁ xs +1) _

mutual
  0→⟨0+0⟩-homo : ∀ x₀ xs y₀ ys
               → ⟦ 0< B₀ 0→⟨0+0⟩ x₀ xs y₀ ys ⇓⟧ ≡ ⟦ 0< B₀ x₀ 0& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧
  0→⟨0+0⟩-homo zero (x₁ 1& xs) zero (y₁ 1& ys) =
    begin
      ⟦ suc₀ 0→⟨1+1⟩ x₁ xs y₁ ys ⇓⟧₀
    ≡⟨ suc₀-homo (0→⟨1+1⟩ x₁ xs y₁ ys) ⟩
      2 ℕ.* ⟦ 0→⟨1+1⟩ x₁ xs y₁ ys ⇓⟧₀
    ≡⟨ 2 *≫ 0→⟨1+1⟩-homo x₁ xs y₁ ys ⟩
      2 ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧)
    ≡⟨ ℕ-Prop.*-distribˡ-+ 2 ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ⟦ 0< B₁ y₁ 1& ys ⇓⟧ ⟩
      2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ 2 ℕ.* ⟦ 0< B₁ y₁ 1& ys ⇓⟧
    ≡⟨⟩
      ⟦ zero 0& x₁ 1& xs ⇓⟧₀ ℕ.+ ⟦ zero 0& y₁ 1& ys ⇓⟧₀
    ∎
  0→⟨0+0⟩-homo zero (x₁ 1& xs) (suc y₀) ys =
    begin
      ⟦ 0 0& 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧₀
    ≡⟨⟩
      2 ℕ.* ⟦ 0< B₁ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧
    ≡⟨ 2 *≫ 0→⟨1+0⟩-homo x₁ xs y₀ ys ⟩
      2 ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧)
    ≡⟨ ℕ-Prop.*-distribˡ-+ 2 ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _ ⟩
      2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ 2 ℕ.* ⟦ 0< B₀ y₀ 0& ys ⇓⟧
    ≡˘⟨ (2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧) +≫ suc₀-homo (y₀ 0& ys) ⟩
      ⟦ zero 0& x₁ 1& xs ⇓⟧₀ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀
    ∎
  0→⟨0+0⟩-homo (suc y₀) ys zero (x₁ 1& xs) =
    begin
      ⟦ 0 0& 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧₀
    ≡⟨⟩
      2 ℕ.* ⟦ 0< B₁ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧
    ≡⟨ 2 *≫ 0→⟨1+0⟩-homo x₁ xs y₀ ys ⟩
      2 ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧)
    ≡⟨ ℕ-Prop.*-distribˡ-+ 2 ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _ ⟩
      2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ 2 ℕ.* ⟦ 0< B₀ y₀ 0& ys ⇓⟧
    ≡˘⟨ (2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧) +≫ suc₀-homo (y₀ 0& ys) ⟩
      ⟦ zero 0& x₁ 1& xs ⇓⟧₀ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀
    ≡⟨ ℕ-Prop.+-comm ⟦ 0 0& x₁ 1& xs ⇓⟧₀ _ ⟩
      ⟦ suc y₀ 0& ys ⇓⟧₀ ℕ.+ ⟦ zero 0& x₁ 1& xs ⇓⟧₀
    ∎
  0→⟨0+0⟩-homo (suc x₀) xs (suc y₀) ys =
    begin
      ⟦ suc₀ 0→⟨0+0⟩ x₀ xs y₀ ys ⇓⟧₀
    ≡⟨ suc₀-homo (0→⟨0+0⟩ x₀ xs y₀ ys)  ⟩
      2 ℕ.* ⟦ 0→⟨0+0⟩ x₀ xs y₀ ys ⇓⟧₀
    ≡⟨ 2 *≫ 0→⟨0+0⟩-homo x₀ xs y₀ ys ⟩
      2 ℕ.* (⟦ x₀ 0& xs ⇓⟧₀ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀)
    ≡⟨ ℕ-Prop.*-distribˡ-+ 2 ⟦ x₀ 0& xs ⇓⟧₀ ⟦ y₀ 0& ys ⇓⟧₀ ⟩
      2 ℕ.* ⟦ x₀ 0& xs ⇓⟧₀ ℕ.+ 2 ℕ.* ⟦ y₀ 0& ys ⇓⟧₀
    ≡˘⟨ 2 ℕ.* ⟦ x₀ 0& xs ⇓⟧₀ +≫ suc₀-homo (y₀ 0& ys) ⟩
      2 ℕ.* ⟦ x₀ 0& xs ⇓⟧₀ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀
    ≡˘⟨ ⟦ suc y₀ 0& ys ⇓⟧₀ ≪+ suc₀-homo (x₀ 0& xs) ⟩
      ⟦ suc x₀ 0& xs ⇓⟧₀ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀
    ∎

  0→⟨1+0?⟩-homo : ∀ ys xs → ℕ.pred ⟦ 0→⟨1+0?⟩ ys xs ⇓⟧₁⁺¹ ≡ ⟦ xs ⇓⟧≤ ℕ.+ ℕ.pred ⟦ ys ⇓⟧₁⁺¹
  0→⟨1+0?⟩-homo ys 0₂ = refl
  0→⟨1+0?⟩-homo (y₁ 1& ys) (0< x₀ 0& xs) = 0→⟨1+0⟩-homo y₁ ys x₀ xs ⟨ trans ⟩ ℕ-Prop.+-comm _ ⟦ 0< x₀ 0& xs ⇓⟧≤

  0→⟨1+0⟩-homo : ∀ x₁ xs y₀ ys
        → ⟦ 0< B₁ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧ ≡ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧
  0→⟨1+0⟩-homo zero xs zero ys =
    begin
      ℕ.pred ⟦ suc₁ 0→⟨1+0?⟩ ys xs ⇓⟧₁⁺¹
    ≡⟨ cong ℕ.pred (suc₁-homo (0→⟨1+0?⟩ ys xs)) ⟩
      ℕ.pred (2 ℕ.* ⟦ 0→⟨1+0?⟩ ys xs ⇓⟧₁⁺¹)
    ≡⟨ pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (0→⟨1+0?⟩ ys xs)) ⟩
      suc (2 ℕ.* ℕ.pred ⟦ 0→⟨1+0?⟩ ys xs ⇓⟧₁⁺¹)
    ≡⟨ cong suc (2 *≫ 0→⟨1+0?⟩-homo ys xs)  ⟩
      suc (2 ℕ.* (⟦ xs ⇓⟧≤ ℕ.+ ℕ.pred ⟦ ys ⇓⟧₁⁺¹))
    ≡⟨ cong suc (ℕ-Prop.*-distribˡ-+ 2 ⟦ xs ⇓⟧≤ _) ⟩
      suc ((2 ℕ.* ⟦ xs ⇓⟧≤) ℕ.+ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹))
    ≡⟨⟩
      1 ℕ.+ ((2 ℕ.* ⟦ xs ⇓⟧≤) ℕ.+ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹))
    ≡˘⟨ ℕ-Prop.+-assoc 1 (2 ℕ.* ⟦ xs ⇓⟧≤) _ ⟩
      1 ℕ.+ (2 ℕ.* ⟦ xs ⇓⟧≤) ℕ.+ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹)
    ≡⟨⟩
      suc (2 ℕ.* ⟦ xs ⇓⟧≤) ℕ.+ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹)
    ≡⟨⟩
      suc (2 ℕ.* ℕ.pred (suc ⟦ xs ⇓⟧≤)) ℕ.+ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹)
    ≡˘⟨ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹) ≪+ pred-distrib-2* {suc ⟦ xs ⇓⟧≤} (λ ()) ⟩
      ℕ.pred (2 ℕ.* suc ⟦ xs ⇓⟧≤) ℕ.+ (2 ℕ.* ℕ.pred ⟦ ys ⇓⟧₁⁺¹)
    ≡⟨⟩
      ⟦ 0< B₁ 0 1& xs ⇓⟧ ℕ.+ ⟦ 0 0& ys ⇓⟧₀
    ∎
  0→⟨1+0⟩-homo zero xs (suc y₀) ys = {!!}
  0→⟨1+0⟩-homo (suc x₁) xs zero ys = {!!}
  0→⟨1+0⟩-homo (suc x₁) xs (suc y₀) ys =
    begin
      ℕ.pred ⟦ suc₁ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧₁⁺¹
    ≡⟨ cong ℕ.pred (suc₁-homo (0→⟨1+0⟩ x₁ xs y₀ ys)) ⟩
      ℕ.pred (2 ℕ.* ⟦ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧₁⁺¹)
    ≡⟨ pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (0→⟨1+0⟩ x₁ xs y₀ ys)) ⟩
      suc (2 ℕ.* ℕ.pred ⟦ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧₁⁺¹)
    ≡⟨ cong suc (2 *≫ 0→⟨1+0⟩-homo x₁ xs y₀ ys) ⟩
      suc (2 ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧))
    ≡⟨ cong suc (ℕ-Prop.*-distribˡ-+ 2 ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _) ⟩
      suc (2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ 2 ℕ.* ⟦ 0< B₀ y₀ 0& ys ⇓⟧)
    ≡⟨⟩
      suc (2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧) ℕ.+ 2 ℕ.* ⟦ 0< B₀ y₀ 0& ys ⇓⟧
    ≡˘⟨ _ ≪+ pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (x₁ 1& xs)) ⟩
      ℕ.pred (2 ℕ.* ⟦ x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ 2 ℕ.* ⟦ 0< B₀ y₀ 0& ys ⇓⟧
    ≡˘⟨ _ ≪+ cong ℕ.pred (suc₁-homo (x₁ 1& xs)) ⟩
      ℕ.pred (⟦ suc x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ 2 ℕ.* ⟦ 0< B₀ y₀ 0& ys ⇓⟧
    ≡˘⟨ _ +≫ suc₀-homo (y₀ 0& ys) ⟩
      ℕ.pred ⟦ suc x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀
    ∎

  0→⟨1+1⟩′-homo : ∀ x₁ xs y₁ ys → ⟦ 0→⟨1+1⟩′ x₁ xs y₁ ys ⇓⟧₁⁺¹ ≡ ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁⁺¹
  0→⟨1+1⟩′-homo zero xs zero ys = {!!}
  0→⟨1+1⟩′-homo zero xs (suc y₁) ys = {!!}
  0→⟨1+1⟩′-homo (suc x₁) xs zero ys = {!!}
  0→⟨1+1⟩′-homo (suc x₁) xs (suc y₁) ys = {!!}

  0→⟨1+1⟩-homo : ∀ x₁ xs y₁ ys
        → ⟦ 0< B₀ 0→⟨1+1⟩ x₁ xs y₁ ys ⇓⟧ ≡ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧
  0→⟨1+1⟩-homo zero xs zero ys = {!!}
  0→⟨1+1⟩-homo zero xs (suc y₁) ys = {!!}
  0→⟨1+1⟩-homo (suc x₁) xs zero ys = {!!}
  0→⟨1+1⟩-homo (suc x₁) xs (suc y₁) ys =
    begin
      ⟦ 0 0& 0→⟨1+1⟩′ x₁ xs y₁ ys ⇓⟧₀
    ≡⟨⟩
      2 ℕ.* ℕ.pred ⟦ 0→⟨1+1⟩′ x₁ xs y₁ ys ⇓⟧₁⁺¹
    ≡⟨ 2 *≫ cong ℕ.pred (0→⟨1+1⟩′-homo x₁ xs y₁ ys) ⟩
      2 ℕ.* ℕ.pred (⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁⁺¹)
    ≡⟨ 2 *≫ pred-distrib-both (⟦x⇓⟧₁⁺¹≢0 (x₁ 1& xs)) ((⟦x⇓⟧₁⁺¹≢0 (y₁ 1& ys))) ⟩
      2 ℕ.* suc (ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ℕ.pred ⟦ y₁ 1& ys ⇓⟧₁⁺¹)
    ≡⟨ suc-double _ ⟩
      suc (suc (2 ℕ.* (ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ℕ.pred ⟦ y₁ 1& ys ⇓⟧₁⁺¹)))
    ≡⟨ cong suc (cong suc (ℕ-Prop.*-distribˡ-+ 2 (ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹) _)) ⟩
      suc (suc (2 ℕ.* ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ 2 ℕ.* ℕ.pred ⟦ y₁ 1& ys ⇓⟧₁⁺¹)
    ≡˘⟨ cong suc (ℕ-Prop.+-suc _ _) ⟩
      suc (2 ℕ.* ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ suc (2 ℕ.* ℕ.pred ⟦ y₁ 1& ys ⇓⟧₁⁺¹)
    ≡˘⟨ _ +≫ pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (y₁ 1& ys)) ⟩
      suc (2 ℕ.* ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ ℕ.pred (2 ℕ.* ⟦ y₁ 1& ys ⇓⟧₁⁺¹)
    ≡˘⟨ _ ≪+ pred-distrib-2* (⟦x⇓⟧₁⁺¹≢0 (x₁ 1& xs)) ⟩
      ℕ.pred (2 ℕ.* ⟦ x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ ℕ.pred (2 ℕ.* ⟦ y₁ 1& ys ⇓⟧₁⁺¹)
    ≡˘⟨ _ +≫ cong ℕ.pred (suc₁-homo (y₁ 1& ys)) ⟩
      ℕ.pred (2 ℕ.* ⟦ x₁ 1& xs ⇓⟧₁⁺¹) ℕ.+ ℕ.pred ⟦ suc y₁ 1& ys ⇓⟧₁⁺¹
    ≡˘⟨ _ ≪+ cong ℕ.pred (suc₁-homo (x₁ 1& xs)) ⟩
      ℕ.pred ⟦ suc x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ℕ.pred ⟦ suc y₁ 1& ys ⇓⟧₁⁺¹
    ∎

+-homo : ∀ x y → ⟦ x + y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧
+-homo 0₂ y = refl
+-homo (0< xs) 0₂ = sym (ℕ-Prop.+-identityʳ _)
+-homo (0< B₀ x₀ 0& xs) (0< B₀ y₀ 0& ys) = 0→⟨0+0⟩-homo x₀ xs y₀ ys
+-homo (0< B₀ x₀ 0& xs) (0< B₁ y₁ 1& ys) = 0→⟨1+0⟩-homo y₁ ys x₀ xs ⟨ trans ⟩ ℕ-Prop.+-comm (ℕ.pred ⟦ y₁ 1& ys ⇓⟧₁⁺¹) ⟦ x₀ 0& xs ⇓⟧₀
+-homo (0< B₁ x₁ 1& xs) (0< B₀ y₀ 0& ys) = 0→⟨1+0⟩-homo x₁ xs y₀ ys
+-homo (0< B₁ x₁ 1& xs) (0< B₁ y₁ 1& ys) = 0→⟨1+1⟩-homo x₁ xs y₁ ys
