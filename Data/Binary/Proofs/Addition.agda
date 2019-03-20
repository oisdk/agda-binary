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

lemma₆ : ∀ c x y → 2 ℕ.^ suc c ℕ.* (x ℕ.+ y) ≡ 2 ℕ.^ c ℕ.* (2 ℕ.* x ℕ.+ 2 ℕ.* y)
lemma₆ c x y =
  begin
    2 ℕ.^ suc c ℕ.* (x ℕ.+ y)
  ≡⟨ cong (ℕ._* (x ℕ.+ y)) (ℕ-Prop.*-comm 2 (2 ℕ.^ c)) ⟩
    (2 ℕ.^ c ℕ.* 2) ℕ.* (x ℕ.+ y)
  ≡⟨ ℕ-Prop.*-assoc (2 ℕ.^ c) 2 _ ⟩
    2 ℕ.^ c ℕ.* (2 ℕ.* (x ℕ.+ y))
  ≡⟨ cong (2 ℕ.^ c ℕ.*_) (ℕ-Prop.*-distribˡ-+ 2 x y) ⟩
    2 ℕ.^ c ℕ.* (2 ℕ.* x ℕ.+ 2 ℕ.* y)
  ∎

-- mutual
--   0→⟨0+0⟩-homo : ∀ c x₀ xs y₀ ys
--                → ⟦ 0< B₀ 0→⟨0+0⟩ c x₀ xs y₀ ys ⇓⟧ ≡ 2 ℕ.^ c ℕ.* (⟦ 0< B₀ x₀ 0& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧)
--   0→⟨0+0⟩-homo c zero (x₁ 1& xs) zero (y₁ 1& ys) =
--     begin
--       ⟦ 0< B₀ 0→⟨1+1⟩ (suc c) x₁ xs y₁ ys ⇓⟧
--     ≡⟨ 0→⟨1+1⟩-homo (suc c) x₁ xs y₁ ys ⟩
--       2 ℕ.^ (suc c) ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧)
--     ≡⟨ lemma₆ c ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ⟦ 0< B₁ y₁ 1& ys ⇓⟧ ⟩
--       2 ℕ.^ c ℕ.* (2 ℕ.* ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ 2 ℕ.* ⟦ 0< B₁ y₁ 1& ys ⇓⟧)
--     ≡⟨⟩
--       2 ℕ.^ c ℕ.* (⟦ 0< B₀ 0 0& x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ 0 0& y₁ 1& ys ⇓⟧)
--     ∎
--   0→⟨0+0⟩-homo c zero     (x₁ 1& xs) (suc y₀) ys =
--     begin
--       ⟦ c 0& 0→⟨1+0⟩ 0 x₁ xs y₀ ys ⇓⟧₀
--     ≡⟨⟩
--       (2 ℕ.^ suc c) ℕ.* ℕ.pred ⟦ 0→⟨1+0⟩ 0 x₁ xs y₀ ys ⇓⟧₁⁺¹
--     ≡⟨ 2 ℕ.^ suc c *≫ 0→⟨1+0⟩-homo 0 x₁ xs y₀ ys ⟩
--       (2 ℕ.^ suc c) ℕ.* (1 ℕ.* (ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀))
--     ≡⟨ 2 ℕ.^ suc c *≫ ℕ-Prop.*-identityˡ _ ⟩
--       (2 ℕ.^ suc c) ℕ.* (ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀)
--     ≡⟨ {!!} ⟩
--       (2 ℕ.^ c) ℕ.* (2 ℕ.* ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ 2 ℕ.* ⟦ y₀ 0& ys ⇓⟧₀)
--     ≡⟨ {!!} ⟩
--       (2 ℕ.^ c) ℕ.* (2 ℕ.* ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀)
--     ≡⟨⟩
--       (2 ℕ.^ c) ℕ.* (⟦ zero 0& x₁ 1& xs ⇓⟧₀ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀)
--     ∎
--   0→⟨0+0⟩-homo c (suc x₀) xs         zero     (y₁ 1& ys) = {!!}
--   0→⟨0+0⟩-homo c (suc x₀) xs         (suc y₀) ys =
--     begin
--       ⟦ 0→⟨0+0⟩ (suc c) x₀ xs y₀ ys ⇓⟧₀
--     ≡⟨ 0→⟨0+0⟩-homo (suc c) x₀ xs y₀ ys ⟩
--       (2 ℕ.^ suc c) ℕ.* (⟦ x₀ 0& xs ⇓⟧₀ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀)
--     ≡⟨ lemma₆ c ⟦ x₀ 0& xs ⇓⟧₀ ⟦ y₀ 0& ys ⇓⟧₀ ⟩
--       (2 ℕ.^ c) ℕ.* (2 ℕ.* ⟦ x₀ 0& xs ⇓⟧₀ ℕ.+ 2 ℕ.* ⟦ y₀ 0& ys ⇓⟧₀)
--     ≡˘⟨ cong (2 ℕ.^ c ℕ.*_) (cong (ℕ._+ 2 ℕ.* ⟦ y₀ 0& ys ⇓⟧₀) (ℕ-Prop.*-assoc 2 (2 ℕ.^ suc x₀) (ℕ.pred ⟦ xs ⇓⟧₁⁺¹))) ⟩
--       (2 ℕ.^ c) ℕ.* (⟦ suc x₀ 0& xs ⇓⟧₀ ℕ.+ 2 ℕ.* ⟦ y₀ 0& ys ⇓⟧₀)
--     ≡˘⟨ 2 ℕ.^ c *≫ ⟦ suc x₀ 0& xs ⇓⟧₀ +≫ ℕ-Prop.*-assoc 2 (2 ℕ.^ suc y₀) (ℕ.pred ⟦ ys ⇓⟧₁⁺¹) ⟩
--       (2 ℕ.^ c) ℕ.* (⟦ suc x₀ 0& xs ⇓⟧₀ ℕ.+ ⟦ suc y₀ 0& ys ⇓⟧₀)
--     ∎


--   0→⟨1+0⟩-homo : ∀ c x₁ xs y₀ ys
--                → ⟦ 0< B₁ 0→⟨1+0⟩ c x₁ xs y₀ ys ⇓⟧ ≡ 2 ℕ.^ c ℕ.* (ℕ.pred ⟦ x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧)
--   0→⟨1+0⟩-homo c zero xs zero (y₁ 1& ys) = {!!}
--   0→⟨1+0⟩-homo c zero xs (suc y₀) ys = {!!}
--   0→⟨1+0⟩-homo c (suc x₁) xs zero ys = {!!}
--   0→⟨1+0⟩-homo c (suc x₁) xs (suc y₀) ys = {!!}

--   0→⟨1+1⟩-homo : ∀ c x₁ xs y₁ ys
--                → ⟦ 0< B₀ 0→⟨1+1⟩ c x₁ xs y₁ ys ⇓⟧ ≡ 2 ℕ.^ c ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧)
--   0→⟨1+1⟩-homo c zero xs zero ys = {!!}
--   0→⟨1+1⟩-homo c zero xs (suc y₁) ys = {!!}
--   0→⟨1+1⟩-homo c (suc x₁) xs zero ys = {!!}
--   0→⟨1+1⟩-homo c (suc x₁) xs (suc y₁) ys =
--     begin
--       ⟦ c 0& 0→⟨1+1⟩′ 0 x₁ xs y₁ ys ⇓⟧₀
--     ≡⟨⟩
--       (2 ℕ.^ suc c) ℕ.* ℕ.pred ⟦ 0→⟨1+1⟩′ zero x₁ xs y₁ ys ⇓⟧₁⁺¹
--     ≡⟨ {!!} ⟩
--       (2 ℕ.^ c) ℕ.* (ℕ.pred ⟦ suc x₁ 1& xs ⇓⟧₁⁺¹ ℕ.+ ℕ.pred ⟦ suc y₁ 1& ys ⇓⟧₁⁺¹)
--     ∎

-- -- 0→⟨1+1⟩′-homo : ∀ c x₁ xs y₁ ys → ⟦ 0< B₁ 0→⟨1+1⟩′ c x₁ xs y₁ ys ⇓⟧ ≡ 2 ℕ.^ c ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧)
-- -- 0→⟨1+1⟩′-homo c x₁ xs y₁ ys = {!!}

--   0→⟨1+0?⟩-homo : ∀ c x₁ xs ys
--     → ⟦ 0< B₁ 0→⟨1+0?⟩ c x₁ xs ys ⇓⟧ ≡ 2 ℕ.^ c ℕ.* (⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ ys ⇓⟧≤)
--   0→⟨1+0?⟩-homo = {!!}

--   0→⟨0?+0⟩-homo : ∀ xs y₀ ys → ⟦ 0< B₀ 0→⟨0?+0⟩ xs y₀ ys ⇓⟧ ≡ ⟦ xs ⇓⟧≤ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧
--   0→⟨0?+0⟩-homo = {!!}

--   1→⟨0?+0⟩-homo : ∀ c xs y₀ ys → ⟦ 0< B₁ 1→⟨0?+0⟩ c xs y₀ ys ⇓⟧ ≡ 2 ℕ.^ c ℕ.* (⟦ xs ⇓⟧≤ ℕ.+ ⟦ 0< B₀ y₀ 0& ys  ⇓⟧)
--   1→⟨0?+0⟩-homo = {!!}

--   1→⟨0?+0?⟩-homo : ∀ c xs ys → ⟦ 1→⟨0?+0?⟩ c xs ys ⇓⟧₁⁺¹ ≡ 2 ℕ.^ suc c ℕ.* suc (⟦ xs ⇓⟧≤ ℕ.+ ⟦ ys ⇓⟧≤)
--   1→⟨0?+0?⟩-homo c 0₂ 0₂ = refl
--   1→⟨0?+0?⟩-homo c 0₂ (0< xs) = {!!} -- carry-homo c xs
--   1→⟨0?+0?⟩-homo c (0< xs) 0₂ = {!!}
--   1→⟨0?+0?⟩-homo c (0< x₀ 0& xs) (0< y₀ 0& ys) = {!!}


+-homo : ∀ x y → ⟦ x + y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧
+-homo 0₂ y = refl
+-homo (0< xs) 0₂ = sym (ℕ-Prop.+-identityʳ _)
+-homo (0< B₀ x₀ 0& xs) (0< B₀ y₀ 0& ys) = 0→⟨0+0⟩-homo 0 x₀ xs y₀ ys ⟨ trans ⟩ ℕ-Prop.+-identityʳ _
+-homo (0< B₀ x₀ 0& xs) (0< B₁ y₁ 1& ys) = 0→⟨1+0⟩-homo 0 y₁ ys x₀ xs ⟨ trans ⟩ (ℕ-Prop.+-identityʳ _ ⟨ trans ⟩ ℕ-Prop.+-comm (ℕ.pred ⟦ y₁ 1& ys ⇓⟧₁⁺¹) ⟦ x₀ 0& xs ⇓⟧₀)
+-homo (0< B₁ x₁ 1& xs) (0< B₀ y₀ 0& ys) = 0→⟨1+0⟩-homo 0 x₁ xs y₀ ys ⟨ trans ⟩ ℕ-Prop.+-identityʳ _
+-homo (0< B₁ x₁ 1& xs) (0< B₁ y₁ 1& ys) = 0→⟨1+1⟩-homo 0 x₁ xs y₁ ys ⟨ trans ⟩ ℕ-Prop.+-identityʳ _
