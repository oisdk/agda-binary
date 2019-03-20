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

mutual
  0→⟨0+0⟩-homo : ∀ x₀ xs y₀ ys
               → ⟦ 0< B₀ 0→⟨0+0⟩ x₀ xs y₀ ys ⇓⟧ ≡ ⟦ 0< B₀ x₀ 0& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧
  0→⟨0+0⟩-homo zero (x₁ 1& xs) zero (y₁ 1& ys) = cong 2*_ (0→⟨1+1⟩-homo x₁ xs y₁ ys) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _
  0→⟨0+0⟩-homo zero (x₁ 1& xs) (suc y₀) ys = cong 2*_ (0→⟨1+0⟩-homo x₁ xs y₀ ys) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _
  0→⟨0+0⟩-homo (suc x₀) xs zero (y₁ 1& ys) = cong 2*_ (0→⟨1+0⟩-homo y₁ ys x₀ xs) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧ _ ⟨ trans ⟩ ℕ-Prop.+-comm (2* ⟦ 0< B₁ y₁ 1& ys ⇓⟧) _
  0→⟨0+0⟩-homo (suc x₀) xs (suc y₀) ys = cong 2*_ (0→⟨0+0⟩-homo x₀ xs y₀ ys) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₀ x₀ 0& xs ⇓⟧ _

  0→⟨1+0?⟩-homo : ∀ ys xs → ⟦ 0→⟨1+0?⟩ ys xs ⇓⟧₁ ≡ ⟦ xs ⇓⟧≤ ℕ.+ ⟦ ys ⇓⟧₁
  0→⟨1+0?⟩-homo ys 0₂ = refl
  0→⟨1+0?⟩-homo (y₁ 1& ys) (0< x₀ 0& xs) = 0→⟨1+0⟩-homo y₁ ys x₀ xs ⟨ trans ⟩ ℕ-Prop.+-comm _ ⟦ 0< x₀ 0& xs ⇓⟧≤

  0→⟨0?+0⟩-homo : ∀ xs y₀ ys → ⟦ 0→⟨0?+0⟩ xs y₀ ys ⇓⟧₀ ≡ ⟦ xs ⇓⟧≤ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀
  0→⟨0?+0⟩-homo 0₂ y₀ ys = refl
  0→⟨0?+0⟩-homo (0< x₀ 0& xs) y₀ ys = 0→⟨0+0⟩-homo x₀ xs y₀ ys

  0→⟨1+0⟩-homo : ∀ x₁ xs y₀ ys
        → ⟦ 0< B₁ 0→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧ ≡ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₀ y₀ 0& ys ⇓⟧
  0→⟨1+0⟩-homo zero xs zero ys = cong suc (cong 2*_ (0→⟨1+0?⟩-homo ys xs) ⟨ trans ⟩ double-distrib-+ ⟦ xs ⇓⟧≤ ⟦ ys ⇓⟧₁)
  0→⟨1+0⟩-homo zero xs (suc y₀) ys = cong suc (cong 2*_ (0→⟨0?+0⟩-homo xs y₀ ys) ⟨ trans ⟩ double-distrib-+ ⟦ xs ⇓⟧≤ _)
  0→⟨1+0⟩-homo (suc x₁) xs zero (y₁ 1& ys) = cong suc (cong 2*_ (0→⟨1+1⟩-homo x₁ xs y₁ ys) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _)
  0→⟨1+0⟩-homo (suc x₁) xs (suc y₀) ys = cong suc (cong 2*_ (0→⟨1+0⟩-homo x₁ xs y₀ ys) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _)

  1→⟨0?+0?⟩-homo : ∀ xs ys → ⟦ 1→⟨0?+0?⟩ xs ys ⇓⟧₁ ≡ suc (⟦ xs ⇓⟧≤ ℕ.+ ⟦ ys ⇓⟧≤)
  1→⟨0?+0?⟩-homo 0₂ 0₂ = refl
  1→⟨0?+0?⟩-homo 0₂ (0< y₀ 0& ys) = carry-homo y₀ ys
  1→⟨0?+0?⟩-homo (0< x₀ 0& xs) 0₂ = carry-homo x₀ xs ⟨ trans ⟩ cong suc (sym (ℕ-Prop.+-identityʳ _))
  1→⟨0?+0?⟩-homo (0< x₀ 0& xs) (0< y₀ 0& ys) = 1→⟨0+0⟩-homo x₀ xs y₀ ys

  carry-homo : ∀ x₀ xs → ⟦ carry x₀ xs ⇓⟧₁ ≡ suc ⟦ x₀ 0& xs ⇓⟧₀
  carry-homo zero xs = refl
  carry-homo (suc x₀) xs = refl

  0→⟨1+1⟩-homo : ∀ x₁ xs y₁ ys
        → ⟦ 0< B₀ 0→⟨1+1⟩ x₁ xs y₁ ys ⇓⟧ ≡ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ ℕ.+ ⟦ 0< B₁ y₁ 1& ys ⇓⟧
  0→⟨1+1⟩-homo zero xs zero ys = (cong 2*_ (1→⟨0?+0?⟩-homo xs ys)) ⟨ trans ⟩ odd-double-distrib-+ ⟦ xs ⇓⟧≤ ⟦ ys ⇓⟧≤
  0→⟨1+1⟩-homo zero xs (suc y₁) ys = cong 2*_ (1→⟨1+0?⟩-homo y₁ ys xs) ⟨ trans ⟩ (cong 2*_ (cong suc (ℕ-Prop.+-comm _ ⟦ xs ⇓⟧≤)) ⟨ trans ⟩ odd-double-distrib-+ ⟦ xs ⇓⟧≤ ⟦ y₁ 1& ys ⇓⟧₁ )
  0→⟨1+1⟩-homo (suc x₁) xs zero ys = cong 2*_ (1→⟨1+0?⟩-homo x₁ xs ys) ⟨ trans ⟩ odd-double-distrib-+ ⟦ x₁ 1& xs ⇓⟧₁ _
  0→⟨1+1⟩-homo (suc x₁) xs (suc y₁) ys = cong 2*_ (1→⟨1+1⟩-homo x₁ xs y₁ ys) ⟨ trans ⟩ odd-double-distrib-+ ⟦ x₁ 1& xs ⇓⟧₁ _

  1→⟨0+0⟩-homo : ∀ x₀ xs y₀ ys → ⟦ 1→⟨0+0⟩ x₀ xs y₀ ys ⇓⟧₁ ≡ suc (⟦ x₀ 0& xs ⇓⟧₀ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀)
  1→⟨0+0⟩-homo zero (x₁ 1& xs) zero (y₁ 1& ys) = cong suc (cong 2*_ (0→⟨1+1⟩-homo x₁ xs y₁ ys)) ⟨ trans ⟩ cong suc (double-distrib-+ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _)
  1→⟨0+0⟩-homo zero (x₁ 1& xs) (suc y₀) ys = cong suc (cong 2*_ (0→⟨1+0⟩-homo x₁ xs y₀ ys)) ⟨ trans ⟩ cong suc (double-distrib-+ ⟦ 0< B₁ x₁ 1& xs ⇓⟧ _)
  1→⟨0+0⟩-homo (suc x₀) xs zero (y₁ 1& ys) = cong suc (cong 2*_ (0→⟨1+0⟩-homo y₁ ys x₀ xs) ⟨ trans ⟩ (cong 2*_ (ℕ-Prop.+-comm ⟦ 0< B₁ y₁ 1& ys ⇓⟧ ⟦ 0< B₀ x₀ 0& xs ⇓⟧) ⟨ trans ⟩ double-distrib-+ ⟦ 0< B₀ x₀ 0& xs ⇓⟧ ⟦ 0< B₁ y₁ 1& ys ⇓⟧ ))
  1→⟨0+0⟩-homo (suc x₀) xs (suc y₀) ys = cong suc (cong 2*_ (0→⟨0+0⟩-homo x₀ xs y₀ ys)) ⟨ trans ⟩ cong suc (double-distrib-+ ⟦ x₀ 0& xs ⇓⟧₀ ⟦ y₀ 0& ys ⇓⟧₀)

  1→⟨1+0?⟩-homo : ∀ x₁ xs ys → ⟦ 1→⟨1+0?⟩ x₁ xs ys ⇓⟧₀ ≡ suc (⟦ x₁ 1& xs ⇓⟧₁ ℕ.+ ⟦ ys ⇓⟧≤)
  1→⟨1+0?⟩-homo x₁ xs 0₂ = inc-homo (0< B₁ x₁ 1& xs) ⟨ trans ⟩ cong suc (sym (ℕ-Prop.+-identityʳ ⟦ x₁ 1& xs ⇓⟧₁))
  1→⟨1+0?⟩-homo x₁ xs (0< y₀ 0& ys) = 1→⟨1+0⟩-homo x₁ xs y₀ ys

  1→⟨0?+0⟩-homo : ∀ xs y₀ ys → ⟦ 1→⟨0?+0⟩ xs y₀ ys ⇓⟧₁ ≡ suc (⟦ xs ⇓⟧≤ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀)
  1→⟨0?+0⟩-homo 0₂ y₀ ys = carry-homo y₀ ys
  1→⟨0?+0⟩-homo (0< x₀ 0& xs) y₀ ys = 1→⟨0+0⟩-homo x₀ xs y₀ ys

  1→⟨1+0⟩-homo : ∀ x₁ xs y₀ ys → ⟦ 1→⟨1+0⟩ x₁ xs y₀ ys ⇓⟧₀ ≡ suc (⟦ x₁ 1& xs ⇓⟧₁ ℕ.+ ⟦ y₀ 0& ys ⇓⟧₀)
  1→⟨1+0⟩-homo zero xs zero (y₁ 1& ys) = cong 2*_ (1→⟨1+0?⟩-homo y₁ ys xs) ⟨ trans ⟩ (double-distrib-+-lsuc ⟦ y₁ 1& ys ⇓⟧₁ _ ⟨ trans ⟩ cong suc (cong suc (ℕ-Prop.+-comm _ (2* ⟦ xs ⇓⟧≤))))
  1→⟨1+0⟩-homo zero xs (suc y₀) ys = cong 2*_ (1→⟨0?+0⟩-homo xs y₀ ys) ⟨ trans ⟩ double-distrib-+-lsuc ⟦ xs ⇓⟧≤ ⟦ y₀ 0& ys ⇓⟧₀
  1→⟨1+0⟩-homo (suc x₁) xs zero (y₁ 1& ys) = cong 2*_ (1→⟨1+1⟩-homo x₁ xs y₁ ys) ⟨ trans ⟩ double-distrib-+-lsuc ⟦ x₁ 1& xs ⇓⟧₁ _
  1→⟨1+0⟩-homo (suc x₁) xs (suc y₀) ys = cong 2*_ (1→⟨1+0⟩-homo x₁ xs y₀ ys) ⟨ trans ⟩ double-distrib-+-lsuc ⟦ x₁ 1& xs ⇓⟧₁ ⟦ y₀ 0& ys ⇓⟧₀

  1→⟨1+1⟩-homo : ∀ x₁ xs y₁ ys → ⟦ 1→⟨1+1⟩ x₁ xs y₁ ys ⇓⟧₁ ≡ suc (⟦ x₁ 1& xs ⇓⟧₁ ℕ.+ ⟦ y₁ 1& ys ⇓⟧₁)
  1→⟨1+1⟩-homo zero xs zero ys = cong suc (cong 2*_ (1→⟨0?+0?⟩-homo xs ys) ⟨ trans ⟩ odd-double-distrib-+ ⟦ xs ⇓⟧≤ ⟦ ys ⇓⟧≤)
  1→⟨1+1⟩-homo zero xs (suc y₁) ys = cong suc ((cong 2*_ (1→⟨1+0?⟩-homo y₁ ys xs)) ⟨ trans ⟩ (odd-double-distrib-+ ⟦ y₁ 1& ys ⇓⟧₁ ⟦ xs ⇓⟧≤ ⟨ trans ⟩ ℕ-Prop.+-comm (suc (2* ⟦ y₁ 1& ys ⇓⟧₁)) (suc (2* ⟦ xs ⇓⟧≤))))
  1→⟨1+1⟩-homo (suc x₁) xs zero ys = cong suc ((cong 2*_ (1→⟨1+0?⟩-homo x₁ xs ys)) ⟨ trans ⟩ odd-double-distrib-+ ⟦ x₁ 1& xs ⇓⟧₁ ⟦ ys ⇓⟧≤)
  1→⟨1+1⟩-homo (suc x₁) xs (suc y₁) ys = cong suc (cong 2*_ (1→⟨1+1⟩-homo x₁ xs y₁ ys) ⟨ trans ⟩ odd-double-distrib-+ ⟦ x₁ 1& xs ⇓⟧₁ ⟦ y₁ 1& ys ⇓⟧₁)

+-homo : ∀ x y → ⟦ x + y ⇓⟧ ≡ ⟦ x ⇓⟧ ℕ.+ ⟦ y ⇓⟧
+-homo 0₂ y = refl
+-homo (0< xs) 0₂ = sym (ℕ-Prop.+-identityʳ _)
+-homo (0< B₀ x₀ 0& xs) (0< B₀ y₀ 0& ys) = 0→⟨0+0⟩-homo x₀ xs y₀ ys
+-homo (0< B₀ x₀ 0& xs) (0< B₁ y₁ 1& ys) = 0→⟨1+0⟩-homo y₁ ys x₀ xs ⟨ trans ⟩ ℕ-Prop.+-comm (⟦ y₁ 1& ys ⇓⟧₁) ⟦ x₀ 0& xs ⇓⟧₀
+-homo (0< B₁ x₁ 1& xs) (0< B₀ y₀ 0& ys) = 0→⟨1+0⟩-homo x₁ xs y₀ ys
+-homo (0< B₁ x₁ 1& xs) (0< B₁ y₁ 1& ys) = 0→⟨1+1⟩-homo x₁ xs y₁ ys
