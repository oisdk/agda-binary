{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Proofs.Lemmas where

open import Relation.Binary.PropositionalEquality
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Empty
import Data.Nat.Properties as ℕ-Prop
open import Data.Binary.Segmented.Operations.Semantics
open import Data.Binary.Segmented.Definitions
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Nat.Reasoning

x≢0⇒x+y≢0 : ∀ x {y} → x ≢ 0 → x ℕ.+ y ≢ 0
x≢0⇒x+y≢0 zero = λ z _ → z refl
x≢0⇒x+y≢0 (suc x) = λ _ ()

pred-distrib-2* : ∀ {x} → x ≢ 0 → ℕ.pred (2 ℕ.* x) ≡ suc (2 ℕ.* ℕ.pred x)
pred-distrib-2* {zero} p = ⊥-elim (p refl)
pred-distrib-2* {suc x} _ = ℕ-Prop.+-suc _ _

-- 2^x≢0 : ∀ x → 2^ x +1 ≢ 0
-- 2^x≢0 zero = λ ()
-- 2^x≢0 (suc x) = x≢0⇒x+y≢0 _ (2^x≢0 x)

x≢0∧y≢0⇒x*y≢0 : ∀ x y → x ≢ 0 → y ≢ 0 → x ℕ.* y ≢ 0
x≢0∧y≢0⇒x*y≢0 zero y x≢0 y≢0 = λ _ → x≢0 refl
x≢0∧y≢0⇒x*y≢0 (suc x) zero x≢0 y≢0 = λ _ → y≢0 refl
x≢0∧y≢0⇒x*y≢0 (suc x) (suc y) x≢0 y≢0 = λ ()

-- ⟦x⇓⟧₁⁺¹≢0 : ∀ x → ⟦ x ⇓⟧₁⁺¹ ≢ 0
-- ⟦x⇓⟧₁⁺¹≢0 (x 1& xs) = x≢0∧y≢0⇒x*y≢0 (2^ x +1) (suc ⟦ xs ⇓⟧≤) (2^x≢0 x) λ ()

pred-distrib-both : ∀ {x y} → x ≢ 0 → y ≢ 0 → ℕ.pred (x ℕ.+ y) ≡ suc (ℕ.pred x ℕ.+ ℕ.pred y)
pred-distrib-both {zero} x≢0 y≢0 = ⊥-elim (x≢0 refl)
pred-distrib-both {suc x} {zero} x≢0 y≢0 = ⊥-elim (y≢0 refl)
pred-distrib-both {suc x} {suc y} x≢0 y≢0 = ℕ-Prop.+-suc _ _

suc-double : ∀ x → 2* suc x ≡ suc (suc (2* x))
suc-double x = cong suc (ℕ-Prop.+-suc _ _)

double-distrib-+ : ∀ x y → 2* (x ℕ.+ y) ≡ (2* x) ℕ.+ (2* y)
double-distrib-+ x y =
  begin
    2* (x ℕ.+ y)
  ≡⟨⟩
    (x ℕ.+ y) ℕ.+ (x ℕ.+ y)
  ≡⟨ ℕ-Prop.+-assoc x y _ ⟩
    x ℕ.+ (y ℕ.+ (x ℕ.+ y))
  ≡⟨ x +≫ ℕ-Prop.+-comm y (x ℕ.+ y) ⟩
    x ℕ.+ ((x ℕ.+ y) ℕ.+ y)
  ≡⟨ x +≫ ℕ-Prop.+-assoc x y y ⟩
    x ℕ.+ (x ℕ.+ (y ℕ.+ y))
  ≡˘⟨ ℕ-Prop.+-assoc x x _ ⟩
    (x ℕ.+ x) ℕ.+ (y ℕ.+ y)
  ≡⟨⟩
    (2* x) ℕ.+ (2* y)
  ∎

odd-double-distrib-+ : ∀ x y → 2* (suc (x ℕ.+ y)) ≡ suc (2* x) ℕ.+ suc (2* y)
odd-double-distrib-+ x y =
  begin
    2* (suc (x ℕ.+ y))
  ≡⟨⟩
    2* ((suc x) ℕ.+ y)
  ≡⟨ double-distrib-+ (suc x) y ⟩
    (2* (suc x)) ℕ.+ (2* y)
  ≡⟨⟩
    (suc x ℕ.+ suc x) ℕ.+ (2* y)
  ≡⟨ (2* y) ≪+ ℕ-Prop.+-suc (suc x) x ⟩
    (suc (suc x) ℕ.+ x) ℕ.+ (2* y)
  ≡⟨⟩
    suc (suc (x ℕ.+ x)) ℕ.+ (2* y)
  ≡⟨⟩
    suc (suc (2* x)) ℕ.+ (2* y)
  ≡˘⟨ ℕ-Prop.+-suc (suc (2* x)) (2* y) ⟩
    suc (2* x) ℕ.+ suc (2* y)
  ∎

double-distrib-+-lsuc : ∀ x y → 2* suc (x ℕ.+ y) ≡ suc (suc (2* x) ℕ.+ (2* y))
double-distrib-+-lsuc x y =
  begin
    2* suc (x ℕ.+ y)
  ≡⟨⟩
    suc (x ℕ.+ y) ℕ.+ suc (x ℕ.+ y)
  ≡⟨⟩
    (suc x ℕ.+ y) ℕ.+ (suc x ℕ.+ y)
  ≡⟨⟩
    2* (suc x ℕ.+ y)
  ≡⟨ double-distrib-+ (suc x) y ⟩
    (2* (suc x)) ℕ.+ (2* y)
  ≡⟨⟩
    ((suc x) ℕ.+ (suc x)) ℕ.+ (2* y)
  ≡⟨ (2* y) ≪+ ℕ-Prop.+-suc (suc x) x ⟩
    suc (suc (x ℕ.+ x)) ℕ.+ (2* y)
  ≡⟨⟩
    suc (suc (2* x) ℕ.+ (2* y))
  ∎
