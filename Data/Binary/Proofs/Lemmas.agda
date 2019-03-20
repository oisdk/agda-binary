module Data.Binary.Proofs.Lemmas where

open import Relation.Binary.PropositionalEquality
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Empty
import Data.Nat.Properties as ℕ-Prop
open import Data.Binary.Operations.Semantics
open import Data.Binary.Definitions

x≢0⇒x+y≢0 : ∀ x {y} → x ≢ 0 → x ℕ.+ y ≢ 0
x≢0⇒x+y≢0 zero = λ z _ → z refl
x≢0⇒x+y≢0 (suc x) = λ _ ()

pred-distrib-2* : ∀ {x} → x ≢ 0 → ℕ.pred (2 ℕ.* x) ≡ suc (2 ℕ.* ℕ.pred x)
pred-distrib-2* {zero} p = ⊥-elim (p refl)
pred-distrib-2* {suc x} _ = ℕ-Prop.+-suc _ _

2^x≢0 : ∀ x → 2^ x +1 ≢ 0
2^x≢0 zero = λ ()
2^x≢0 (suc x) = x≢0⇒x+y≢0 _ (2^x≢0 x)

x≢0∧y≢0⇒x*y≢0 : ∀ x y → x ≢ 0 → y ≢ 0 → x ℕ.* y ≢ 0
x≢0∧y≢0⇒x*y≢0 zero y x≢0 y≢0 = λ _ → x≢0 refl
x≢0∧y≢0⇒x*y≢0 (suc x) zero x≢0 y≢0 = λ _ → y≢0 refl
x≢0∧y≢0⇒x*y≢0 (suc x) (suc y) x≢0 y≢0 = λ ()

⟦x⇓⟧₁⁺¹≢0 : ∀ x → ⟦ x ⇓⟧₁⁺¹ ≢ 0
⟦x⇓⟧₁⁺¹≢0 (x 1& xs) = x≢0∧y≢0⇒x*y≢0 (2^ x +1) (suc ⟦ xs ⇓⟧≤) (2^x≢0 x) λ ()

pred-distrib-both : ∀ {x y} → x ≢ 0 → y ≢ 0 → ℕ.pred (x ℕ.+ y) ≡ suc (ℕ.pred x ℕ.+ ℕ.pred y)
pred-distrib-both {zero} x≢0 y≢0 = ⊥-elim (x≢0 refl)
pred-distrib-both {suc x} {zero} x≢0 y≢0 = ⊥-elim (y≢0 refl)
pred-distrib-both {suc x} {suc y} x≢0 y≢0 = ℕ-Prop.+-suc _ _

suc-double : ∀ x → 2 ℕ.* suc x ≡ suc (suc (2 ℕ.* x))
suc-double x = cong suc (ℕ-Prop.+-suc _ _)
