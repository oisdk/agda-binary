{-# OPTIONS --without-K --safe #-}

module Data.Binary.Views where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Definitions
open import Data.Binary.Operations.Unary
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.Proofs.Unary
open import Function
open import Data.Empty

import Data.Nat.Properties as ℕ-Prop

-- A "suc"-like view onto a binary number
data Suc-View : 𝔹 → Set where
  zeroᵇ : Suc-View 0₂
  sucᵇ : ∀ x → Suc-View (inc x)

suc-view : ∀ x → Suc-View x
suc-view 0₂ = zeroᵇ
suc-view (0< xs) = subst Suc-View (cong 0<_ (inc-dec xs)) (sucᵇ (dec⁺ xs))

⟦x⇓⟧⁺≢0 : ∀ x → ⟦ x ⇓⟧⁺ ≢ 0
⟦x⇓⟧⁺≢0 x p with suc-view (0< x)
⟦x⇓⟧⁺≢0 .(inc⁺ x) p | sucᵇ x with sym (inc-homo x) ⟨ trans ⟩ p
⟦x⇓⟧⁺≢0 .(inc⁺ x) p | sucᵇ x | ()

-- Similar to the suc-like view as before, but also works as well-founded recursion
data Suc-Rec : 𝔹 → Set where
  zeroʳ : Suc-Rec 0₂
  sucʳ : ∀ x → Suc-Rec x → Suc-Rec (inc x)

suc-rec : ∀ x → Suc-Rec x
suc-rec x = go _ x (inspect ⟦_⇓⟧ x)
  where
  go : ∀ n x → Reveal ⟦_⇓⟧ · x is n → Suc-Rec x
  go n 0₂ p = zeroʳ
  go zero (0< x) [ p ] = ⊥-elim (⟦x⇓⟧⁺≢0 x p)
  go (suc n) (0< xs) [ p ] = subst Suc-Rec (cong 0<_ (inc-dec xs)) (sucʳ (dec⁺ xs) (go n (dec⁺ xs) [ ℕ-Prop.suc-injective (sym (inc-homo (dec⁺ xs)) ⟨ trans ⟩ cong ⟦_⇓⟧⁺ (inc-dec xs)  ⟨ trans ⟩ p) ]))
