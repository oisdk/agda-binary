{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Proofs.Semantics where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.NonZero.Operations.Unary
open import Data.Binary.NonZero.Proofs.Unary
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function

homo : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
homo zero = refl
homo (suc n) = inc-homo ⟦ n ⇑⟧ ⟨ trans ⟩ cong suc (homo n)


inj : ∀ {x y} → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
inj {xs} {ys} eq = go (subst (NatView xs) eq (nat-view xs)) (nat-view ys)
  where
  go : ∀ {n xs ys} → NatView xs n → NatView ys n → xs ≡ ys
  go ℕzero ℕzero = refl
  go (ℕsuc xs) (ℕsuc ys) = cong inc (go xs ys)

open import Function.Bijection

𝔹↔ℕ : 𝔹 ⤖ ℕ
𝔹↔ℕ = bijection ⟦_⇓⟧ ⟦_⇑⟧ inj homo
