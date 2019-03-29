{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Semantics where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Operations.Unary
open import Data.Binary.Proofs.Unary
open import Data.Binary.Definitions
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function

homo : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
homo zero = refl
homo (suc n) = inc-homo ⟦ n ⇑⟧ ⟨ trans ⟩ cong suc (homo n)

inj : ∀ {x y} → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
inj {xs} {ys} eq = go (subst (IncView xs) eq (inc-view xs)) (inc-view ys)
  where
  go : ∀ {n xs ys} → IncView xs n → IncView ys n → xs ≡ ys
  go Izero Izero = refl
  go (Isuc refl xs) (Isuc refl ys) = cong inc (go xs ys)

open import Function.Bijection

𝔹↔ℕ : 𝔹 ⤖ ℕ
𝔹↔ℕ = bijection ⟦_⇓⟧ ⟦_⇑⟧ inj homo
