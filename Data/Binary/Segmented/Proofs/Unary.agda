{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Proofs.Unary where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Segmented.Operations.Unary
open import Data.Binary.Segmented.Definitions
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Empty
open import Relation.Binary.PropositionalEquality.FasterReasoning
open import Data.Nat.Properties as ℕ-Prop
open import Data.Binary.Segmented.Operations.Semantics
open import Data.Binary.Segmented.Proofs.Lemmas
open import Function

dec-inc : ∀ x → dec⁺ (inc⁺ x) ≡ x
dec-inc 0₂                         = refl
dec-inc (0< B₁ _ 1& 0₂           ) = refl
dec-inc (0< B₁ _ 1& 0< zero  0& _) = refl
dec-inc (0< B₁ _ 1& 0< suc _ 0& _) = refl
dec-inc (0< B₀ zero  0& _        ) = refl
dec-inc (0< B₀ suc _ 0& _        ) = refl

inc-dec : ∀ x → inc⁺ (dec⁺ x) ≡ x
inc-dec (     B₁ zero  1& 0₂  ) = refl
inc-dec (     B₁ zero  1& 0< _) = refl
inc-dec (     B₁ suc _ 1& _   ) = refl
inc-dec (B₀ _ 0& zero  1& 0₂  ) = refl
inc-dec (B₀ _ 0& zero  1& 0< _) = refl
inc-dec (B₀ _ 0& suc _ 1& _   ) = refl

even-odd-homo : ∀ x {y} → 2^ x * suc y ≡ suc ⟨2^ x * y ⟩−1
even-odd-homo zero = refl
even-odd-homo (suc x) {y} = cong 2*_ (even-odd-homo x) ⟨ trans ⟩ ℕ-Prop.+-suc (suc ⟨2^ x * y ⟩−1) _

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0₂ = refl
inc-homo (0< B₀ zero  0& y 1& xs) = refl
inc-homo (0< B₀ suc x 0& y 1& xs) = refl
inc-homo (0< B₁ x 1& 0₂) = even-odd-homo (suc x)
inc-homo (0< B₁ x 1& 0< zero  0& xs) = even-odd-homo (suc x)
inc-homo (0< B₁ x 1& 0< suc _ 0& xs) = even-odd-homo (suc x)
