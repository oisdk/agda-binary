{-# OPTIONS --without-K --safe #-}

module Data.Binary.Proofs.Decidability where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Binary.Definitions
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Nullary

mutual
  infix 4 _≟₀_ _≟₁_ _≟≤_
  _≟₀_ : Decidable (_≡_ {A = 𝔹₀})
  x 0& xs ≟₀ y 0& ys with x ℕ.≟ y
  x 0& xs ≟₀ y 0& ys | no ¬p = no λ { refl → ¬p refl }
  x 0& xs ≟₀ y 0& ys | yes p with xs ≟₁ ys
  x 0& xs ≟₀ y 0& ys | yes p | no ¬p = no λ { refl → ¬p refl }
  x 0& xs ≟₀ y 0& ys | yes p₁ | yes p₂ = yes (cong₂ _0&_ p₁ p₂)

  _≟₁_ : Decidable (_≡_ {A = 𝔹₁})
  x 1& xs ≟₁ y 1& ys with x ℕ.≟ y
  x 1& xs ≟₁ y 1& ys | no ¬p = no λ { refl → ¬p refl }
  x 1& xs ≟₁ y 1& ys | yes p with xs ≟≤ ys
  x 1& xs ≟₁ y 1& ys | yes p | no ¬p = no λ { refl → ¬p refl }
  x 1& xs ≟₁ y 1& ys | yes p₁ | yes p₂ = yes (cong₂ _1&_ p₁ p₂)

  _≟≤_ : Decidable (_≡_ {A = 0≤ 𝔹₀})
  0₂ ≟≤ 0₂ = yes refl
  0₂ ≟≤ 0< _ = no (λ ())
  0< _ ≟≤ 0₂ = no (λ ())
  0< xs ≟≤ 0< ys with xs ≟₀ ys
  ... | yes p = yes (cong 0<_ p)
  ... | no ¬p = no λ { refl → ¬p refl }

infix 4 _≟_
_≟_ : Decidable (_≡_ {A = 𝔹})
0₂ ≟ 0₂ = yes refl
0₂ ≟ (0< x) = no (λ ())
(0< x) ≟ 0₂ = no (λ ())
(0< B₀ xs) ≟ (0< B₀ ys) with xs ≟₀ ys
(0< B₀ xs ≟ 0< B₀ ys) | yes p = yes (cong (λ z → 0< B₀ z) p)
(0< B₀ xs ≟ 0< B₀ ys) | no ¬p = no λ { refl → ¬p refl }
(0< B₀ xs) ≟ (0< B₁ ys) = no (λ ())
(0< B₁ x) ≟ (0< B₀ x₁) = no (λ ())
(0< B₁ xs) ≟ (0< B₁ ys) with xs ≟₁ ys
(0< B₁ x ≟ 0< B₁ x₁) | yes p = yes (cong (λ z → 0< B₁ z) p)
(0< B₁ x ≟ 0< B₁ x₁) | no ¬p = no λ { refl → ¬p refl }
