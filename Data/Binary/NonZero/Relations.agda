{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Relations where

open import Data.Binary.NonZero.Definitions
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

infix 4 _<⁺_ _<_ _≤⁺_ _≤_
mutual
  data _<⁺_ : 𝔹⁺ → 𝔹⁺ → Set where
    1⁺<1∷ : ∀ {ys} → 1⁺ <⁺ (1⁺∷ ys)
    1⁺<0∷ : ∀ {ys} → 1⁺ <⁺ (0⁺∷ ys)
    0∷<0∷ : ∀ {xs ys} → xs <⁺ ys → (0⁺∷ xs) <⁺ (0⁺∷ ys)
    0∷<1∷ : ∀ {xs ys} → xs ≤⁺ ys → (0⁺∷ xs) <⁺ (1⁺∷ ys)
    1∷<0∷ : ∀ {xs ys} → xs <⁺ ys → (1⁺∷ xs) <⁺ (0⁺∷ ys)
    1∷<1∷ : ∀ {xs ys} → xs <⁺ ys → (1⁺∷ xs) <⁺ (1⁺∷ ys)

  data _<_ : 𝔹 → 𝔹 → Set where
    0<⁺ : ∀ {ys} → 0ᵇ < (0< ys)
    ⁺<⁺ : ∀ {xs ys} → xs <⁺ ys → (0< xs) < (0< ys)

  data _≤⁺_ : 𝔹⁺ → 𝔹⁺ → Set where
    1⁺≤n : ∀ {ys} → 1⁺ ≤⁺ ys
    0∷≤0∷ : ∀ {xs ys} → xs ≤⁺ ys → (0⁺∷ xs) ≤⁺ (0⁺∷ ys)
    0∷≤1∷ : ∀ {xs ys} → xs ≤⁺ ys → (0⁺∷ xs) ≤⁺ (1⁺∷ ys)
    1∷≤0∷ : ∀ {xs ys} → xs <⁺ ys → (1⁺∷ xs) ≤⁺ (0⁺∷ ys)
    1∷≤1∷ : ∀ {xs ys} → xs ≤⁺ ys → (1⁺∷ xs) ≤⁺ (1⁺∷ ys)

  data _≤_ : 𝔹 → 𝔹 → Set where
    0≤n : ∀ {ys} → 0ᵇ ≤ ys
    ⁺≤⁺ : ∀ {xs ys} → xs ≤⁺ ys → (0< xs) ≤ (0< ys)

mutual
  _≤?_ : Decidable _≤_
  0ᵇ ≤? ys = yes 0≤n
  (0< xs) ≤? 0ᵇ = no λ ()
  (0< xs) ≤? (0< ys) = map′ ⁺≤⁺ (λ { (⁺≤⁺ x) → x}) (xs ≤⁺? ys)

  _<?_ : Decidable _<_
  xs <? 0ᵇ = no λ ()
  0ᵇ <? (0< ys) = yes 0<⁺
  (0< xs) <? (0< ys) = map′ ⁺<⁺ (λ { (⁺<⁺ x) → x}) (xs <⁺? ys)

  _≤⁺?_ : Decidable _≤⁺_
  1⁺ ≤⁺? ys = yes 1⁺≤n
  (0⁺∷ xs) ≤⁺? 1⁺ = no λ ()
  (0⁺∷ xs) ≤⁺? (0⁺∷ ys) = map′ 0∷≤0∷ (λ { (0∷≤0∷ zs) → zs}) (xs ≤⁺? ys)
  (0⁺∷ xs) ≤⁺? (1⁺∷ ys) = map′ 0∷≤1∷ (λ { (0∷≤1∷ zs) → zs}) (xs ≤⁺? ys)
  (1⁺∷ xs) ≤⁺? 1⁺ = no λ ()
  (1⁺∷ xs) ≤⁺? (0⁺∷ ys) = map′ 1∷≤0∷ (λ { (1∷≤0∷ zs) → zs}) (xs <⁺? ys)
  (1⁺∷ xs) ≤⁺? (1⁺∷ ys) = map′ 1∷≤1∷ (λ { (1∷≤1∷ zs) → zs}) (xs ≤⁺? ys)

  _<⁺?_ : Decidable _<⁺_
  xs <⁺? 1⁺ = no λ ()
  1⁺ <⁺? (0⁺∷ ys) = yes 1⁺<0∷
  (0⁺∷ xs) <⁺? (0⁺∷ ys) = map′ 0∷<0∷ (λ { (0∷<0∷ zs) → zs }) (xs <⁺? ys)
  (1⁺∷ xs) <⁺? (0⁺∷ ys) = map′ 1∷<0∷ (λ { (1∷<0∷ zs) → zs }) (xs <⁺? ys)
  1⁺ <⁺? (1⁺∷ ys) = yes 1⁺<1∷
  (0⁺∷ xs) <⁺? (1⁺∷ ys) = map′ 0∷<1∷ (λ { (0∷<1∷ zs) → zs }) (xs ≤⁺? ys)
  (1⁺∷ xs) <⁺? (1⁺∷ ys) = map′ 1∷<1∷ (λ { (1∷<1∷ zs) → zs }) (xs <⁺? ys)

mutual
  ≤-irrel : Irrelevant _≤_
  ≤-irrel 0≤n 0≤n = refl
  ≤-irrel (⁺≤⁺ xs) (⁺≤⁺ ys) = cong ⁺≤⁺ (≤⁺-irrel xs ys)

  ≤⁺-irrel : Irrelevant _≤⁺_
  ≤⁺-irrel 1⁺≤n 1⁺≤n = refl
  ≤⁺-irrel (0∷≤0∷ xs) (0∷≤0∷ ys) = cong 0∷≤0∷ (≤⁺-irrel xs ys)
  ≤⁺-irrel (0∷≤1∷ xs) (0∷≤1∷ ys) = cong 0∷≤1∷ (≤⁺-irrel xs ys)
  ≤⁺-irrel (1∷≤0∷ xs) (1∷≤0∷ ys) = cong 1∷≤0∷ (<⁺-irrel xs ys)
  ≤⁺-irrel (1∷≤1∷ xs) (1∷≤1∷ ys) = cong 1∷≤1∷ (≤⁺-irrel xs ys)

  <-irrel : Irrelevant _<_
  <-irrel 0<⁺ 0<⁺ = refl
  <-irrel (⁺<⁺ xs) (⁺<⁺ ys) = cong ⁺<⁺ (<⁺-irrel xs ys)

  <⁺-irrel : Irrelevant _<⁺_
  <⁺-irrel 1⁺<1∷ 1⁺<1∷ = refl
  <⁺-irrel 1⁺<0∷ 1⁺<0∷ = refl
  <⁺-irrel (0∷<0∷ xs) (0∷<0∷ ys) = cong 0∷<0∷ (<⁺-irrel xs ys)
  <⁺-irrel (0∷<1∷ xs) (0∷<1∷ ys) = cong 0∷<1∷ (≤⁺-irrel xs ys)
  <⁺-irrel (1∷<0∷ xs) (1∷<0∷ ys) = cong 1∷<0∷ (<⁺-irrel xs ys)
  <⁺-irrel (1∷<1∷ xs) (1∷<1∷ ys) = cong 1∷<1∷ (<⁺-irrel xs ys)
