{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Relations where

open import Data.Binary.NonZero.Definitions
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (not; _∧_; _∨_; T)
open import Data.Bool.Properties using (T?)

infix 4 ⟅_⟆_≺ᵇ_ ⟅_⟆_≺⁺_ ⟅_⟆_≺_ _!_≺⁺?_ _!_≺?_

⟅_⟆_≺ᵇ_ : Bit → Bit → Bit → Bit
⟅ p ⟆ I ≺ᵇ q = q ∧ p
⟅ p ⟆ O ≺ᵇ q = p ∨ q

⟅_⟆_≺⁺_ : Bit → 𝔹⁺ → 𝔹⁺ → Set
⟅ p ⟆ 1ᵇ       ≺⁺ (y ∷ ys) = ⊤
⟅ p ⟆ 1ᵇ       ≺⁺ 1ᵇ = T p
⟅ p ⟆ (x ∷ xs) ≺⁺ 1ᵇ = ⊥
⟅ p ⟆ (x ∷ xs) ≺⁺ (y ∷ ys) = ⟅ ⟅ p ⟆ x ≺ᵇ y ⟆ xs ≺⁺ ys

⟅_⟆_≺_ : Bit → 𝔹 → 𝔹 → Set
⟅ p ⟆ 0ᵇ ≺ 0ᵇ = T p
⟅ p ⟆ 0ᵇ ≺ (0< x) = ⊤
⟅ p ⟆ 0< xs ≺ 0ᵇ = ⊥
⟅ p ⟆ 0< xs ≺ (0< ys) = ⟅ p ⟆ xs ≺⁺ ys

weaken : ∀ x xs ys → ⟅ x ⟆ xs ≺⁺ ys → ⟅ I ⟆ xs ≺⁺ ys
weaken x (O ∷ xs) 1ᵇ xs<ys = xs<ys
weaken x (O ∷ xs) (y ∷ ys) xs<ys = weaken (x ∨ y) xs ys xs<ys
weaken x (I ∷ xs) 1ᵇ xs<ys = xs<ys
weaken x (I ∷ xs) (O ∷ ys) xs<ys = xs<ys
weaken x (I ∷ xs) (I ∷ ys) xs<ys = weaken x xs ys xs<ys
weaken O 1ᵇ 1ᵇ xs<ys = tt
weaken O 1ᵇ (x ∷ xs) xs<ys = tt
weaken I 1ᵇ ys xs<ys = xs<ys

≺⁺-trans : ∀ x y xs ys zs → ⟅ x ⟆ xs ≺⁺ ys → ⟅ y ⟆ ys ≺⁺ zs → ⟅ x ∧ y ⟆ xs ≺⁺ zs
≺⁺-trans c₁ c₂ 1ᵇ ys (x ∷ zs) xs<ys ys<zs = tt
≺⁺-trans c₁ c₂ (x ∷ xs) 1ᵇ 1ᵇ xs<ys ys<zs = xs<ys
≺⁺-trans c₁ c₂ (x ∷ xs) 1ᵇ (z ∷ zs) () ys<zs
≺⁺-trans c₁ c₂ (x ∷ xs) (y ∷ ys) 1ᵇ xs<ys ys<zs = ys<zs
≺⁺-trans O O 1ᵇ 1ᵇ 1ᵇ xs<ys ys<zs = ys<zs
≺⁺-trans O O 1ᵇ (x ∷ xs) 1ᵇ xs<ys ys<zs = ys<zs
≺⁺-trans O I 1ᵇ 1ᵇ 1ᵇ xs<ys ys<zs = xs<ys
≺⁺-trans O I 1ᵇ (x ∷ xs) 1ᵇ xs<ys ys<zs = ys<zs
≺⁺-trans I O 1ᵇ 1ᵇ 1ᵇ xs<ys ys<zs = ys<zs
≺⁺-trans I O 1ᵇ (x ∷ xs) 1ᵇ xs<ys ys<zs = ys<zs
≺⁺-trans I I 1ᵇ ys 1ᵇ xs<ys ys<zs = tt
≺⁺-trans I c₂ (I ∷ xs) (O ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans O (c₂ ∨ O) xs ys zs xs<ys ys<zs
≺⁺-trans I c₂ (I ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans O c₂ (I ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans O (c₂ ∨ I) xs ys zs xs<ys ys<zs
≺⁺-trans O c₂ (I ∷ xs) (I ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans O c₂ xs ys zs xs<ys ys<zs
≺⁺-trans O c₂ (I ∷ xs) (O ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans O (c₂ ∨ O) xs ys zs xs<ys ys<zs
≺⁺-trans O c₂ (I ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans O O xs ys zs xs<ys ys<zs
≺⁺-trans O c₂ (O ∷ xs) (y ∷ ys) (I ∷ zs) xs<ys ys<zs = weaken (y ∧ (⟅ c₂ ⟆ y ≺ᵇ I)) xs zs (≺⁺-trans y (⟅ c₂ ⟆ y ≺ᵇ I) xs ys zs xs<ys ys<zs)
≺⁺-trans O c₂ (O ∷ xs) (O ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans O (c₂ ∨ O) xs ys zs xs<ys ys<zs
≺⁺-trans O c₂ (O ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans I O (I ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans O I xs ys zs xs<ys ys<zs
≺⁺-trans I O (I ∷ xs) (I ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans I O (O ∷ xs) (y ∷ ys) (I ∷ zs) xs<ys ys<zs = weaken (⟅ O ⟆ y ≺ᵇ I) xs zs (≺⁺-trans I (⟅ O ⟆ y ≺ᵇ I) xs ys zs xs<ys ys<zs)
≺⁺-trans I O (O ∷ xs) (O ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans I O (O ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans I I (I ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = weaken O xs zs (≺⁺-trans (O ∧ I) (⟅ I ⟆ O ≺ᵇ I) xs ys zs xs<ys ys<zs)
≺⁺-trans I I (I ∷ xs) (I ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans (I ∧ I) (⟅ I ⟆ I ≺ᵇ I) xs ys zs xs<ys ys<zs
≺⁺-trans I I (O ∷ xs) (y ∷ ys) (z ∷ zs) xs<ys ys<zs = weaken (⟅ I ⟆ y ≺ᵇ z) xs zs (≺⁺-trans I (⟅ I ⟆ y ≺ᵇ z) xs ys zs xs<ys ys<zs)

_!_≺⁺?_ : ∀ x xs ys → Dec (⟅ x ⟆ xs ≺⁺ ys)
c ! 1ᵇ ≺⁺? x ∷ xs = yes tt
c ! 1ᵇ ≺⁺? 1ᵇ = T? c
c ! x ∷ xs ≺⁺? 1ᵇ = no (λ z → z)
c ! x ∷ xs ≺⁺? y ∷ ys = (⟅ c ⟆ x ≺ᵇ y) ! xs ≺⁺? ys

_!_≺?_ : ∀ x xs ys → Dec (⟅ x ⟆ xs ≺ ys)
c ! 0< xs ≺? 0< ys = c ! xs ≺⁺? ys
c ! 0< xs ≺? 0ᵇ = no (λ z → z)
c ! 0ᵇ ≺? 0< _ = yes tt
c ! 0ᵇ ≺? 0ᵇ = T? c

open import Data.Binary.NonZero.Operations.Addition
open import Data.Binary.NonZero.Operations.Unary

≼-refl : ∀ xs → ⟅ I ⟆ xs ≺⁺ xs
≼-refl 1ᵇ = tt
≼-refl (O ∷ xs) = ≼-refl xs
≼-refl (I ∷ xs) = ≼-refl xs

≺⁺-inc⁺⁺ : ∀ x xs → ⟅ x ⟆ xs ≺⁺ inc⁺⁺ xs
≺⁺-inc⁺⁺ _ 1ᵇ = tt
≺⁺-inc⁺⁺ c (I ∷ xs) = ≺⁺-inc⁺⁺ O xs
≺⁺-inc⁺⁺ O (O ∷ xs) = ≼-refl xs
≺⁺-inc⁺⁺ I (O ∷ xs) = ≼-refl xs

≺⁺-add : ∀ ys xs c₁ c₂  → ⟅ c₁ ⟆ xs ≺⁺ add c₂ ys xs
≺⁺-add 1ᵇ 1ᵇ c₁ O = tt
≺⁺-add 1ᵇ 1ᵇ c₁ I = tt
≺⁺-add 1ᵇ (x ∷ xs) c₁ O = ≺⁺-inc⁺⁺ c₁ (x ∷ xs)
≺⁺-add 1ᵇ (x ∷ xs) c₁ I = ≺⁺-inc⁺⁺ (⟅ c₁ ⟆ x ≺ᵇ x) xs
≺⁺-add (y ∷ ys) (x ∷ xs) c₁ c₂ = ≺⁺-add ys xs (⟅ c₁ ⟆ x ≺ᵇ sumᵇ c₂ y x) (carryᵇ c₂ y x)
≺⁺-add (y ∷ ys) 1ᵇ c₁ I = tt
≺⁺-add (O ∷ ys) 1ᵇ c₁ O = tt
≺⁺-add (I ∷ ys) 1ᵇ c₁ O = tt

infix 4 _≤_ _<_
record _≤_ (x y : 𝔹) : Set where
  constructor ≤!
  field
    .proof : ⟅ I ⟆ x ≺ y

record _<_ (x y : 𝔹) : Set where
  field
    .proof : ⟅ O ⟆ x ≺ y
