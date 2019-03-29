{-# OPTIONS --without-K --safe #-}

module Data.Binary.Relations where

open import Data.Binary.Relations.Raw
open import Data.Binary.Definitions
open import Data.Binary.Operations.Addition
open import Relation.Binary
open import Relation.Nullary
import Data.Empty.Irrelevant as Irrel

infix 4 _≤_ _<_
record _≤_ (x y : 𝔹) : Set where
  constructor ≤!
  field
    .proof : ⟅ I ⟆ x ≺ y

record _<_ (x y : 𝔹) : Set where
  constructor <!
  field
    .proof : ⟅ O ⟆ x ≺ y

_≤?_ : Decidable _≤_
x ≤? y with I ! x ≺? y
(x ≤? y) | yes x₁ = yes (≤! x₁)
(x ≤? y) | no x₁ = no λ p → Irrel.⊥-elim (x₁ (_≤_.proof p))

_<?_ : Decidable _<_
x <? y with O ! x ≺? y
(x <? y) | yes x₁ = yes (<! x₁)
(x <? y) | no x₁ = no λ p → Irrel.⊥-elim (x₁ (_<_.proof p))

<⇒≤ : ∀ {x y} → x < y → x ≤ y
<⇒≤ {x} {y} x<y = ≤! (weaken x y (_<_.proof x<y))

≤-trans : Transitive _≤_
≤-trans {i} {j} {k} i≤j j≤k = ≤! (≺-trans I I i j k (_≤_.proof i≤j) (_≤_.proof j≤k))

<-trans : Transitive _<_
<-trans {i} {j} {k} i<j j<k = <! (≺-trans O O i j k (_<_.proof i<j) (_<_.proof j<k))

n≤m+n : ∀ x y → x ≤ y + x
n≤m+n x y = ≤! (≺-add y x)
