{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Relations where

open import Data.Binary.NonZero.Definitions
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (not; _∧_; _∨_; T)
open import Data.Bool.Properties using (T?)
open import Data.Sum as Sum using (inj₁; inj₂; _⊎_)

infix 4 ⟅_⟆_≺ᵇ_ ⟅_⟆_≺⁺_ ⟅_⟆_≺_ _!_≺⁺?_ _!_≺?_ _≺_ _≼_ _≺⁺_ _≼⁺_

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

_≺_ = ⟅ O ⟆_≺_
_≼_ = ⟅ I ⟆_≺_
_≺⁺_ = ⟅ O ⟆_≺⁺_
_≼⁺_ = ⟅ I ⟆_≺⁺_

weaken : ∀ x xs ys → ⟅ x ⟆ xs ≺⁺ ys → xs ≼⁺ ys
weaken x (O ∷ xs) 1ᵇ xs<ys = xs<ys
weaken x (O ∷ xs) (y ∷ ys) xs<ys = weaken (x ∨ y) xs ys xs<ys
weaken x (I ∷ xs) 1ᵇ xs<ys = xs<ys
weaken x (I ∷ xs) (O ∷ ys) xs<ys = xs<ys
weaken x (I ∷ xs) (I ∷ ys) xs<ys = weaken x xs ys xs<ys
weaken O 1ᵇ 1ᵇ xs<ys = tt
weaken O 1ᵇ (x ∷ xs) xs<ys = tt
weaken I 1ᵇ ys xs<ys = xs<ys

weaken′ : ∀ xs ys → ⟅ O ⟆ xs ≺ ys → xs ≼ ys
weaken′ (0< xs) (0< ys) xs<ys = weaken O xs ys xs<ys
weaken′ (0< x) 0ᵇ xs<ys = xs<ys
weaken′ 0ᵇ (0< x) xs<ys = tt
weaken′ 0ᵇ 0ᵇ xs<ys = tt

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

≺-trans : ∀ x y xs ys zs → ⟅ x ⟆ xs ≺ ys → ⟅ y ⟆ ys ≺ zs → ⟅ x ∧ y ⟆ xs ≺ zs
≺-trans x y (0< x₁) (0< x₃) (0< x₂) xs<ys ys<zs = ≺⁺-trans x y x₁ x₃ x₂ xs<ys ys<zs
≺-trans x y (0< x₁) 0ᵇ (0< x₂) () ys<zs
≺-trans x y (0< x₁) (0< x₂) 0ᵇ xs<ys ys<zs = ys<zs
≺-trans x y (0< x₁) 0ᵇ 0ᵇ xs<ys ys<zs = xs<ys
≺-trans x y 0ᵇ ys (0< x₁) xs<ys ys<zs = tt
≺-trans x y 0ᵇ (0< x₁) 0ᵇ tt ()
≺-trans O O 0ᵇ 0ᵇ 0ᵇ xs<ys ys<zs = ys<zs
≺-trans O I 0ᵇ 0ᵇ 0ᵇ xs<ys ys<zs = xs<ys
≺-trans I O 0ᵇ 0ᵇ 0ᵇ xs<ys ys<zs = ys<zs
≺-trans I I 0ᵇ 0ᵇ 0ᵇ xs<ys ys<zs = tt

_!_≺⁺?_ : ∀ x xs ys → Dec (⟅ x ⟆ xs ≺⁺ ys)
c ! 1ᵇ ≺⁺? x ∷ xs = yes tt
c ! 1ᵇ ≺⁺? 1ᵇ = T? c
c ! x ∷ xs ≺⁺? 1ᵇ = no (λ z → z)
c ! x ∷ xs ≺⁺? y ∷ ys = (⟅ c ⟆ x ≺ᵇ y) ! xs ≺⁺? ys

asym-≺⁺ : ∀ c xs ys → ⟅ c ⟆ ys ≺⁺ xs → ¬ ⟅ not c ⟆ xs ≺⁺ ys
asym-≺⁺ O 1ᵇ 1ᵇ ys<xs xs<ys = ys<xs
asym-≺⁺ O 1ᵇ (x ∷ xs) ys<xs xs<ys = ys<xs
asym-≺⁺ O (O ∷ xs) 1ᵇ ys<xs xs<ys = xs<ys
asym-≺⁺ O (O ∷ xs) (O ∷ ys) ys<xs xs<ys = asym-≺⁺ I ys xs xs<ys ys<xs
asym-≺⁺ O (O ∷ xs) (I ∷ ys) ys<xs xs<ys = asym-≺⁺ I ys xs xs<ys ys<xs
asym-≺⁺ O (I ∷ xs) 1ᵇ ys<xs xs<ys = xs<ys
asym-≺⁺ O (I ∷ xs) (O ∷ ys) ys<xs xs<ys = asym-≺⁺ O ys xs xs<ys ys<xs
asym-≺⁺ O (I ∷ xs) (I ∷ ys) ys<xs xs<ys = asym-≺⁺ I ys xs xs<ys ys<xs
asym-≺⁺ I 1ᵇ 1ᵇ ys<xs xs<ys = xs<ys
asym-≺⁺ I 1ᵇ (x ∷ xs) ys<xs xs<ys = ys<xs
asym-≺⁺ I (O ∷ xs) 1ᵇ ys<xs xs<ys = xs<ys
asym-≺⁺ I (O ∷ xs) (O ∷ ys) ys<xs xs<ys = asym-≺⁺ O ys xs xs<ys ys<xs
asym-≺⁺ I (O ∷ xs) (I ∷ ys) ys<xs xs<ys = asym-≺⁺ I ys xs xs<ys ys<xs
asym-≺⁺ I (I ∷ xs) 1ᵇ ys<xs xs<ys = xs<ys
asym-≺⁺ I (I ∷ xs) (O ∷ ys) ys<xs xs<ys = asym-≺⁺ O ys xs xs<ys ys<xs
asym-≺⁺ I (I ∷ xs) (I ∷ ys) ys<xs xs<ys = asym-≺⁺ O ys xs xs<ys ys<xs

asym-≺ : ∀ c xs ys → ⟅ c ⟆ ys ≺ xs → ¬ ⟅ not c ⟆ xs ≺ ys
asym-≺ c (0< xs) (0< ys) ys<xs xs<ys = asym-≺⁺ c xs ys ys<xs xs<ys
asym-≺ c (0< x) 0ᵇ ys<xs xs<ys = xs<ys
asym-≺ c 0ᵇ (0< x) ys<xs xs<ys = ys<xs
asym-≺ c 0ᵇ 0ᵇ ys<xs xs<ys = asym-≺⁺ c 1ᵇ 1ᵇ ys<xs xs<ys

pos-asym-≺⁺ : ∀ c xs ys → ¬ ⟅ c ⟆ ys ≺⁺ xs → ⟅ not c ⟆ xs ≺⁺ ys
pos-asym-≺⁺ c 1ᵇ (x ∷ ys) ys≺xs = tt
pos-asym-≺⁺ c (x ∷ xs) 1ᵇ ys≺xs = ys≺xs tt
pos-asym-≺⁺ c (I ∷ xs) (I ∷ ys) ys≺xs = pos-asym-≺⁺ c xs ys ys≺xs
pos-asym-≺⁺ O (O ∷ xs) (O ∷ ys) ys≺xs = pos-asym-≺⁺ O xs ys ys≺xs
pos-asym-≺⁺ I (O ∷ xs) (O ∷ ys) ys≺xs = pos-asym-≺⁺ I xs ys ys≺xs
pos-asym-≺⁺ O (O ∷ xs) (I ∷ ys) ys≺xs = pos-asym-≺⁺ O xs ys ys≺xs
pos-asym-≺⁺ I (O ∷ xs) (I ∷ ys) ys≺xs = pos-asym-≺⁺ O xs ys ys≺xs
pos-asym-≺⁺ O (I ∷ xs) (O ∷ ys) ys≺xs = pos-asym-≺⁺ I xs ys ys≺xs
pos-asym-≺⁺ I (I ∷ xs) (O ∷ ys) ys≺xs = pos-asym-≺⁺ I xs ys ys≺xs
pos-asym-≺⁺ O 1ᵇ 1ᵇ ys≺xs = tt
pos-asym-≺⁺ I 1ᵇ 1ᵇ ys≺xs = ys≺xs tt

pos-asym-≺ : ∀ c xs ys → ¬ ⟅ c ⟆ ys ≺ xs → ⟅ not c ⟆ xs ≺ ys
pos-asym-≺ c (0< xs) (0< ys) ys≮xs = pos-asym-≺⁺ c xs ys ys≮xs
pos-asym-≺ c (0< x) 0ᵇ ys≮xs = ys≮xs tt
pos-asym-≺ c 0ᵇ (0< x) ys≮xs = tt
pos-asym-≺ O 0ᵇ 0ᵇ ys≮xs = tt
pos-asym-≺ I 0ᵇ 0ᵇ ys≮xs = ys≮xs tt

_!_≺?_ : ∀ x xs ys → Dec (⟅ x ⟆ xs ≺ ys)
c ! 0< xs ≺? 0< ys = c ! xs ≺⁺? ys
c ! 0< xs ≺? 0ᵇ = no (λ z → z)
c ! 0ᵇ ≺? 0< _ = yes tt
c ! 0ᵇ ≺? 0ᵇ = T? c

compare-≺ : ∀ c → Conn ⟅ c ⟆_≺_ ⟅ not c ⟆_≺_
compare-≺ c xs ys with c ! xs ≺? ys
compare-≺ c xs ys | yes p = inj₁ p
compare-≺ c xs ys | no ¬p = inj₂ (pos-asym-≺ c ys xs ¬p)

≺⁺-antisym : ∀ c → Antisymmetric _≡_ ⟅ c ⟆_≺⁺_
≺⁺-antisym c {1ᵇ} {1ᵇ} xs<ys ys<xs = refl
≺⁺-antisym c {1ᵇ} {x ∷ ys} xs<ys ()
≺⁺-antisym c {x ∷ xs} {1ᵇ} () ys<xs
≺⁺-antisym c {O ∷ xs} {O ∷ ys} xs<ys ys<xs = cong (O ∷_) (≺⁺-antisym (c ∨ O) xs<ys ys<xs)
≺⁺-antisym c {O ∷ xs} {I ∷ ys} xs<ys ys<xs = ⊥-elim (asym-≺⁺ O xs ys ys<xs (weaken (c ∨ I) xs ys xs<ys))
≺⁺-antisym c {I ∷ xs} {O ∷ ys} xs<ys ys<xs = ⊥-elim (asym-≺⁺ O ys xs xs<ys (weaken (c ∨ I) ys xs ys<xs))
≺⁺-antisym c {I ∷ xs} {I ∷ ys} xs<ys ys<xs = cong (I ∷_) (≺⁺-antisym c xs<ys ys<xs)

≺-antisym : ∀ c → Antisymmetric _≡_ ⟅ c ⟆_≺_
≺-antisym c {0< x} {0< x₁} xs<ys ys<xs = cong 0<_ (≺⁺-antisym c xs<ys ys<xs)
≺-antisym c {0< x} {0ᵇ} () ys<xs
≺-antisym c {0ᵇ} {0< x} xs<ys ()
≺-antisym c {0ᵇ} {0ᵇ} xs<ys ys<xs = refl

open import Data.Binary.NonZero.Operations.Addition
import Data.Empty.Irrelevant as Irrel
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
<⇒≤ {x} {y} x<y = ≤! (weaken′ x y (_<_.proof x<y))

≤-trans : Transitive _≤_
≤-trans {i} {j} {k} i≤j j≤k = ≤! (≺-trans I I i j k (_≤_.proof i≤j) (_≤_.proof j≤k))

<-trans : Transitive _<_
<-trans {i} {j} {k} i<j j<k = <! (≺-trans O O i j k (_<_.proof i<j) (_<_.proof j<k))
