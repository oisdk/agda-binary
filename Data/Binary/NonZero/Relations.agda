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

record _≤_ (x y : 𝔹) : Set where
  field
    .proof : ⟅ I ⟆ x ≺ y

record _<_ (x y : 𝔹) : Set where
  field
    .proof : ⟅ O ⟆ x ≺ y

-- record _<_ (x y : 𝔹) : Set where
  

-- plus-≺ : ∀ xs ys → ⟅ I ⟆  xs ≺⁺ add x ys xs
-- plus-≺ ≺ 1ᵇ 1ᵇ = tt
-- plus-≺ ≺ 1ᵇ (O ∷ ys) = tt
-- plus-≺ ≺ 1ᵇ (I ∷ ys) = tt
-- plus-≺ ≺ (O ∷ xs) 1ᵇ = {!!}
-- plus-≺ ≺ (I ∷ xs) 1ᵇ = {!!}
-- plus-≺ ≺ (x ∷ xs) (x ∷ ys) = {!!}
-- plus-≺ I 1ᵇ 1ᵇ = {!!}
-- plus-≺ I 1ᵇ (x ∷ ys) = {!!}
-- plus-≺ I (x ∷ xs) 1ᵇ = {!!}
-- plus-≺ I (x ∷ xs) (x ∷ ys) = {!!}


-- -- -- -- infix 4 _<⁺_ _<_ _≤⁺_ _≤_ _≤ᵇ_

-- -- -- -- _<⁺_ : 𝔹⁺ → 𝔹⁺ → Set
-- -- -- -- _<⁺_ = ⟅ ⊥ ⟆_≺⁺_

-- -- -- -- _≤⁺_ : 𝔹⁺ → 𝔹⁺ → Set
-- -- -- -- _≤⁺_ = ⟅ ⊤ ⟆_≺⁺_

-- -- -- -- _<_ : 


-- -- -- -- data _<_ : 𝔹 → 𝔹 → Set where
-- -- -- --   0<⁺ : ∀ {ys} → 0ᵇ < (0< ys)
-- -- -- --   ⁺<⁺ : ∀ {xs ys} → xs <⁺ ys → (0< xs) < (0< ys)

-- -- -- -- data _≤_ : 𝔹 → 𝔹 → Set where
-- -- -- --   0≤n : ∀ {ys} → 0ᵇ ≤ ys
-- -- -- --   ⁺≤⁺ : ∀ {xs ys} → xs ≤⁺ ys → (0< xs) ≤ (0< ys)

-- -- -- -- _≤ᵇ?_ : Decidable _≤ᵇ_
-- -- -- -- O ≤ᵇ? y = yes 0≤b
-- -- -- -- I ≤ᵇ? O = no λ ()
-- -- -- -- I ≤ᵇ? I = yes I≤I

-- -- -- -- mutual
-- -- -- --   _≤⁺?_ : Decidable _≤⁺_
-- -- -- --   1ᵇ ≤⁺? ys = yes 1ᵇ≤n
-- -- -- --   (x ∷ xs) ≤⁺? 1ᵇ = no λ ()
-- -- -- --   (O ∷ xs) ≤⁺? (y ∷ ys) = map′ (0≤b ∷≤_) (λ { (x ∷≤ xs) → xs}) (xs ≤⁺? ys)
-- -- -- --   (I ∷ xs) ≤⁺? (O ∷ ys) = map′ >∷≤_ (λ { (>∷≤ zs) → zs}) (xs <⁺? ys)
-- -- -- --   (I ∷ xs) ≤⁺? (I ∷ ys) = map′ (I≤I ∷≤_) (λ { (x ∷≤ zs) → zs}) (xs ≤⁺? ys)

-- -- -- --   _<⁺?_ : Decidable _<⁺_
-- -- -- --   xs <⁺? 1ᵇ = no λ ()
-- -- -- --   1ᵇ <⁺? (y ∷ ys) = yes 1ᵇ<∷
-- -- -- --   (x ∷ xs) <⁺? (O ∷ ys) = map′ (0≤b ∷<_) (λ { (x ∷< zs) → zs}) (xs <⁺? ys)
-- -- -- --   (O ∷ xs) <⁺? (I ∷ ys) = map′ <∷<_ (λ { (<∷< zs) → zs}) (xs ≤⁺? ys)
-- -- -- --   (I ∷ xs) <⁺? (I ∷ ys) = map′ (I≤I ∷<_) (λ { (x ∷< zs) → zs}) (xs <⁺? ys)

-- -- -- -- _≤?_ : Decidable _≤_
-- -- -- -- 0ᵇ ≤? ys = yes 0≤n
-- -- -- -- (0< xs) ≤? 0ᵇ = no λ ()
-- -- -- -- (0< xs) ≤? (0< ys) = map′ ⁺≤⁺ (λ { (⁺≤⁺ x) → x}) (xs ≤⁺? ys)

-- -- -- -- _<?_ : Decidable _<_
-- -- -- -- xs <? 0ᵇ = no λ ()
-- -- -- -- 0ᵇ <? (0< ys) = yes 0<⁺
-- -- -- -- (0< xs) <? (0< ys) = map′ ⁺<⁺ (λ { (⁺<⁺ x) → x}) (xs <⁺? ys)

-- -- -- -- ≤ᵇ-irrel : Irrelevant _≤ᵇ_
-- -- -- -- ≤ᵇ-irrel 0≤b 0≤b = refl
-- -- -- -- ≤ᵇ-irrel I≤I I≤I = refl

-- -- -- -- mutual
-- -- -- --   ≤⁺-irrel : Irrelevant _≤⁺_
-- -- -- --   ≤⁺-irrel 1ᵇ≤n 1ᵇ≤n = refl
-- -- -- --   ≤⁺-irrel (>∷≤ xs) (>∷≤ ys) = cong >∷≤_ (<⁺-irrel xs ys)
-- -- -- --   ≤⁺-irrel (x ∷≤ xs) (y ∷≤ ys) = cong₂ _∷≤_ (≤ᵇ-irrel x y) (≤⁺-irrel xs ys)

-- -- -- --   <⁺-irrel : Irrelevant _<⁺_
-- -- -- --   <⁺-irrel 1ᵇ<∷ 1ᵇ<∷ = refl
-- -- -- --   <⁺-irrel (<∷< xs) (<∷< ys) = cong <∷<_ (≤⁺-irrel xs ys)
-- -- -- --   <⁺-irrel (x ∷< xs) (y ∷< ys) = cong₂ _∷<_ (≤ᵇ-irrel x y) (<⁺-irrel xs ys)

-- -- -- -- ≤-irrel : Irrelevant _≤_
-- -- -- -- ≤-irrel 0≤n 0≤n = refl
-- -- -- -- ≤-irrel (⁺≤⁺ xs) (⁺≤⁺ ys) = cong ⁺≤⁺ (≤⁺-irrel xs ys)

-- -- -- -- <-irrel : Irrelevant _<_
-- -- -- -- <-irrel 0<⁺ 0<⁺ = refl
-- -- -- -- <-irrel (⁺<⁺ xs) (⁺<⁺ ys) = cong ⁺<⁺ (<⁺-irrel xs ys)

-- -- -- -- ≤ᵇ-refl : Reflexive _≤ᵇ_
-- -- -- -- ≤ᵇ-refl {O} = 0≤b
-- -- -- -- ≤ᵇ-refl {I} = I≤I

-- -- -- -- ≤⁺-refl : Reflexive _≤⁺_
-- -- -- -- ≤⁺-refl {1ᵇ} = 1ᵇ≤n
-- -- -- -- ≤⁺-refl {x ∷ xs} = ≤ᵇ-refl ∷≤ ≤⁺-refl

-- -- -- -- ≤-refl : Reflexive _≤_
-- -- -- -- ≤-refl {0ᵇ} = 0≤n
-- -- -- -- ≤-refl {0< xs} = ⁺≤⁺ ≤⁺-refl

-- -- -- -- ≤ᵇ-trans : Transitive _≤ᵇ_
-- -- -- -- ≤ᵇ-trans 0≤b j≤k = 0≤b
-- -- -- -- ≤ᵇ-trans I≤I I≤I = I≤I

-- -- -- -- mutual
-- -- -- --   <∙≤⇒≤ : ∀ {x y z} → x <⁺ y → y ≤⁺ z → x ≤⁺ z
-- -- -- --   <∙≤⇒≤ i<j j≤k = {!!}

-- -- -- --   <∙≤⇒< : ∀ {x y z} → x <⁺ y → y ≤⁺ z → x <⁺ z
-- -- -- --   <∙≤⇒< i<j j≤k = {!!}

-- -- -- --   ≤∙<⇒< : ∀ {x y z} → x ≤⁺ y → y <⁺ z → x <⁺ z
-- -- -- --   ≤∙<⇒< i≤j j<k = {!!}

-- -- -- --   ≤∙<⇒≤ : ∀ {x y z} → x ≤⁺ y → y <⁺ z → x ≤⁺ z
-- -- -- --   ≤∙<⇒≤ i≤j j<k = {!!}

-- -- -- --   ≤⁺-trans : Transitive _≤⁺_
-- -- -- --   ≤⁺-trans 1ᵇ≤n j≤k = 1ᵇ≤n
-- -- -- --   ≤⁺-trans (>∷≤ i<j) (_∷≤_ {y = O} x j≤k) = >∷≤ <∙≤⇒< i<j j≤k
-- -- -- --   ≤⁺-trans (>∷≤ i<j) (_∷≤_ {y = I} x j≤k) = I≤I ∷≤ <∙≤⇒≤ i<j j≤k
-- -- -- --   ≤⁺-trans (x ∷≤ i≤j) (y ∷≤ j≤k) = ≤ᵇ-trans x y ∷≤ ≤⁺-trans i≤j j≤k
-- -- -- --   ≤⁺-trans (0≤b ∷≤ i≤j) (>∷≤ j<k) = 0≤b ∷≤ ≤∙<⇒≤ i≤j j<k
-- -- -- --   ≤⁺-trans (I≤I ∷≤ i≤j) (>∷≤ j<k) = >∷≤ ≤∙<⇒< i≤j j<k

-- -- -- --   <⁺-trans : Transitive _<⁺_
-- -- -- --   <⁺-trans 1ᵇ<∷ (<∷< x) = 1ᵇ<∷
-- -- -- --   <⁺-trans 1ᵇ<∷ (x ∷< j<k) = 1ᵇ<∷
-- -- -- --   <⁺-trans (<∷< i≤j) (0≤b ∷< j<k) = 0≤b ∷< ≤∙<⇒< i≤j j<k
-- -- -- --   <⁺-trans (<∷< i≤j) (I≤I ∷< j<k) = <∷< ≤∙<⇒≤ i≤j j<k
-- -- -- --   <⁺-trans (x ∷< i<j) (y ∷< j<k) = ≤ᵇ-trans y x ∷< <⁺-trans i<j j<k
-- -- -- --   <⁺-trans (_∷<_ {O} x i<j) (<∷< j≤k) = <∷< <∙≤⇒≤ i<j j≤k
-- -- -- --   <⁺-trans (_∷<_ {I} x i<j) (<∷< j≤k) = I≤I ∷< <∙≤⇒< i<j j≤k

-- -- -- -- -- -- ≤-trans : Transitive _≤_
-- -- -- -- -- -- ≤-trans 0≤n j≤k = 0≤n
-- -- -- -- -- -- ≤-trans (⁺≤⁺ i≤j) (⁺≤⁺ j≤k) = ⁺≤⁺ (≤⁺-trans i≤j j≤k)

-- -- -- -- -- -- <-trans : Transitive _<_
-- -- -- -- -- -- <-trans 0<⁺ (⁺<⁺ x) = 0<⁺
-- -- -- -- -- -- <-trans (⁺<⁺ xs) (⁺<⁺ ys) = ⁺<⁺ (<⁺-trans xs ys)
