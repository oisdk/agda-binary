{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Relations where

open import Data.Binary.NonZero.Definitions
open import Relation.Nullary
open import Relation.Binary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

So : Bit → Set
So O = ⊥
So I = ⊤

! : Bit → Bit
! O = I
! I = O

_∧_ : Bit → Bit → Bit
O ∧ y = O
I ∧ y = y

_∨_ : Bit → Bit → Bit
I ∨ _ = I
O ∨ x = x


⟅_⟆_≺ᵇ_ : Bit → Bit → Bit → Bit
⟅ p ⟆ I ≺ᵇ q = q ∧ p
⟅ p ⟆ O ≺ᵇ q = q ∨ p

⟅_⟆_≺⁺_ : Bit → 𝔹⁺ → 𝔹⁺ → Set
⟅ p ⟆ 1⁺        ≺⁺ (y ⁺∷ ys) = ⊤
⟅ p ⟆ 1⁺        ≺⁺ 1⁺ = So p
⟅ p ⟆ (x ⁺∷ xs) ≺⁺ 1⁺ = ⊥
⟅ p ⟆ (x ⁺∷ xs) ≺⁺ (y ⁺∷ ys) = ⟅ ⟅ p ⟆ x ≺ᵇ y ⟆ xs ≺⁺ ys

⟅_⟆_≺_ : Bit → 𝔹 → 𝔹 → Set
⟅ p ⟆ 0ᵇ ≺ 0ᵇ = So p
⟅ p ⟆ 0ᵇ ≺ (0< x) = ⊤
⟅ p ⟆ 0< x ≺ 0ᵇ = ⊥
⟅ p ⟆ 0< xs ≺ (0< ys) = ⟅ p ⟆ xs ≺⁺ ys

-- ≺⁺-trans : ∀ x y xs ys zs → ⟅ x ⟆ xs ≺⁺ ys → ⟅ y ⟆ ys ≺⁺ zs → ⟅ x ∧ y ⟆ xs ≺⁺ zs
-- ≺⁺-trans xc yc (0⁺∷ xs) (0⁺∷ ys) (0⁺∷ zs) xs<ys ys<zs = ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (0⁺∷ xs) (0⁺∷ ys) (1⁺∷ zs) xs<ys ys<zs = {!!} -- ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (0⁺∷ xs) (1⁺∷ ys) (0⁺∷ zs) xs<ys ys<zs = {!!} -- ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (0⁺∷ xs) (1⁺∷ ys) (1⁺∷ zs) xs<ys ys<zs = {!!} -- ≺⁺-trans I I  xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (1⁺∷ xs) (0⁺∷ ys) (0⁺∷ zs) xs<ys ys<zs = {!!} -- ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (1⁺∷ xs) (0⁺∷ ys) (1⁺∷ zs) xs<ys ys<zs = {!!} -- ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (1⁺∷ xs) (1⁺∷ ys) (0⁺∷ zs) xs<ys ys<zs = {!!} -- ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc (1⁺∷ xs) (1⁺∷ ys) (1⁺∷ zs) xs<ys ys<zs = ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
-- ≺⁺-trans xc yc 1⁺ (x ⁺∷ ys) (x₁ ⁺∷ zs) xs<ys ys<zs = tt
-- ≺⁺-trans xc I (x ⁺∷ xs) 1⁺ 1⁺ () ys<zs
-- ≺⁺-trans xc I (x ⁺∷ xs) (x₁ ⁺∷ ys) 1⁺ xs<ys ()
-- ≺⁺-trans I yc 1⁺ 1⁺ (x ⁺∷ zs) xs<ys ys<zs = tt
-- ≺⁺-trans xc O (x ⁺∷ xs) 1⁺ 1⁺ xs<ys ()
-- ≺⁺-trans xc O (x ⁺∷ xs) (x₁ ⁺∷ ys) 1⁺ xs<ys ()
-- ≺⁺-trans I I 1⁺ 1⁺ 1⁺ xs<ys ys<zs = tt


-- -- infix 4 _<⁺_ _<_ _≤⁺_ _≤_ _≤ᵇ_

-- -- _<⁺_ : 𝔹⁺ → 𝔹⁺ → Set
-- -- _<⁺_ = ⟅ ⊥ ⟆_≺⁺_

-- -- _≤⁺_ : 𝔹⁺ → 𝔹⁺ → Set
-- -- _≤⁺_ = ⟅ ⊤ ⟆_≺⁺_

-- -- _<_ : 


-- -- data _<_ : 𝔹 → 𝔹 → Set where
-- --   0<⁺ : ∀ {ys} → 0ᵇ < (0< ys)
-- --   ⁺<⁺ : ∀ {xs ys} → xs <⁺ ys → (0< xs) < (0< ys)

-- -- data _≤_ : 𝔹 → 𝔹 → Set where
-- --   0≤n : ∀ {ys} → 0ᵇ ≤ ys
-- --   ⁺≤⁺ : ∀ {xs ys} → xs ≤⁺ ys → (0< xs) ≤ (0< ys)

-- -- _≤ᵇ?_ : Decidable _≤ᵇ_
-- -- O ≤ᵇ? y = yes 0≤b
-- -- I ≤ᵇ? O = no λ ()
-- -- I ≤ᵇ? I = yes I≤I

-- -- mutual
-- --   _≤⁺?_ : Decidable _≤⁺_
-- --   1⁺ ≤⁺? ys = yes 1⁺≤n
-- --   (x ⁺∷ xs) ≤⁺? 1⁺ = no λ ()
-- --   (0⁺∷ xs) ≤⁺? (y ⁺∷ ys) = map′ (0≤b ∷≤_) (λ { (x ∷≤ xs) → xs}) (xs ≤⁺? ys)
-- --   (1⁺∷ xs) ≤⁺? (0⁺∷ ys) = map′ >∷≤_ (λ { (>∷≤ zs) → zs}) (xs <⁺? ys)
-- --   (1⁺∷ xs) ≤⁺? (1⁺∷ ys) = map′ (I≤I ∷≤_) (λ { (x ∷≤ zs) → zs}) (xs ≤⁺? ys)

-- --   _<⁺?_ : Decidable _<⁺_
-- --   xs <⁺? 1⁺ = no λ ()
-- --   1⁺ <⁺? (y ⁺∷ ys) = yes 1⁺<∷
-- --   (x ⁺∷ xs) <⁺? (0⁺∷ ys) = map′ (0≤b ∷<_) (λ { (x ∷< zs) → zs}) (xs <⁺? ys)
-- --   (0⁺∷ xs) <⁺? (1⁺∷ ys) = map′ <∷<_ (λ { (<∷< zs) → zs}) (xs ≤⁺? ys)
-- --   (1⁺∷ xs) <⁺? (1⁺∷ ys) = map′ (I≤I ∷<_) (λ { (x ∷< zs) → zs}) (xs <⁺? ys)

-- -- _≤?_ : Decidable _≤_
-- -- 0ᵇ ≤? ys = yes 0≤n
-- -- (0< xs) ≤? 0ᵇ = no λ ()
-- -- (0< xs) ≤? (0< ys) = map′ ⁺≤⁺ (λ { (⁺≤⁺ x) → x}) (xs ≤⁺? ys)

-- -- _<?_ : Decidable _<_
-- -- xs <? 0ᵇ = no λ ()
-- -- 0ᵇ <? (0< ys) = yes 0<⁺
-- -- (0< xs) <? (0< ys) = map′ ⁺<⁺ (λ { (⁺<⁺ x) → x}) (xs <⁺? ys)

-- -- ≤ᵇ-irrel : Irrelevant _≤ᵇ_
-- -- ≤ᵇ-irrel 0≤b 0≤b = refl
-- -- ≤ᵇ-irrel I≤I I≤I = refl

-- -- mutual
-- --   ≤⁺-irrel : Irrelevant _≤⁺_
-- --   ≤⁺-irrel 1⁺≤n 1⁺≤n = refl
-- --   ≤⁺-irrel (>∷≤ xs) (>∷≤ ys) = cong >∷≤_ (<⁺-irrel xs ys)
-- --   ≤⁺-irrel (x ∷≤ xs) (y ∷≤ ys) = cong₂ _∷≤_ (≤ᵇ-irrel x y) (≤⁺-irrel xs ys)

-- --   <⁺-irrel : Irrelevant _<⁺_
-- --   <⁺-irrel 1⁺<∷ 1⁺<∷ = refl
-- --   <⁺-irrel (<∷< xs) (<∷< ys) = cong <∷<_ (≤⁺-irrel xs ys)
-- --   <⁺-irrel (x ∷< xs) (y ∷< ys) = cong₂ _∷<_ (≤ᵇ-irrel x y) (<⁺-irrel xs ys)

-- -- ≤-irrel : Irrelevant _≤_
-- -- ≤-irrel 0≤n 0≤n = refl
-- -- ≤-irrel (⁺≤⁺ xs) (⁺≤⁺ ys) = cong ⁺≤⁺ (≤⁺-irrel xs ys)

-- -- <-irrel : Irrelevant _<_
-- -- <-irrel 0<⁺ 0<⁺ = refl
-- -- <-irrel (⁺<⁺ xs) (⁺<⁺ ys) = cong ⁺<⁺ (<⁺-irrel xs ys)

-- -- ≤ᵇ-refl : Reflexive _≤ᵇ_
-- -- ≤ᵇ-refl {O} = 0≤b
-- -- ≤ᵇ-refl {I} = I≤I

-- -- ≤⁺-refl : Reflexive _≤⁺_
-- -- ≤⁺-refl {1⁺} = 1⁺≤n
-- -- ≤⁺-refl {x ⁺∷ xs} = ≤ᵇ-refl ∷≤ ≤⁺-refl

-- -- ≤-refl : Reflexive _≤_
-- -- ≤-refl {0ᵇ} = 0≤n
-- -- ≤-refl {0< xs} = ⁺≤⁺ ≤⁺-refl

-- -- ≤ᵇ-trans : Transitive _≤ᵇ_
-- -- ≤ᵇ-trans 0≤b j≤k = 0≤b
-- -- ≤ᵇ-trans I≤I I≤I = I≤I

-- -- mutual
-- --   <∙≤⇒≤ : ∀ {x y z} → x <⁺ y → y ≤⁺ z → x ≤⁺ z
-- --   <∙≤⇒≤ i<j j≤k = {!!}

-- --   <∙≤⇒< : ∀ {x y z} → x <⁺ y → y ≤⁺ z → x <⁺ z
-- --   <∙≤⇒< i<j j≤k = {!!}

-- --   ≤∙<⇒< : ∀ {x y z} → x ≤⁺ y → y <⁺ z → x <⁺ z
-- --   ≤∙<⇒< i≤j j<k = {!!}

-- --   ≤∙<⇒≤ : ∀ {x y z} → x ≤⁺ y → y <⁺ z → x ≤⁺ z
-- --   ≤∙<⇒≤ i≤j j<k = {!!}

-- --   ≤⁺-trans : Transitive _≤⁺_
-- --   ≤⁺-trans 1⁺≤n j≤k = 1⁺≤n
-- --   ≤⁺-trans (>∷≤ i<j) (_∷≤_ {y = O} x j≤k) = >∷≤ <∙≤⇒< i<j j≤k
-- --   ≤⁺-trans (>∷≤ i<j) (_∷≤_ {y = I} x j≤k) = I≤I ∷≤ <∙≤⇒≤ i<j j≤k
-- --   ≤⁺-trans (x ∷≤ i≤j) (y ∷≤ j≤k) = ≤ᵇ-trans x y ∷≤ ≤⁺-trans i≤j j≤k
-- --   ≤⁺-trans (0≤b ∷≤ i≤j) (>∷≤ j<k) = 0≤b ∷≤ ≤∙<⇒≤ i≤j j<k
-- --   ≤⁺-trans (I≤I ∷≤ i≤j) (>∷≤ j<k) = >∷≤ ≤∙<⇒< i≤j j<k

-- --   <⁺-trans : Transitive _<⁺_
-- --   <⁺-trans 1⁺<∷ (<∷< x) = 1⁺<∷
-- --   <⁺-trans 1⁺<∷ (x ∷< j<k) = 1⁺<∷
-- --   <⁺-trans (<∷< i≤j) (0≤b ∷< j<k) = 0≤b ∷< ≤∙<⇒< i≤j j<k
-- --   <⁺-trans (<∷< i≤j) (I≤I ∷< j<k) = <∷< ≤∙<⇒≤ i≤j j<k
-- --   <⁺-trans (x ∷< i<j) (y ∷< j<k) = ≤ᵇ-trans y x ∷< <⁺-trans i<j j<k
-- --   <⁺-trans (_∷<_ {O} x i<j) (<∷< j≤k) = <∷< <∙≤⇒≤ i<j j≤k
-- --   <⁺-trans (_∷<_ {I} x i<j) (<∷< j≤k) = I≤I ∷< <∙≤⇒< i<j j≤k

-- -- -- -- ≤-trans : Transitive _≤_
-- -- -- -- ≤-trans 0≤n j≤k = 0≤n
-- -- -- -- ≤-trans (⁺≤⁺ i≤j) (⁺≤⁺ j≤k) = ⁺≤⁺ (≤⁺-trans i≤j j≤k)

-- -- -- -- <-trans : Transitive _<_
-- -- -- -- <-trans 0<⁺ (⁺<⁺ x) = 0<⁺
-- -- -- -- <-trans (⁺<⁺ xs) (⁺<⁺ ys) = ⁺<⁺ (<⁺-trans xs ys)
