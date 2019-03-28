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

pattern ≺ = O
pattern ≼ = I

⟅_⟆_≺ᵇ_ : Bit → Bit → Bit → Bit
⟅ p ⟆ I ≺ᵇ q = q ∧ p
⟅ p ⟆ O ≺ᵇ q = q ∨ p

⟅_⟆_≺⁺_ : Bit → 𝔹⁺ → 𝔹⁺ → Set
⟅ p ⟆ 1ᵇ        ≺⁺ (y ∷ ys) = ⊤
⟅ p ⟆ 1ᵇ        ≺⁺ 1ᵇ = T p
⟅ p ⟆ (x ∷ xs) ≺⁺ 1ᵇ = ⊥
⟅ p ⟆ (x ∷ xs) ≺⁺ (y ∷ ys) = ⟅ ⟅ p ⟆ x ≺ᵇ y ⟆ xs ≺⁺ ys

⟅_⟆_≺_ : Bit → 𝔹 → 𝔹 → Set
⟅ p ⟆ 0ᵇ ≺ 0ᵇ = T p
⟅ p ⟆ 0ᵇ ≺ (0< x) = ⊤
⟅ p ⟆ 0< x ≺ 0ᵇ = ⊥
⟅ p ⟆ 0< xs ≺ (0< ys) = ⟅ p ⟆ xs ≺⁺ ys

weaken : ∀ x xs ys → ⟅ x ⟆ xs ≺⁺ ys → ⟅ I ⟆ xs ≺⁺ ys
weaken I xs ys xs<ys = xs<ys
weaken O 1ᵇ 1ᵇ xs<ys = tt
weaken O 1ᵇ (x ∷ ys) xs<ys = tt
weaken O (x ∷ xs) 1ᵇ xs<ys = xs<ys
weaken O (O ∷ xs) (O ∷ ys) xs<ys = weaken O xs ys xs<ys
weaken O (O ∷ xs) (I ∷ ys) xs<ys = xs<ys
weaken O (I ∷ xs) (O ∷ ys) xs<ys = xs<ys
weaken O (I ∷ xs) (I ∷ ys) xs<ys = weaken O xs ys xs<ys

≺⁺-trans : ∀ x y xs ys zs → ⟅ x ⟆ xs ≺⁺ ys → ⟅ y ⟆ ys ≺⁺ zs → ⟅ x ∧ y ⟆ xs ≺⁺ zs
≺⁺-trans xc yc (x ∷ xs) 1ᵇ (z ∷ zs) () ys<zs
≺⁺-trans xc yc (O ∷ xs) (O ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
≺⁺-trans O yc (O ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = weaken O xs zs (≺⁺-trans O I xs ys zs xs<ys ys<zs)
≺⁺-trans I yc (O ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans I I xs ys zs xs<ys ys<zs
≺⁺-trans xc yc (O ∷ xs) (I ∷ ys) (I ∷ zs) xs<ys ys<zs = weaken yc xs zs (≺⁺-trans I yc xs ys zs xs<ys ys<zs)
≺⁺-trans O yc (O ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans I O (O ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans I I (O ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = weaken O xs zs (≺⁺-trans I O xs ys zs xs<ys ys<zs)
≺⁺-trans xc yc (I ∷ xs) (O ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans O yc xs ys zs xs<ys ys<zs
≺⁺-trans O yc (I ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans O I xs ys zs xs<ys ys<zs
≺⁺-trans I O (I ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans O I xs ys zs xs<ys ys<zs
≺⁺-trans I I (I ∷ xs) (O ∷ ys) (I ∷ zs) xs<ys ys<zs = weaken O xs zs (≺⁺-trans O I xs ys zs xs<ys ys<zs)
≺⁺-trans xc yc (I ∷ xs) (I ∷ ys) (I ∷ zs) xs<ys ys<zs = ≺⁺-trans xc yc xs ys zs xs<ys ys<zs
≺⁺-trans O yc (I ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans O O xs ys zs xs<ys ys<zs
≺⁺-trans I yc (I ∷ xs) (I ∷ ys) (O ∷ zs) xs<ys ys<zs = ≺⁺-trans I O xs ys zs xs<ys ys<zs
≺⁺-trans xc yc (x ∷ xs) 1ᵇ 1ᵇ () ys<zs
≺⁺-trans xc yc (x ∷ xs) (x₁ ∷ ys) 1ᵇ xs<ys ()
≺⁺-trans O O 1ᵇ ys (z ∷ zs) xs<ys ys<zs = tt
≺⁺-trans O O 1ᵇ 1ᵇ 1ᵇ ()
≺⁺-trans O O 1ᵇ (y ∷ ys) 1ᵇ xs<ys ()
≺⁺-trans O I 1ᵇ ys (z ∷ zs) xs<ys ys<zs = tt
≺⁺-trans O I 1ᵇ 1ᵇ 1ᵇ () ys<zs
≺⁺-trans O I 1ᵇ (x ∷ ys) 1ᵇ xs<ys ()
≺⁺-trans I O 1ᵇ ys (x ∷ zs) xs<ys ys<zs = tt
≺⁺-trans I O 1ᵇ 1ᵇ 1ᵇ xs<ys ()
≺⁺-trans I O 1ᵇ (x ∷ ys) 1ᵇ xs<ys ()
≺⁺-trans I I 1ᵇ ys 1ᵇ xs<ys ys<zs = tt
≺⁺-trans I I 1ᵇ ys (x ∷ zs) xs<ys ys<zs = tt


-- -- -- infix 4 _<⁺_ _<_ _≤⁺_ _≤_ _≤ᵇ_

-- -- -- _<⁺_ : 𝔹⁺ → 𝔹⁺ → Set
-- -- -- _<⁺_ = ⟅ ⊥ ⟆_≺⁺_

-- -- -- _≤⁺_ : 𝔹⁺ → 𝔹⁺ → Set
-- -- -- _≤⁺_ = ⟅ ⊤ ⟆_≺⁺_

-- -- -- _<_ : 


-- -- -- data _<_ : 𝔹 → 𝔹 → Set where
-- -- --   0<⁺ : ∀ {ys} → 0ᵇ < (0< ys)
-- -- --   ⁺<⁺ : ∀ {xs ys} → xs <⁺ ys → (0< xs) < (0< ys)

-- -- -- data _≤_ : 𝔹 → 𝔹 → Set where
-- -- --   0≤n : ∀ {ys} → 0ᵇ ≤ ys
-- -- --   ⁺≤⁺ : ∀ {xs ys} → xs ≤⁺ ys → (0< xs) ≤ (0< ys)

-- -- -- _≤ᵇ?_ : Decidable _≤ᵇ_
-- -- -- O ≤ᵇ? y = yes 0≤b
-- -- -- I ≤ᵇ? O = no λ ()
-- -- -- I ≤ᵇ? I = yes I≤I

-- -- -- mutual
-- -- --   _≤⁺?_ : Decidable _≤⁺_
-- -- --   1ᵇ ≤⁺? ys = yes 1ᵇ≤n
-- -- --   (x ∷ xs) ≤⁺? 1ᵇ = no λ ()
-- -- --   (O ∷ xs) ≤⁺? (y ∷ ys) = map′ (0≤b ∷≤_) (λ { (x ∷≤ xs) → xs}) (xs ≤⁺? ys)
-- -- --   (I ∷ xs) ≤⁺? (O ∷ ys) = map′ >∷≤_ (λ { (>∷≤ zs) → zs}) (xs <⁺? ys)
-- -- --   (I ∷ xs) ≤⁺? (I ∷ ys) = map′ (I≤I ∷≤_) (λ { (x ∷≤ zs) → zs}) (xs ≤⁺? ys)

-- -- --   _<⁺?_ : Decidable _<⁺_
-- -- --   xs <⁺? 1ᵇ = no λ ()
-- -- --   1ᵇ <⁺? (y ∷ ys) = yes 1ᵇ<∷
-- -- --   (x ∷ xs) <⁺? (O ∷ ys) = map′ (0≤b ∷<_) (λ { (x ∷< zs) → zs}) (xs <⁺? ys)
-- -- --   (O ∷ xs) <⁺? (I ∷ ys) = map′ <∷<_ (λ { (<∷< zs) → zs}) (xs ≤⁺? ys)
-- -- --   (I ∷ xs) <⁺? (I ∷ ys) = map′ (I≤I ∷<_) (λ { (x ∷< zs) → zs}) (xs <⁺? ys)

-- -- -- _≤?_ : Decidable _≤_
-- -- -- 0ᵇ ≤? ys = yes 0≤n
-- -- -- (0< xs) ≤? 0ᵇ = no λ ()
-- -- -- (0< xs) ≤? (0< ys) = map′ ⁺≤⁺ (λ { (⁺≤⁺ x) → x}) (xs ≤⁺? ys)

-- -- -- _<?_ : Decidable _<_
-- -- -- xs <? 0ᵇ = no λ ()
-- -- -- 0ᵇ <? (0< ys) = yes 0<⁺
-- -- -- (0< xs) <? (0< ys) = map′ ⁺<⁺ (λ { (⁺<⁺ x) → x}) (xs <⁺? ys)

-- -- -- ≤ᵇ-irrel : Irrelevant _≤ᵇ_
-- -- -- ≤ᵇ-irrel 0≤b 0≤b = refl
-- -- -- ≤ᵇ-irrel I≤I I≤I = refl

-- -- -- mutual
-- -- --   ≤⁺-irrel : Irrelevant _≤⁺_
-- -- --   ≤⁺-irrel 1ᵇ≤n 1ᵇ≤n = refl
-- -- --   ≤⁺-irrel (>∷≤ xs) (>∷≤ ys) = cong >∷≤_ (<⁺-irrel xs ys)
-- -- --   ≤⁺-irrel (x ∷≤ xs) (y ∷≤ ys) = cong₂ _∷≤_ (≤ᵇ-irrel x y) (≤⁺-irrel xs ys)

-- -- --   <⁺-irrel : Irrelevant _<⁺_
-- -- --   <⁺-irrel 1ᵇ<∷ 1ᵇ<∷ = refl
-- -- --   <⁺-irrel (<∷< xs) (<∷< ys) = cong <∷<_ (≤⁺-irrel xs ys)
-- -- --   <⁺-irrel (x ∷< xs) (y ∷< ys) = cong₂ _∷<_ (≤ᵇ-irrel x y) (<⁺-irrel xs ys)

-- -- -- ≤-irrel : Irrelevant _≤_
-- -- -- ≤-irrel 0≤n 0≤n = refl
-- -- -- ≤-irrel (⁺≤⁺ xs) (⁺≤⁺ ys) = cong ⁺≤⁺ (≤⁺-irrel xs ys)

-- -- -- <-irrel : Irrelevant _<_
-- -- -- <-irrel 0<⁺ 0<⁺ = refl
-- -- -- <-irrel (⁺<⁺ xs) (⁺<⁺ ys) = cong ⁺<⁺ (<⁺-irrel xs ys)

-- -- -- ≤ᵇ-refl : Reflexive _≤ᵇ_
-- -- -- ≤ᵇ-refl {O} = 0≤b
-- -- -- ≤ᵇ-refl {I} = I≤I

-- -- -- ≤⁺-refl : Reflexive _≤⁺_
-- -- -- ≤⁺-refl {1ᵇ} = 1ᵇ≤n
-- -- -- ≤⁺-refl {x ∷ xs} = ≤ᵇ-refl ∷≤ ≤⁺-refl

-- -- -- ≤-refl : Reflexive _≤_
-- -- -- ≤-refl {0ᵇ} = 0≤n
-- -- -- ≤-refl {0< xs} = ⁺≤⁺ ≤⁺-refl

-- -- -- ≤ᵇ-trans : Transitive _≤ᵇ_
-- -- -- ≤ᵇ-trans 0≤b j≤k = 0≤b
-- -- -- ≤ᵇ-trans I≤I I≤I = I≤I

-- -- -- mutual
-- -- --   <∙≤⇒≤ : ∀ {x y z} → x <⁺ y → y ≤⁺ z → x ≤⁺ z
-- -- --   <∙≤⇒≤ i<j j≤k = {!!}

-- -- --   <∙≤⇒< : ∀ {x y z} → x <⁺ y → y ≤⁺ z → x <⁺ z
-- -- --   <∙≤⇒< i<j j≤k = {!!}

-- -- --   ≤∙<⇒< : ∀ {x y z} → x ≤⁺ y → y <⁺ z → x <⁺ z
-- -- --   ≤∙<⇒< i≤j j<k = {!!}

-- -- --   ≤∙<⇒≤ : ∀ {x y z} → x ≤⁺ y → y <⁺ z → x ≤⁺ z
-- -- --   ≤∙<⇒≤ i≤j j<k = {!!}

-- -- --   ≤⁺-trans : Transitive _≤⁺_
-- -- --   ≤⁺-trans 1ᵇ≤n j≤k = 1ᵇ≤n
-- -- --   ≤⁺-trans (>∷≤ i<j) (_∷≤_ {y = O} x j≤k) = >∷≤ <∙≤⇒< i<j j≤k
-- -- --   ≤⁺-trans (>∷≤ i<j) (_∷≤_ {y = I} x j≤k) = I≤I ∷≤ <∙≤⇒≤ i<j j≤k
-- -- --   ≤⁺-trans (x ∷≤ i≤j) (y ∷≤ j≤k) = ≤ᵇ-trans x y ∷≤ ≤⁺-trans i≤j j≤k
-- -- --   ≤⁺-trans (0≤b ∷≤ i≤j) (>∷≤ j<k) = 0≤b ∷≤ ≤∙<⇒≤ i≤j j<k
-- -- --   ≤⁺-trans (I≤I ∷≤ i≤j) (>∷≤ j<k) = >∷≤ ≤∙<⇒< i≤j j<k

-- -- --   <⁺-trans : Transitive _<⁺_
-- -- --   <⁺-trans 1ᵇ<∷ (<∷< x) = 1ᵇ<∷
-- -- --   <⁺-trans 1ᵇ<∷ (x ∷< j<k) = 1ᵇ<∷
-- -- --   <⁺-trans (<∷< i≤j) (0≤b ∷< j<k) = 0≤b ∷< ≤∙<⇒< i≤j j<k
-- -- --   <⁺-trans (<∷< i≤j) (I≤I ∷< j<k) = <∷< ≤∙<⇒≤ i≤j j<k
-- -- --   <⁺-trans (x ∷< i<j) (y ∷< j<k) = ≤ᵇ-trans y x ∷< <⁺-trans i<j j<k
-- -- --   <⁺-trans (_∷<_ {O} x i<j) (<∷< j≤k) = <∷< <∙≤⇒≤ i<j j≤k
-- -- --   <⁺-trans (_∷<_ {I} x i<j) (<∷< j≤k) = I≤I ∷< <∙≤⇒< i<j j≤k

-- -- -- -- -- ≤-trans : Transitive _≤_
-- -- -- -- -- ≤-trans 0≤n j≤k = 0≤n
-- -- -- -- -- ≤-trans (⁺≤⁺ i≤j) (⁺≤⁺ j≤k) = ⁺≤⁺ (≤⁺-trans i≤j j≤k)

-- -- -- -- -- <-trans : Transitive _<_
-- -- -- -- -- <-trans 0<⁺ (⁺<⁺ x) = 0<⁺
-- -- -- -- -- <-trans (⁺<⁺ xs) (⁺<⁺ ys) = ⁺<⁺ (<⁺-trans xs ys)
