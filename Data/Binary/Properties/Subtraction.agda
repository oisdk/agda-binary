{-# OPTIONS --cubical #-}

module Data.Binary.Properties.Subtraction where

open import Data.Binary.Definition
open import Data.Binary.Addition
open import Data.Binary.Properties.Addition using (+-cong)
open import Data.Binary.Multiplication
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ

open import Data.Binary.Properties.Isomorphism

open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Properties.Double
open import Data.Binary.Double
open import Data.Binary.Subtraction

_-′_ : ℕ → ℕ → Maybe ℕ
n     -′ zero  = just n
zero  -′ suc _ = nothing
suc n -′ suc m = n -′ m

1ᵇℕ : ℕ → ℕ
1ᵇℕ n = suc (n ℕ.* 2)

-′‿cong : ∀ n m → from-maybe 0 (n -′ m) ≡ n ℕ.- m
-′‿cong n zero    = refl
-′‿cong zero (suc m) = refl
-′‿cong (suc n) (suc m) = -′‿cong n m

⟦_⇓⟧′ : Maybe 𝔹 → Maybe ℕ
⟦_⇓⟧′ = map-maybe ⟦_⇓⟧

exp-suc : ℕ → ℕ → ℕ
exp-suc zero x = x ℕ.* 2
exp-suc (suc n) x = (exp-suc n x) ℕ.* 2

maybe-fuse : {A B C : Set} (c : B → C) (f : A → B) (b : B) (x : Maybe A)
           → c (maybe f b x) ≡ maybe (c ∘ f) (c b) x
maybe-fuse _ _ _ nothing  = refl
maybe-fuse _ _ _ (just _) = refl

map-maybe-comp : {A B C : Set} (f : A → B) (b : B) (g : C → A) (x : Maybe C) → maybe f b (map-maybe g x) ≡ maybe (f ∘ g) b x
map-maybe-comp f b g = maybe-fuse (maybe f b) _ _

1ᵇz-lemma : ∀ n → ⟦ map-maybe 1ᵇ_ n ⇓⟧′ ≡ map-maybe 1ᵇℕ (map-maybe ⟦_⇓⟧ n)
1ᵇz-lemma nothing  = refl
1ᵇz-lemma (just x) = refl

1ᵇzs-distrib‿-′ : ∀ x y → map-maybe 1ᵇℕ (x -′ suc y) ≡  (x ℕ.* 2) -′ suc (y ℕ.* 2)
1ᵇzs-distrib‿-′ zero y = refl
1ᵇzs-distrib‿-′ (suc x) zero = refl
1ᵇzs-distrib‿-′ (suc x) (suc y) = 1ᵇzs-distrib‿-′ x y

2ᵇzs-distrib‿-′ : ∀ x y → map-maybe (ℕ._* 2) (x -′ suc y) ≡  (x ℕ.* 2) -′ suc (suc (y ℕ.* 2))
2ᵇzs-distrib‿-′ zero y = refl
2ᵇzs-distrib‿-′ (suc x) zero = refl
2ᵇzs-distrib‿-′ (suc x) (suc y) = 2ᵇzs-distrib‿-′ x y

1ᵇsz-distrib‿-′ : ∀ x y → map-maybe 1ᵇℕ (x -′ y) ≡ suc (x ℕ.* 2) -′ (y ℕ.* 2)
1ᵇsz-distrib‿-′ zero zero = refl
1ᵇsz-distrib‿-′ zero (suc y) = refl
1ᵇsz-distrib‿-′ (suc x) zero = refl
1ᵇsz-distrib‿-′ (suc x) (suc y) = 1ᵇsz-distrib‿-′ x y

+-cong‿-′ : ∀ n x y → (n ℕ.+ x) -′ (n ℕ.+ y) ≡ x -′ y
+-cong‿-′ zero x y = refl
+-cong‿-′ (suc n) x y = +-cong‿-′ n x y

*-distrib‿-′ : ∀ n x y → map-maybe (ℕ._* suc n) (x -′ y) ≡ (x ℕ.* suc n) -′ (y ℕ.* suc n)
*-distrib‿-′ n zero zero = refl
*-distrib‿-′ n zero (suc y) = refl
*-distrib‿-′ n (suc x) zero = refl
*-distrib‿-′ n (suc x) (suc y) = *-distrib‿-′ n x y ∙ sym (+-cong‿-′ n _ _)


-- sube-cong  : ∀ n xs ys → ⟦ sube  n xs ys ⇓⟧′ ≡ map-maybe (exp-suc n) (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧)
-- sube₁-cong : ∀ n xs ys → ⟦ sube₁ n xs ys ⇓⟧′ ≡ map-maybe (exp-suc n) (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧)
-- sub₁-cong  : ∀   xs ys → ⟦ sub₁ xs ys ⇓⟧′ ≡ ⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧
-- sub-cong   : ∀   xs ys → ⟦ sub xs ys ⇓⟧′ ≡ ⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧

-- sube-cong n _       0ᵇ      = {!!}
-- sube-cong n 0ᵇ      (1ᵇ ys) = {!!}
-- sube-cong n 0ᵇ      (2ᵇ ys) = {!!}
-- sube-cong n (1ᵇ xs) (1ᵇ ys) = {!!}
-- sube-cong n (1ᵇ xs) (2ᵇ ys) = {!!}
-- sube-cong n (2ᵇ xs) (1ᵇ ys) = {!!}
-- sube-cong n (2ᵇ xs) (2ᵇ ys) = {!!}

-- sube₁-cong n 0ᵇ      _       = refl
-- sube₁-cong n (1ᵇ xs) 0ᵇ      = {!!}
-- sube₁-cong n (1ᵇ xs) (1ᵇ ys) = {!!}
-- sube₁-cong n (1ᵇ xs) (2ᵇ ys) = {!!}
-- sube₁-cong n (2ᵇ xs) 0ᵇ      = {!!}
-- sube₁-cong n (2ᵇ xs) (1ᵇ ys) = {!!}
-- sube₁-cong n (2ᵇ xs) (2ᵇ ys) = {!!}

-- sub₁-cong 0ᵇ      _       = refl
-- sub₁-cong (1ᵇ xs) 0ᵇ      = cong just (double-cong xs)
-- sub₁-cong (1ᵇ xs) (1ᵇ ys) = 1ᵇz-lemma (sub₁ xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub₁-cong xs ys) ∙ 1ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
-- sub₁-cong (1ᵇ xs) (2ᵇ ys) = sube₁-cong 0 xs ys ∙ 2ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
-- sub₁-cong (2ᵇ xs) 0ᵇ      = refl
-- sub₁-cong (2ᵇ xs) (1ᵇ ys) = sube-cong 0 xs ys ∙ *-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
-- sub₁-cong (2ᵇ xs) (2ᵇ ys) = 1ᵇz-lemma (sub₁ xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub₁-cong xs ys) ∙ 1ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧

-- sub-cong xs 0ᵇ           = refl
-- sub-cong 0ᵇ      (1ᵇ _)  = refl
-- sub-cong 0ᵇ      (2ᵇ _)  = refl
-- sub-cong (1ᵇ xs) (1ᵇ ys) = sube-cong 0 xs ys ∙ *-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
-- sub-cong (2ᵇ xs) (2ᵇ ys) = sube-cong 0 xs ys ∙ *-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
-- sub-cong (1ᵇ xs) (2ᵇ ys) = 1ᵇz-lemma (sub₁ xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub₁-cong xs ys) ∙ 1ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
-- sub-cong (2ᵇ xs) (1ᵇ ys) = 1ᵇz-lemma (sub xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub-cong xs ys) ∙ 1ᵇsz-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧

-- -‿cong : ∀ xs ys → ⟦ xs - ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.- ⟦ ys ⇓⟧
-- -‿cong x y = maybe-fuse ⟦_⇓⟧ _ _ (sub x y)
--            ∙ sym (map-maybe-comp _ _ ⟦_⇓⟧ (sub x y))
--            ∙ cong (from-maybe 0) (sub-cong x y)
--            ∙ -′‿cong ⟦ x ⇓⟧ ⟦ y ⇓⟧
