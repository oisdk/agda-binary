{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Helpers where

private variable A B C : Set

open import Cubical.Foundations.Prelude
  using (_≡_; cong; refl; _∙_; sym; cong₂; subst; funExt)
  public

open import Cubical.Foundations.Isomorphism
  using (Iso)
  public

open import Cubical.Data.Empty
  using (⊥)
  renaming (rec to ⊥-elim)
  public

open Iso public

import Agda.Builtin.Nat as ℕ
open import Data.Binary.Helpers
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit public
open import Agda.Builtin.Maybe public

maybe : {A B : Set} → (A → B) → B → Maybe A → B
maybe f b nothing = b
maybe f b (just x) = f x

map-maybe : {A B : Set} → (A → B) → Maybe A → Maybe B
map-maybe f = maybe (just ∘ f) nothing

from-maybe : {A : Set} → A → Maybe A → A
from-maybe = maybe id

flip : (A → B → C) → B → A → C
flip f x y = f y x

infixr 2 ≡˘⟨⟩-syntax _≡⟨⟩_ ≡⟨∙⟩-syntax

≡˘⟨⟩-syntax : ∀ (x : A) {y z} → y ≡ z → y ≡ x → x ≡ z
≡˘⟨⟩-syntax _ y≡z y≡x = sym y≡x ∙ y≡z

syntax ≡˘⟨⟩-syntax x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

≡⟨∙⟩-syntax : ∀ (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨∙⟩-syntax _ y≡z x≡y = x≡y ∙ y≡z

syntax ≡⟨∙⟩-syntax x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

_≡⟨⟩_ : ∀ (x : A) {y} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

infix 2.5 _∎
_∎ : (x : A) → x ≡ x
_∎ x = refl

+-suc : ∀ x y → x ℕ.+ suc y ≡ suc (x ℕ.+ y)
+-suc zero y = refl
+-suc (suc x) y = cong suc (+-suc x y)

+-idʳ : ∀ x → x ℕ.+ 0 ≡ x
+-idʳ zero     = refl
+-idʳ (suc x)  = cong suc (+-idʳ x)

+-comm : ∀ x y → x ℕ.+ y ≡ y ℕ.+ x
+-comm x zero = +-idʳ x
+-comm x (suc y) = +-suc x y ∙ cong suc (+-comm x y)

+-assoc : ∀ x y z → (x ℕ.+ y) ℕ.+ z ≡ x ℕ.+ (y ℕ.+ z)
+-assoc zero     y z = refl
+-assoc (suc x)  y z = cong suc (+-assoc x y z)

+-*-distrib : ∀ x y z → (x ℕ.+ y) ℕ.* z ≡ x ℕ.* z ℕ.+ y ℕ.* z
+-*-distrib zero y z = refl
+-*-distrib (suc x) y z = cong (z ℕ.+_) (+-*-distrib x y z) ∙ sym (+-assoc z (x ℕ.* z) (y ℕ.* z))

T : Bool → Set
T true = ⊤
T false = ⊥

not : Bool → Bool
not true = false
not false = true

infix 4 _<_
_<_ : ℕ → ℕ → Set
n < m = T (n ℕ.< m)

infix 4 _≤ᴮ_
_≤ᴮ_ : ℕ → ℕ → Bool
n ≤ᴮ m = not (m ℕ.< n)

infix 4 _≤_
_≤_ : ℕ → ℕ → Set
n ≤ m = T (n ≤ᴮ m)

≤-trans : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p q = tt
≤-trans (suc n) zero zero p q = p
≤-trans (suc zero) zero (suc n) p q = tt
≤-trans (suc (suc n₁)) zero (suc n) p q = ≤-trans (suc n₁) zero n p tt
≤-trans (suc n) (suc zero) zero p q = q
≤-trans (suc zero) (suc zero) (suc n) p q = tt
≤-trans (suc (suc n₁)) (suc zero) (suc n) p q = ≤-trans (suc n₁) zero n p tt
≤-trans (suc n₁) (suc (suc n)) zero p q = q
≤-trans (suc zero) (suc (suc n₁)) (suc n) p q = tt
≤-trans (suc (suc n₁)) (suc (suc n₂)) (suc n) p q = ≤-trans (suc n₁) (suc n₂) n p q

s≤s : ∀ n m → n ≤ m → suc n ≤ suc m
s≤s zero m p = tt
s≤s (suc n) m p = p

n≤s : ∀ n m → n ≤ m → n ≤ suc m
n≤s zero m p = tt
n≤s (suc zero) m p = tt
n≤s (suc (suc n)) zero p = p
n≤s (suc (suc n₁)) (suc n) p = n≤s (suc n₁) n p

div-helper′ : (m n j : ℕ) → ℕ
div-helper′ m  zero    j      = zero
div-helper′ m (suc n)  zero   = suc (div-helper′ m n m)
div-helper′ m (suc n) (suc j) = div-helper′ m n j

div-helper-lemma : ∀ k m n j → ℕ.div-helper k m n j ≡ k ℕ.+ div-helper′ m n j
div-helper-lemma k m zero j = sym (+-idʳ k)
div-helper-lemma k m (suc n) zero = div-helper-lemma (suc k) m n m ∙ sym (+-suc k (div-helper′ m n m))
div-helper-lemma k m (suc n) (suc j) = div-helper-lemma k m n j

div2-≤ : ∀ n → div2 n ≤ n
div2-≤ n = subst (_≤ n) (sym (div-helper-lemma 0 1 n 1)) (go 1 n 1)
  where
  go : ∀ m n j → div-helper′ m n j ≤ n
  go m zero j = tt
  go m (suc n) zero = s≤s (div-helper′ m n m) n (go m n m)
  go m (suc n) (suc j) = n≤s (div-helper′ m n j) n (go m n j)

p≤p : ∀ n m → suc n ≤ suc m → n ≤ m
p≤p zero m p = tt
p≤p (suc n) m p = p

≤-refl : ∀ n → n ≤ n
≤-refl zero = tt
≤-refl (suc zero) = tt
≤-refl (suc (suc n)) = ≤-refl (suc n)

bool : ∀ {a} {A : Set a} → A → A → Bool → A
bool f t false = f
bool f t true = t

is-just : Maybe A → Bool
is-just (just _) = true
is-just _        = false

¬nothing≡just : {x : A} → (nothing ≡ just x) → ⊥
¬nothing≡just e = subst (bool ⊤ ⊥) (cong is-just e) tt

¬just≡nothing : {x : A} → (just x ≡ nothing) → ⊥
¬just≡nothing e = subst (bool ⊥ ⊤) (cong is-just e) tt

just-inj : {x y : A} → just x ≡ just y → x ≡ y
just-inj {x = x} = cong (from-maybe x)

*-zeroʳ : ∀ x → x ℕ.* zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc x) = *-zeroʳ x

*-suc : ∀ x y → x ℕ.+ x ℕ.* y ≡ x ℕ.* suc y
*-suc zero    y = refl
*-suc (suc x) y = cong suc (sym (+-assoc x y (x ℕ.* y)) ∙ cong (ℕ._+ x ℕ.* y) (+-comm x y) ∙ +-assoc y x (x ℕ.* y) ∙ cong (y ℕ.+_) (*-suc x y))

*-comm : ∀ x y → x ℕ.* y ≡ y ℕ.* x
*-comm zero    y = sym (*-zeroʳ y)
*-comm (suc x) y = cong (y ℕ.+_) (*-comm x y) ∙ *-suc y x

*-assoc : ∀ x y z → (x ℕ.* y) ℕ.* z ≡ x ℕ.* (y ℕ.* z)
*-assoc zero    y z = refl
*-assoc (suc x) y z = +-*-distrib y (x ℕ.* y) z ∙ cong (y ℕ.* z ℕ.+_) (*-assoc x y z)
