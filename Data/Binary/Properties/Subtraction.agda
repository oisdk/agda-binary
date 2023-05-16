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

exp2 : ℕ → ℕ → ℕ
exp2 zero    x = x
exp2 (suc n) x = exp2 n x ℕ.* 2

exp2-𝔹 : ℕ → 𝔹 → 𝔹
exp2-𝔹 zero    xs = xs
exp2-𝔹 (suc n) xs = exp2-𝔹 n (2× xs)

exp2-𝔹-0ᵇ : ∀ n → exp2-𝔹 n 0ᵇ ≡ 0ᵇ
exp2-𝔹-0ᵇ zero = refl
exp2-𝔹-0ᵇ (suc n) = exp2-𝔹-0ᵇ n

exp2-𝔹-2ᵇ : ∀ n xs → exp2-𝔹 n (2ᵇ xs) ≡ xs +1×2^suc n
exp2-𝔹-2ᵇ zero 0ᵇ = refl
exp2-𝔹-2ᵇ zero (1ᵇ xs) = refl
exp2-𝔹-2ᵇ zero (2ᵇ xs) = refl
exp2-𝔹-2ᵇ (suc n) xs = exp2-𝔹-2ᵇ n (1ᵇ xs)

exp2-𝔹-×2^suc : ∀ n xs → exp2-𝔹 (suc n) xs ≡ xs ×2^suc n
exp2-𝔹-×2^suc n 0ᵇ      = exp2-𝔹-0ᵇ n
exp2-𝔹-×2^suc n (1ᵇ xs) = exp2-𝔹-2ᵇ n (2× xs)
exp2-𝔹-×2^suc n (2ᵇ xs) = exp2-𝔹-2ᵇ n (1ᵇ xs)

exp2-assoc : ∀ n m → exp2 n (m ℕ.* 2) ≡ exp2 n m ℕ.* 2
exp2-assoc zero m = refl
exp2-assoc (suc n) m = cong (ℕ._* 2) (exp2-assoc n m)

exp2-𝔹-cong : ∀ n xs → ⟦ exp2-𝔹 n xs ⇓⟧ ≡ exp2 n ⟦ xs ⇓⟧
exp2-𝔹-cong zero xs = refl
exp2-𝔹-cong (suc n) xs = exp2-𝔹-cong n (2× xs) ∙ cong (exp2 n) (double-cong xs) ∙ exp2-assoc n ⟦ xs ⇓⟧

×2^suc-cong : ∀ n xs → ⟦ xs ×2^suc n ⇓⟧ ≡ exp2 (suc n) ⟦ xs ⇓⟧
×2^suc-cong n xs = cong ⟦_⇓⟧ (sym (exp2-𝔹-×2^suc n xs)) ∙ exp2-𝔹-cong (suc n) xs

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

-′‿*2-suc : ∀ x y → map-maybe suc ((x ℕ.* 2) -′ (y ℕ.* 2)) ≡ suc (x ℕ.* 2) -′ (y ℕ.* 2)
-′‿*2-suc zero zero = refl
-′‿*2-suc zero (suc y) = refl
-′‿*2-suc (suc x) zero = refl
-′‿*2-suc (suc x) (suc y) = -′‿*2-suc x y

-′‿suc-*2 : ∀ x y → map-maybe (suc ∘ (ℕ._* 2)) (x -′ suc y) ≡ (x ℕ.* 2) -′ suc (y ℕ.* 2)
-′‿suc-*2 zero zero = refl
-′‿suc-*2 zero (suc y) = refl
-′‿suc-*2 (suc x) zero = refl
-′‿suc-*2 (suc x) (suc y) = -′‿suc-*2 x y

+1×2^suc-cong : ∀ n xs → ⟦ xs +1×2^suc n ⇓⟧ ≡ exp2 (suc n) (suc ⟦ xs ⇓⟧)
+1×2^suc-cong n xs = cong ⟦_⇓⟧ (sym (exp2-𝔹-2ᵇ n xs)) ∙ exp2-𝔹-cong n (2ᵇ xs) ∙ exp2-assoc n (suc ⟦ xs ⇓⟧)

exp-suc-lemma : ∀ n xs ys → map-maybe (λ x → exp2 n x ℕ.* 2 ℕ.* 2) (xs -′ ys) ≡
                  map-maybe (λ x → exp2 n x ℕ.* 2)
                  ((xs ℕ.* 2) -′ (ys ℕ.* 2))
exp-suc-lemma n xs ys = cong (flip map-maybe (xs -′ ys)) (funExt (λ x → cong (ℕ._* 2) (sym (exp2-assoc n x)))) ∙ sym (map-maybe-comp _ _ _ (xs -′ ys)) ∙ cong (map-maybe (exp2 (suc n))) (*-distrib‿-′ 1 xs ys)

subᵉ₁-0-cong : ∀ n xs ys → ⟦ map-maybe (_+1×2^suc n) (subᵉ₁ 0 xs ys) ⇓⟧′ ≡ map-maybe (exp2 (suc n)) ((⟦ xs ⇓⟧ ℕ.* 2) -′ suc (⟦ ys ⇓⟧ ℕ.* 2))
subᵉ-0-cong : ∀ n xs ys → ⟦ map-maybe (_+1×2^suc n) (subᵉ 0 xs ys) ⇓⟧′ ≡ map-maybe (exp2 (suc n)) (suc (⟦ xs ⇓⟧ ℕ.* 2) -′ (⟦ ys ⇓⟧ ℕ.* 2))
subᵉ-cong  : ∀ n xs ys → ⟦ subᵉ  n xs ys ⇓⟧′ ≡ map-maybe (exp2 (suc n)) (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧)
subᵉ₁-cong : ∀ n xs ys → ⟦ subᵉ₁ n xs ys ⇓⟧′ ≡ map-maybe (exp2 (suc n)) (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧)
sub₁-cong  : ∀   xs ys → ⟦ sub₁ xs ys ⇓⟧′ ≡ ⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧
sub-cong   : ∀   xs ys → ⟦ sub xs ys ⇓⟧′ ≡ ⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧

subᵉ₁-0-cong n xs ys =
  ⟦ map-maybe (_+1×2^suc n) (subᵉ₁ 0 xs ys) ⇓⟧′ ≡⟨ map-maybe-comp _ _ _ (subᵉ₁ 0 xs ys) ⟩
  map-maybe (⟦_⇓⟧ ∘ (_+1×2^suc n)) (subᵉ₁ 0 xs ys) ≡⟨ cong (flip map-maybe (subᵉ₁ 0 xs ys)) (funExt (+1×2^suc-cong n)) ⟩
  map-maybe (exp2 (suc n) ∘ suc ∘ ⟦_⇓⟧) (subᵉ₁ 0 xs ys) ≡˘⟨ map-maybe-comp _ _ _ (subᵉ₁ 0 xs ys) ⟩
  map-maybe (exp2 (suc n) ∘ suc) ⟦ subᵉ₁ 0 xs ys ⇓⟧′ ≡⟨ cong (map-maybe (exp2 (suc n) ∘ suc)) (subᵉ₁-cong 0 xs ys) ⟩
  map-maybe (exp2 (suc n) ∘ suc) (map-maybe (exp2 1) (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧)) ≡⟨ map-maybe-comp _ _ _ (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n) ∘ suc ∘ exp2 1) (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧) ≡˘⟨ map-maybe-comp _ _ _ (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n)) (map-maybe (suc ∘ exp2 1) (⟦ xs ⇓⟧ -′ suc ⟦ ys ⇓⟧)) ≡⟨ cong (map-maybe (exp2 (suc n))) (-′‿suc-*2 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n)) ((⟦ xs ⇓⟧ ℕ.* 2) -′ suc (⟦ ys ⇓⟧ ℕ.* 2)) ∎

subᵉ-0-cong n xs ys =
  ⟦ map-maybe (_+1×2^suc n) (subᵉ 0 xs ys) ⇓⟧′ ≡⟨ map-maybe-comp _ _ _ (subᵉ 0 xs ys) ⟩
  map-maybe (⟦_⇓⟧ ∘ (_+1×2^suc n)) (subᵉ 0 xs ys) ≡⟨ cong (flip map-maybe (subᵉ 0 xs ys)) (funExt (+1×2^suc-cong n)) ⟩
  map-maybe (exp2 (suc n) ∘ suc ∘ ⟦_⇓⟧) (subᵉ 0 xs ys) ≡˘⟨ map-maybe-comp _ _ _ (subᵉ 0 xs ys) ⟩
  map-maybe (exp2 (suc n) ∘ suc) ⟦ subᵉ 0 xs ys ⇓⟧′ ≡⟨ cong (map-maybe (exp2 (suc n) ∘ suc)) (subᵉ-cong 0 xs ys) ⟩
  map-maybe (exp2 (suc n) ∘ suc) (map-maybe (exp2 1) (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧)) ≡⟨ map-maybe-comp _ _ _ (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n) ∘ suc ∘ exp2 1) (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧) ≡˘⟨ map-maybe-comp _ _ _ (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n)) (map-maybe (suc ∘ exp2 1) (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧)) ≡˘⟨ cong (map-maybe (exp2 (suc n))) (map-maybe-comp _ _ _ (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧)) ⟩
  map-maybe (exp2 (suc n)) (map-maybe suc (map-maybe (exp2 1) (⟦ xs ⇓⟧ -′ ⟦ ys ⇓⟧))) ≡⟨ cong (map-maybe (exp2 (suc n)) ∘ map-maybe suc) (*-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n)) (map-maybe suc (exp2 1 ⟦ xs ⇓⟧ -′ exp2 1 ⟦ ys ⇓⟧)) ≡⟨ cong (map-maybe (exp2 (suc n))) (-′‿*2-suc ⟦ xs ⇓⟧ ⟦ ys ⇓⟧) ⟩
  map-maybe (exp2 (suc n)) (suc (⟦ xs ⇓⟧ ℕ.* 2) -′ (⟦ ys ⇓⟧ ℕ.* 2)) ∎

subᵉ-cong n xs      0ᵇ      = cong just (×2^suc-cong n xs)
subᵉ-cong n 0ᵇ      (1ᵇ ys) = refl
subᵉ-cong n 0ᵇ      (2ᵇ ys) = refl
subᵉ-cong n (1ᵇ xs) (1ᵇ ys) = subᵉ-cong (suc n) xs ys ∙ exp-suc-lemma n ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
subᵉ-cong n (1ᵇ xs) (2ᵇ ys) = subᵉ₁-0-cong n xs ys
subᵉ-cong n (2ᵇ xs) (1ᵇ ys) = subᵉ-0-cong n xs ys

subᵉ-cong n (2ᵇ xs) (2ᵇ ys) = subᵉ-cong (suc n) xs ys ∙ exp-suc-lemma n ⟦ xs ⇓⟧ ⟦ ys ⇓⟧

subᵉ₁-cong n 0ᵇ      _       = refl
subᵉ₁-cong n (1ᵇ xs) 0ᵇ      = cong just (×2^suc-cong (suc n) xs ∙ cong (ℕ._* 2) (sym (exp2-assoc n ⟦ xs ⇓⟧)))
subᵉ₁-cong n (1ᵇ xs) (1ᵇ ys) = subᵉ₁-0-cong n xs ys
subᵉ₁-cong n (1ᵇ xs) (2ᵇ ys) = subᵉ₁-cong (suc n) xs ys ∙ exp-suc-lemma n ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
subᵉ₁-cong n (2ᵇ xs) 0ᵇ      = cong just (+1×2^suc-cong n (2× xs) ∙ cong (λ e → exp2 n (suc e) ℕ.* 2) (double-cong xs))
subᵉ₁-cong n (2ᵇ xs) (1ᵇ ys) = subᵉ-cong (suc n) xs ys ∙ exp-suc-lemma n ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
subᵉ₁-cong n (2ᵇ xs) (2ᵇ ys) = subᵉ₁-0-cong n xs ys

sub₁-cong 0ᵇ      _       = refl
sub₁-cong (1ᵇ xs) 0ᵇ      = cong just (double-cong xs)
sub₁-cong (1ᵇ xs) (1ᵇ ys) = 1ᵇz-lemma (sub₁ xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub₁-cong xs ys) ∙ 1ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub₁-cong (1ᵇ xs) (2ᵇ ys) = subᵉ₁-cong 0 xs ys ∙ 2ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub₁-cong (2ᵇ xs) 0ᵇ      = refl
sub₁-cong (2ᵇ xs) (1ᵇ ys) = subᵉ-cong 0 xs ys ∙ *-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub₁-cong (2ᵇ xs) (2ᵇ ys) = 1ᵇz-lemma (sub₁ xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub₁-cong xs ys) ∙ 1ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧

sub-cong xs 0ᵇ           = refl
sub-cong 0ᵇ      (1ᵇ _)  = refl
sub-cong 0ᵇ      (2ᵇ _)  = refl
sub-cong (1ᵇ xs) (1ᵇ ys) = subᵉ-cong 0 xs ys ∙ *-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (2ᵇ xs) (2ᵇ ys) = subᵉ-cong 0 xs ys ∙ *-distrib‿-′ 1 ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (1ᵇ xs) (2ᵇ ys) = 1ᵇz-lemma (sub₁ xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub₁-cong xs ys) ∙ 1ᵇzs-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (2ᵇ xs) (1ᵇ ys) = 1ᵇz-lemma (sub xs ys) ∙ cong (map-maybe 1ᵇℕ) (sub-cong xs ys) ∙ 1ᵇsz-distrib‿-′ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧

-‿cong : ∀ xs ys → ⟦ xs - ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.- ⟦ ys ⇓⟧
-‿cong x y = maybe-fuse ⟦_⇓⟧ _ _ (sub x y)
           ∙ sym (map-maybe-comp _ _ ⟦_⇓⟧ (sub x y))
           ∙ cong (from-maybe 0) (sub-cong x y)
           ∙ -′‿cong ⟦ x ⇓⟧ ⟦ y ⇓⟧
