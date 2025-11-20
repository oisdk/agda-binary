{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Conversion where

open import Data.Binary.Conversion
open import Data.Binary.Definition
open import Data.Binary.Increment
import Data.Binary.Conversion.Fast as F
open import Data.Binary.Conversion.Fast using (⟦_⇑⟧⟨_⟩)

open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
import Agda.Builtin.Nat as ℕ
open import Agda.Builtin.Bool

tail𝔹 : 𝔹 → 𝔹
tail𝔹 0ᵇ = 0ᵇ
tail𝔹 (1ᵇ xs) = xs
tail𝔹 (2ᵇ xs) = xs

tail𝔹-inc : ∀ xs → inc (tail𝔹 (inc xs)) ≡ tail𝔹 (inc (inc (inc xs)))
tail𝔹-inc 0ᵇ = refl
tail𝔹-inc (1ᵇ xs) = refl
tail𝔹-inc (2ᵇ xs) = refl

tail-homo : ∀ n → tail𝔹 (inc ⟦ n ⇑⟧) ≡ ⟦ div2 n ⇑⟧
tail-homo n = go n ∙ cong ⟦_⇑⟧ (sym (div-helper-lemma 0 1 n 1))
  where
  go : ∀ n → tail𝔹 (inc ⟦ n ⇑⟧) ≡ ⟦ div-helper′ 1 n 1 ⇑⟧
  go zero = refl
  go (suc zero) = refl
  go (suc (suc n)) = sym (tail𝔹-inc ⟦ n ⇑⟧) ∙ cong inc (go n)

head𝔹 : 𝔹 → Maybe Bool
head𝔹 0ᵇ = nothing
head𝔹 (1ᵇ xs) = just true
head𝔹 (2ᵇ xs) = just false

head𝔹-inc : ∀ xs → head𝔹 (inc (inc (inc xs))) ≡ head𝔹 (inc xs)
head𝔹-inc 0ᵇ = refl
head𝔹-inc (1ᵇ xs) = refl
head𝔹-inc (2ᵇ xs) = refl

head𝔹-homo : ∀ n → head𝔹 (inc ⟦ n ⇑⟧) ≡ just (even n)
head𝔹-homo zero    = refl
head𝔹-homo (suc zero) = refl
head𝔹-homo (suc (suc n)) = head𝔹-inc ⟦ n ⇑⟧ ∙ head𝔹-homo n

head-tail-cong : ∀ xs ys → head𝔹 xs ≡ head𝔹 ys → tail𝔹 xs ≡ tail𝔹 ys → xs ≡ ys
head-tail-cong 0ᵇ 0ᵇ h≡ t≡ = refl
head-tail-cong 0ᵇ (1ᵇ ys) h≡ t≡ = ⊥-elim (¬nothing≡just h≡)
head-tail-cong 0ᵇ (2ᵇ ys) h≡ t≡ = ⊥-elim (¬nothing≡just h≡)
head-tail-cong (1ᵇ xs) 0ᵇ h≡ t≡ = ⊥-elim (¬just≡nothing h≡)
head-tail-cong (1ᵇ xs) (1ᵇ ys) h≡ t≡ = cong 1ᵇ_ t≡
head-tail-cong (1ᵇ xs) (2ᵇ ys) h≡ t≡ = ⊥-elim (subst (bool ⊥ ⊤) (just-inj h≡) tt)
head-tail-cong (2ᵇ xs) 0ᵇ h≡ t≡ = ⊥-elim (¬just≡nothing h≡)
head-tail-cong (2ᵇ xs) (1ᵇ ys) h≡ t≡ = ⊥-elim (subst (bool ⊤ ⊥) (just-inj h≡) tt)
head-tail-cong (2ᵇ xs) (2ᵇ ys) h≡ t≡ = cong 2ᵇ_ t≡

div2≤ : ∀ n m → n ≤ m → div2 n ≤ m
div2≤ n m = ≤-trans (div2 n) n m (div2-≤ n)

fast-correct-helper : ∀ n w → n ≤ w → ⟦ n ⇑⟧⟨ w ⟩ ≡ ⟦ n ⇑⟧
fast-correct-helper zero    w       p = refl
fast-correct-helper (suc n) (suc w) p =
    head-tail-cong _ (inc ⟦ n ⇑⟧)
      (lemma₁ (even n) ⟦ div2 n ⇑⟧⟨ w ⟩ ∙ sym (head𝔹-homo n))
      (lemma₂ (even n) ⟦ div2 n ⇑⟧⟨ w ⟩ ∙ fast-correct-helper (div2 n) w (div2≤ n w (p≤p n w p)) ∙ sym (tail-homo n))
  where
  lemma₁ : ∀ x xs → head𝔹 (if x then 1ᵇ xs else 2ᵇ xs) ≡ just x
  lemma₁ false xs = refl
  lemma₁ true  xs = refl

  lemma₂ : ∀ x xs → tail𝔹 (if x then 1ᵇ xs else 2ᵇ xs) ≡ xs
  lemma₂ false xs = refl
  lemma₂ true xs  = refl

fast-correct : ∀ n → F.⟦ n ⇑⟧ ≡ ⟦ n ⇑⟧
fast-correct n = fast-correct-helper n n (≤-refl n)
