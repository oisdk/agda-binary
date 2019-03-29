{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Tests.Subtraction where

open import Data.List as List using (List; _∷_; [])
open import Data.Product
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics as Pos using (⟦_⇓⟧⁺)
open import Relation.Binary.PropositionalEquality
open import Data.Maybe as Maybe using (Maybe; just; nothing)

ℤ : Set
ℤ = Bit × ℕ

⟦_⇓⟧ : 𝔹± → ℤ
⟦ 0< (O , snd) ⇓⟧ = O , ⟦ snd ⇓⟧⁺
⟦ 0< (I , snd) ⇓⟧ = I , ℕ.pred ⟦ snd ⇓⟧⁺
⟦ 0ᵇ ⇓⟧ = O , 0

- : ℕ → ℤ
- zero = O , zero
- (suc snd) = I , snd

+⇑ : ℕ → ℤ
+⇑ = O ,_

⟦_⇑⟧ : ℤ → 𝔹±
⟦ O , snd ⇑⟧ = Maybe.map (O ,_) Pos.⟦ snd ⇑⟧
⟦ I , snd ⇑⟧ = Maybe.map (I ,_) Pos.⟦ suc snd ⇑⟧

-- _≡⌈_⌉≡_ : (𝔹 → 𝔹) → ℕ → (ℕ → ℕ) → Set
-- fᵇ ≡⌈ n ⌉≡ fⁿ = let xs = List.upTo n in List.map (λ x → ⟦ fᵇ ⟦ x ⇑⟧ ⇓⟧ ) xs ≡ List.map fⁿ xs


prod : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
prod [] ys = []
prod (x ∷ xs) ys = List.foldr (λ y ys → (x , y) ∷ ys) (prod xs ys) ys

_≡⌈_⌉₂≡_ : (𝔹± → 𝔹± → 𝔹±) → ℕ → (ℤ → ℤ → ℤ) → Set
fᵇ ≡⌈ n ⌉₂≡ fⁿ = List.map (λ { (x , y) → ⟦ fᵇ ⟦ x ⇑⟧ ⟦ y ⇑⟧ ⇓⟧ }) zs ≡ List.map (uncurry fⁿ) zs
  where
  xs : List ℕ
  xs = List.upTo n
  ys = List.map (I ,_) xs List.++ List.map (O ,_) xs
  zs = prod ys ys

_ℤ-_ : ℕ → ℕ → ℤ
x ℤ- y with y ℕ.<ᵇ x
(x ℤ- y) | I = O , (x ℕ.∸ suc y)
(x ℤ- y) | O = I , (y ℕ.∸ x)

_z+_ : ℤ → ℤ → ℤ
(O , x) z+ (O , y) = O , (x ℕ.+ y)
(O , x) z+ (I , y) = x ℤ- y
(I , x) z+ (O , y) = y ℤ- x
(I , x) z+ (I , y) = I , (suc x ℕ.+ y)


{-# DISPLAY _,_ I xn = - (suc xn) #-}
{-# DISPLAY _,_ O xn = +⇑ xn #-}

open import Data.Binary.NonZero.Operations.Subtraction

-- _ : ⟦ ⟦ (- 3) ⇑⟧ + ⟦ +⇑ 2 ⇑⟧ ⇓⟧ ≡ (- 1)
-- _ = refl

-- _ : _+_ ≡⌈ 3 ⌉₂≡ _z+_
-- _ = refl
