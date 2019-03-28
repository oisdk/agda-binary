{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Proofs.Unary where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.NonZero.Operations.Unary
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function

inc⁺⁺-homo : ∀ xs → ⟦ inc⁺⁺ xs ⇓⟧⁺ ≡ suc ⟦ xs ⇓⟧⁺
inc⁺⁺-homo 1ᵇ = refl
inc⁺⁺-homo (O ∷ xs) = refl
inc⁺⁺-homo (I ∷ xs) =
  begin
    2* ⟦ inc⁺⁺ xs ⇓⟧⁺
  ≡⟨ cong 2*_ (inc⁺⁺-homo xs) ⟩
    2* (suc ⟦ xs ⇓⟧⁺)
  ≡⟨⟩
    (suc ⟦ xs ⇓⟧⁺) ℕ.+ suc ⟦ xs ⇓⟧⁺
  ≡⟨ ℕ.+-suc (suc ⟦ xs ⇓⟧⁺) ⟦ xs ⇓⟧⁺ ⟩
    suc (suc (2* ⟦ xs ⇓⟧⁺))
  ∎

inc-homo : ∀ x → ⟦ inc x ⇓⟧ ≡ suc ⟦ x ⇓⟧
inc-homo 0ᵇ = refl
inc-homo (0< xs) = inc⁺⁺-homo xs

open import Data.Product

⟦x⇓⟧⁺≡suc : ∀ x → ∃[ n ] (⟦ x ⇓⟧⁺ ≡ suc n)
⟦x⇓⟧⁺≡suc 1ᵇ = 0 , refl
⟦x⇓⟧⁺≡suc (I ∷ x) = 2* ⟦ x ⇓⟧⁺ , refl
⟦x⇓⟧⁺≡suc (O ∷ x) with ⟦x⇓⟧⁺≡suc x
⟦x⇓⟧⁺≡suc (O ∷ x) | fst , snd = suc (2* fst) , (cong 2*_ snd ⟨ trans ⟩ (ℕ.+-suc (suc fst) _))

⟦x⇓⟧⁺≢0 : ∀ x → ⟦ x ⇓⟧⁺ ≢ 0
⟦x⇓⟧⁺≢0 x x≡0 with ⟦x⇓⟧⁺≡suc x
⟦x⇓⟧⁺≢0 x x≡0 | _ , prf with sym x≡0 ⟨ trans ⟩ prf
⟦x⇓⟧⁺≢0 x x≡0 | _ , prf | ()

open import Data.Empty

inc-dec⁺⁺ : ∀ x xs → inc⁺⁺ (dec⁺⁺ x xs) ≡ x ∷ xs
inc-dec⁺⁺ I xs = refl
inc-dec⁺⁺ O 1ᵇ = refl
inc-dec⁺⁺ O (x ∷ xs) = cong (O ∷_) (inc-dec⁺⁺ x xs)

inc-dec : ∀ xs → inc⁺ (dec⁺ xs) ≡ xs
inc-dec 1ᵇ = refl
inc-dec (x ∷ xs) = inc-dec⁺⁺ x xs

data IncView : 𝔹 → ℕ → Set where
  Izero : IncView 0ᵇ 0
  Isuc : ∀ {n xs ys} → inc xs ≡ ys → IncView xs n → IncView ys (suc n)

inc-view : ∀ xs → IncView xs ⟦ xs ⇓⟧
inc-view xs = go _ xs refl
  where
  go : ∀ n xs → ⟦ xs ⇓⟧ ≡ n → IncView xs n
  go .0 0ᵇ refl = Izero
  go zero (0< xs) eq = ⊥-elim (⟦x⇓⟧⁺≢0 xs eq)
  go (suc n) (0< xs) eq =
    Isuc
      (cong 0<_ (inc-dec xs))
      (go n (dec⁺ xs)
            (ℕ.suc-injective (sym (inc-homo (dec⁺ xs)) ⟨ trans ⟩ cong ⟦_⇓⟧⁺ (inc-dec xs) ⟨ trans ⟩ eq)))
