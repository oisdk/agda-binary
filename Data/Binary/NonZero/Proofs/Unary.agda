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
inc⁺⁺-homo 1⁺ = refl
inc⁺⁺-homo (0⁺∷ xs) = refl
inc⁺⁺-homo (1⁺∷ xs) =
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

data IncView : 𝔹 → Set where
  𝔹zero : IncView 0ᵇ
  𝔹suc  : ∀ xs → IncView xs → IncView (inc xs)

open import Data.Product

⟦x⇓⟧⁺≡suc : ∀ x → ∃[ n ] (⟦ x ⇓⟧⁺ ≡ suc n)
⟦x⇓⟧⁺≡suc 1⁺ = 0 , refl
⟦x⇓⟧⁺≡suc (1⁺∷ x) = 2* ⟦ x ⇓⟧⁺ , refl
⟦x⇓⟧⁺≡suc (0⁺∷ x) with ⟦x⇓⟧⁺≡suc x
⟦x⇓⟧⁺≡suc (0⁺∷ x) | fst , snd = suc (2* fst) , (cong 2*_ snd ⟨ trans ⟩ (ℕ.+-suc (suc fst) _))

⟦x⇓⟧⁺≢0 : ∀ x → ⟦ x ⇓⟧⁺ ≢ 0
⟦x⇓⟧⁺≢0 x x≡0 with ⟦x⇓⟧⁺≡suc x
⟦x⇓⟧⁺≢0 x x≡0 | _ , prf with sym x≡0 ⟨ trans ⟩ prf
⟦x⇓⟧⁺≢0 x x≡0 | _ , prf | ()

open import Data.Empty

inc-dec : ∀ xs → inc⁺ (dec⁺ xs) ≡ xs
inc-dec 1⁺ = refl
inc-dec (1⁺∷ xs) = refl
inc-dec (0⁺∷ xs) with inc-dec xs | dec⁺ xs | inspect dec⁺ xs
inc-dec (0⁺∷ xs) | prf | 0ᵇ | [ prf₂ ] = cong 0⁺∷_ (sym (cong inc⁺ prf₂) ⟨ trans ⟩ prf)
inc-dec (0⁺∷ xs) | prf | 0< x | [ prf₂ ] = cong 0⁺∷_ (sym (cong inc⁺ prf₂) ⟨ trans ⟩ prf)

inc-view : ∀ xs → IncView xs
inc-view xs = go _ xs (inspect ⟦_⇓⟧ xs)
  where
  go : ∀ n xs → Reveal ⟦_⇓⟧ · xs is n → IncView xs
  go n 0ᵇ p = 𝔹zero
  go zero (0< x) [ p ] = ⊥-elim (⟦x⇓⟧⁺≢0 x p)
  go (suc n) (0< xs) [ p ] = subst IncView (cong 0<_ (inc-dec xs)) (𝔹suc (dec⁺ xs) (go n (dec⁺ xs) [ ℕ.suc-injective (sym (inc-homo (dec⁺ xs)) ⟨ trans ⟩ (cong ⟦_⇓⟧⁺ (inc-dec xs) ⟨ trans ⟩ p)) ]))
