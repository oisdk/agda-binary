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

data IncView : 𝔹 → Set where
  𝔹zero : IncView 0ᵇ
  𝔹suc  : ∀ xs → IncView xs → IncView (inc xs)

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

inc-view : ∀ xs → IncView xs
inc-view xs = go _ xs (inspect ⟦_⇓⟧ xs)
  where
  go : ∀ n xs → Reveal ⟦_⇓⟧ · xs is n → IncView xs
  go n 0ᵇ p = 𝔹zero
  go zero (0< x) [ p ] = ⊥-elim (⟦x⇓⟧⁺≢0 x p)
  go (suc n) (0< xs) [ p ] = subst IncView (cong 0<_ (inc-dec xs)) (𝔹suc (dec⁺ xs) (go n (dec⁺ xs) [ ℕ.suc-injective (sym (inc-homo (dec⁺ xs)) ⟨ trans ⟩ (cong ⟦_⇓⟧⁺ (inc-dec xs) ⟨ trans ⟩ p)) ]))

data NatView : 𝔹 → ℕ → Set where
  ℕzero : NatView 0ᵇ 0
  ℕsuc : ∀ {n xs} → NatView xs n → NatView (inc xs) (suc n)

nat-view : ∀ xs → NatView xs ⟦ xs ⇓⟧
nat-view xs = go _ xs refl
  where
  go : ∀ n xs → ⟦ xs ⇓⟧ ≡ n → NatView xs n
  go .0 0ᵇ refl = ℕzero
  go zero (0< xs) eq = ⊥-elim (⟦x⇓⟧⁺≢0 xs eq)
  go (suc n) (0< xs) eq with ℕ.suc-injective (sym (inc-homo (dec⁺ xs)) ⟨ trans ⟩ cong ⟦_⇓⟧⁺ (inc-dec xs) ⟨ trans ⟩ eq)
  go (suc n) (0< xs) eq | decr with go n (dec⁺ xs) decr
  go (suc n) (0< xs) eq | decr | ys = subst (flip NatView (suc n)) (cong 0<_ (inc-dec xs)) (ℕsuc ys)
