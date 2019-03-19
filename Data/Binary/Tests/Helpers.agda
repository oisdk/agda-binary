{-# OPTIONS --without-K --safe #-}

module Data.Binary.Tests.Helpers where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Semantics
open import Data.List as List
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Function
open import Data.Product

∀⟨ℕ⟩<_∶_≐_ : ℕ → (𝔹 → 𝔹) → (ℕ → ℕ) → Set
∀⟨ℕ⟩< n ∶ 𝔹f ≐ ℕf = let xs = List.upTo n in List.map (⟦_⇓⟧ ∘ 𝔹f ∘ ⟦_⇑⟧) xs ≡ List.map ℕf xs

∀⟨ℕ⟩₂<_∶_≐_ : ℕ → (𝔹 → 𝔹 → 𝔹) → (ℕ → ℕ → ℕ) → Set
∀⟨ℕ⟩₂< n ∶ 𝔹f ≐ ℕf = List.map (λ { (x , y) → ⟦ 𝔹f ⟦ x ⇑⟧ ⟦ y ⇑⟧ ⇓⟧ }) ys ≡ List.map (uncurry ℕf) ys
  where
  xs : List ℕ
  xs = List.upTo n

  ys : List (ℕ × ℕ)
  ys = List.concatMap (λ x → List.map (x ,_) xs) xs
