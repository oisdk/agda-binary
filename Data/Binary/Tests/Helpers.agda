{-# OPTIONS --without-K --safe #-}

module Data.Binary.Tests.Helpers where

open import Data.List as List using (List; _∷_; [])
open import Data.Product
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Binary.Definitions
open import Data.Binary.Operations.Semantics
open import Relation.Binary.PropositionalEquality

_≡⌈_⌉≡_ : (𝔹 → 𝔹) → ℕ → (ℕ → ℕ) → Set
fᵇ ≡⌈ n ⌉≡ fⁿ = let xs = List.upTo n in List.map (λ x → ⟦ fᵇ ⟦ x ⇑⟧ ⇓⟧ ) xs ≡ List.map fⁿ xs


prod : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
prod [] ys = []
prod (x ∷ xs) ys = List.foldr (λ y ys → (x , y) ∷ ys) (prod xs ys) ys

_≡⌈_⌉₂≡_ : (𝔹 → 𝔹 → 𝔹) → ℕ → (ℕ → ℕ → ℕ) → Set
fᵇ ≡⌈ n ⌉₂≡ fⁿ = List.map (λ { (x , y) → ⟦ fᵇ ⟦ x ⇑⟧ ⟦ y ⇑⟧ ⇓⟧ }) ys ≡ List.map (uncurry fⁿ) ys
  where
  xs : List ℕ
  xs = List.upTo n
  ys = prod xs xs

