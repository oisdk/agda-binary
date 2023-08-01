{-# OPTIONS --cubical #-}

module Data.Binary.Testing where

open import Data.Binary.Increment
open import Data.Binary.Definition
open import Agda.Builtin.List
open import Data.Binary.Helpers
open import Agda.Builtin.Strict

force : 𝔹 → 𝔹
force 0ᵇ = 0ᵇ
force (1ᵇ xs) = primForce (force xs) 1ᵇ_
force (2ᵇ xs) = primForce (force xs) 2ᵇ_

inc′ : 𝔹 → 𝔹
inc′ 0ᵇ = 1ᵇ 0ᵇ
inc′ (1ᵇ xs) = 2ᵇ xs
inc′ (2ᵇ xs) = primForce (inc′ xs) 1ᵇ_

up-to : ℕ → List 𝔹
up-to = go 0ᵇ
  where
  go : 𝔹 → ℕ → List 𝔹
  go i zero    = []
  go i (suc n) = primForce i λ i → i ∷ go (inc′ i) n

up-to′ : ℕ → List ℕ
up-to′ = go zero
  where
  go : ℕ → ℕ → List ℕ
  go i zero = []
  go i (suc n) = i ∷ go (suc i) n

module _ {A : Set} (f : A → A → A) where
  comb′ : A → List A → List A → List A
  comb′ x []       zs = zs
  comb′ x (y ∷ ys) zs = f x y ∷ comb′ x ys zs

  comb : List A → List A → List A
  comb []       ys = []
  comb (x ∷ xs) ys = comb′ x ys (comb xs ys)

forces : List 𝔹 → List 𝔹
forces [] = []
forces (x ∷ xs) = primForce (force x) λ x′ → primForce (forces xs) λ xs′ → x′ ∷ xs′

open import Data.Binary.Conversion.Fast
open import Data.Binary.Properties.Helpers using (_≡_; refl) public

perf-test : (𝔹 → 𝔹 → 𝔹) → ℕ → Set
perf-test f n = comb f (up-to n) (up-to n) ≡ forces (comb f (up-to n) (up-to n))

map : {A B : Set} → (A → B) → List A → List B
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs

test : (𝔹 → 𝔹 → 𝔹) → (ℕ → ℕ → ℕ) → ℕ → Set
test f g n =
  let xs = comb f (up-to n) (up-to n)
      ys = comb g (up-to′ n) (up-to′ n)
  in xs ≡ forces (map ⟦_⇑⟧ ys)
