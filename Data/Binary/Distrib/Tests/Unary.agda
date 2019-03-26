{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Tests.Unary where

open import Relation.Binary.PropositionalEquality
open import Data.List as List
open import Data.Binary.Distrib.Operations.Semantics
open import Data.Nat

invol : ℕ → Set
invol n = let xs = List.upTo n in List.map (λ x → ⟦  ⟦ x ⇑⟧ ⇓⟧) xs ≡ xs

_ : invol 50
_ = refl
