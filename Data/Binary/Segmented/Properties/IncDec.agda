{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Properties.IncDec where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Segmented
open import Data.Nat as ℕ using (ℕ; suc; zero)

dec-inc : ∀ x → dec⁺ (inc⁺ x) ≡ x
dec-inc 0₂                         = refl
dec-inc (0< B₁ _ 1& 0₂           ) = refl
dec-inc (0< B₁ _ 1& 0< zero  0& _) = refl
dec-inc (0< B₁ _ 1& 0< suc _ 0& _) = refl
dec-inc (0< B₀ zero  0& _        ) = refl
dec-inc (0< B₀ suc _ 0& _        ) = refl

inc-dec : ∀ x → inc⁺ (dec⁺ x) ≡ x
inc-dec (     B₁ zero  1& 0₂  ) = refl
inc-dec (     B₁ zero  1& 0< _) = refl
inc-dec (     B₁ suc _ 1& _   ) = refl
inc-dec (B₀ _ 0& zero  1& 0₂  ) = refl
inc-dec (B₀ _ 0& zero  1& 0< _) = refl
inc-dec (B₀ _ 0& suc _ 1& _   ) = refl
