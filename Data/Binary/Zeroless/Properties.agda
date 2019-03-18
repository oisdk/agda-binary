{-# OPTIONS --without-K --safe #-}

module Data.Binary.Zeroless.Properties where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; [])
open import Data.Product
open import Function
open import Data.Binary.Zeroless
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

inc-dec : ∀ x → dec (Inc.inc′ x) ≡ x
inc-dec [] = refl
inc-dec (suc x ∷ xs) = refl
inc-dec (zero ∷ xs) =
  let y , ys = Inc.inc′ xs in
  begin
    dec (Inc.inc′ (0 ∷ xs))
  ≡⟨⟩
    dec (Inc.inc″ 0 xs)
  ≡⟨⟩
    dec (map₁ suc (Inc.inc′ xs))
  ≡⟨⟩
    dec (map₁ suc (y , ys))
  ≡⟨⟩
    dec (suc y , ys)
  ≡⟨⟩
    0 ∷ dec (y , ys)
  ≡⟨⟩
    0 ∷ dec (Inc.inc′ xs)
  ≡⟨ cong (0 ∷_) (inc-dec xs) ⟩
    0 ∷ xs
  ∎

