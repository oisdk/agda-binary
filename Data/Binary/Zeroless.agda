{-# OPTIONS --without-K --safe #-}

module Data.Binary.Zeroless where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; [])
open import Data.Product
open import Function

Bits : Set
Bits = List ℕ

Bits⁺ : Set
Bits⁺ = ℕ × Bits

inc : Bits → Bits
inc = uncurry _∷_ ∘ inc′
  module Inc where
  mutual
    inc′ : Bits → Bits⁺
    inc′ [] = 0 , []
    inc′ (x ∷ xs) = inc″ x xs

    inc″ : ℕ → Bits → Bits⁺
    inc″ zero ns = map₁ suc (inc′ ns)
    inc″ (suc n) ns = 0 , n ∷ ns

binFromNat : ℕ → Bits
binFromNat zero = []
binFromNat (suc n) = inc (binFromNat n)

toNat : Bits → ℕ
toNat = List.foldr (λ x xs → 2 ℕ.^ x ℕ.* (1 ℕ.+ 2 ℕ.* xs)) 0

_*2 : Bits → Bits
[] *2 = []
(x ∷ xs) *2 = suc x ∷ xs

dec : Bits⁺ → Bits
dec (x , xs) = List.replicate x 0 List.++ (xs *2)


