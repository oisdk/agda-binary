{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product as Product using (_×_; _,_)
open import Function

data 0≤_ (A : Set) : Set where
  0₂ : 0≤ A
  0<_ : A → 0≤ A

infixr 5 _0&_ _1&_ B₀_ B₁_ 0<_
mutual
  record 𝔹₀ : Set where
    constructor _0&_
    inductive
    field
      zeroes : ℕ
      tail₁ : 𝔹₁

  record 𝔹₁ : Set where
    constructor _1&_
    inductive
    field
      ones : ℕ
      tail₀ : 0≤  𝔹₀

  data 𝔹⁺ : Set where
    B₀_ : 𝔹₀ → 𝔹⁺
    B₁_ : 𝔹₁ → 𝔹⁺

  𝔹 : Set
  𝔹 = 0≤ 𝔹⁺

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0₂                               =      B₁ 0     1& 0₂
inc⁺ (0< B₀ zero  0& y 1& xs        ) =      B₁ suc y 1& xs
inc⁺ (0< B₀ suc x 0& y 1& xs        ) =      B₁ 0     1& 0< x 0& y 1& xs
inc⁺ (0< B₁ x 1& 0₂                 ) = B₀ x 0& 0     1& 0₂
inc⁺ (0< B₁ x 1& 0< zero  0& z 1& xs) = B₀ x 0& suc z 1& xs
inc⁺ (0< B₁ x 1& 0< suc y 0& z 1& xs) = B₀ x 0& 0     1& 0< y 0& z 1& xs

inc : 𝔹 → 𝔹
inc x = 0< inc⁺ x

dec⁺ : 𝔹⁺ → 𝔹
dec⁺ (     B₁ zero  1& 0₂)         = 0₂
dec⁺ (     B₁ zero  1& 0< x 0& xs) = 0< B₀ suc x 0& xs
dec⁺ (     B₁ suc y 1& xs)         = 0< B₀ 0     0& y 1& xs
dec⁺ (B₀ x 0& zero  1& 0₂)         = 0<          B₁ x 1& 0₂
dec⁺ (B₀ x 0& zero  1& 0< y 0& xs) = 0<          B₁ x 1& 0< suc y  0& xs
dec⁺ (B₀ x 0& suc y 1& xs)         = 0<          B₁ x 1& 0< 0 0& y 1& xs

dec : 𝔹 → 𝔹
dec 0₂ = 0₂
dec (0< x) = dec⁺ x

⟦_⇑⟧ : ℕ → 𝔹
⟦ zero  ⇑⟧ = 0₂
⟦ suc n ⇑⟧ = inc ⟦ n ⇑⟧

mutual
  ⟦_⇓⟧≤ : 0≤ 𝔹₀ → ℕ
  ⟦ 0₂ ⇓⟧≤ = 0
  ⟦ 0< xs ⇓⟧≤ = ⟦ xs ⇓⟧₀

  ⟦_⇓⟧₁⁺¹ : 𝔹₁ → ℕ
  ⟦ x 1& xs ⇓⟧₁⁺¹ = 2 ℕ.^ suc x ℕ.* suc ⟦ xs ⇓⟧≤

  ⟦_⇓⟧₀ : 𝔹₀ → ℕ
  ⟦ x 0& xs ⇓⟧₀ = 2 ℕ.^ suc x ℕ.* ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧⁺ : 𝔹⁺ → ℕ
⟦ B₀ xs ⇓⟧⁺ = ⟦ xs ⇓⟧₀
⟦ B₁ xs ⇓⟧⁺ = ℕ.pred ⟦ xs ⇓⟧₁⁺¹

⟦_⇓⟧ : 𝔹 → ℕ
⟦ 0₂ ⇓⟧ = 0
⟦ 0< xs ⇓⟧ = ⟦ xs ⇓⟧⁺
