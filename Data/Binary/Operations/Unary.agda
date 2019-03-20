{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Unary where

open import Data.Binary.Definitions
open import Data.Nat as ℕ using (ℕ; suc; zero)

inc₁ : ℕ → 𝔹₁ → 𝔹₁
inc₁ zero    xs = suc₁ xs
inc₁ (suc y) xs = 0 1& 0< y 0& xs

inc≤ : 0≤ 𝔹₀ → 𝔹₁
inc≤ 0₂ = 0 1& 0₂
inc≤ (0< xs) = inc₁ (H₀ xs) (T₀ xs)

inc₀ : ℕ → 𝔹₁ → 𝔹₁
inc₀ zero    xs = suc₁ xs
inc₀ (suc x) xs = 0 1& 0< x 0& xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0₂         = B₁ 0 1& 0₂
inc⁺ (0< B₀ xs) = B₁ (inc₀ (H₀ xs) (T₀ xs))
inc⁺ (0< B₁ xs) = B₀ (H₁ xs 0& inc≤ (T₁ xs))

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
