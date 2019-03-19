{-# OPTIONS --without-K --safe #-}

module Data.Binary.Operations.Unary where

open import Data.Binary.Definitions
open import Data.Nat as ℕ using (ℕ; suc; zero)

inc₁ : 0≤ 𝔹₀ → 𝔹₁
inc₁ (0₂                 ) = 0     1& 0₂
inc₁ (0< zero  0& z 1& xs) = suc z 1& xs
inc₁ (0< suc y 0& z 1& xs) = 0     1& 0< y 0& z 1& xs

inc₀ : 𝔹₀ → 𝔹₁
inc₀ (zero  0& y 1& xs) = suc y 1& xs
inc₀ (suc x 0& y 1& xs) = 0     1& 0< x 0& y 1& xs

inc⁺ : 𝔹 → 𝔹⁺
inc⁺ 0₂              = B₁ 0 1& 0₂
inc⁺ (0< B₀ xs)      = B₁ (inc₀ xs)
inc⁺ (0< B₁ x 1& xs) = B₀ (x 0& inc₁ xs)

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
