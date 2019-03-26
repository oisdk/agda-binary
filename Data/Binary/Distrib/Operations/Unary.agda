{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Operations.Unary where

open import Data.Binary.Distrib.Definitions

inc : 𝔹 → 𝔹
inc 0ᵇ = s2* 0ᵇ
inc (2*s x) = s2* inc x
inc (s2* x) = 2*s x
