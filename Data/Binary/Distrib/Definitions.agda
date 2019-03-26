{-# OPTIONS --without-K --safe #-}

module Data.Binary.Distrib.Definitions where

infixr 5 2*s_ s2*_
data 𝔹 : Set where
  0ᵇ : 𝔹
  2*s_ : 𝔹 → 𝔹
  s2*_ : 𝔹 → 𝔹
