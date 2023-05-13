{-# OPTIONS --cubical #-}

module Data.Binary.Properties where

open import Data.Binary.Properties.Addition public
  using (+-cong)
open import Data.Binary.Properties.Multiplication public
  using (*-cong)
open import Data.Binary.Properties.Subtraction public
  using (-‿cong)
open import Data.Binary.Properties.Conversion public
  using (fast-correct)
open import Data.Binary.Properties.Isomorphism public
  using (𝔹⇔ℕ; 𝔹-rightInv; 𝔹-leftInv)
