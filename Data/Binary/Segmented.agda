{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented where

open import Data.Binary.Segmented.Definitions               using (𝔹) public
open import Data.Binary.Segmented.Operations.Addition       using (_+_) public
open import Data.Binary.Segmented.Operations.Multiplication using (_*_) public
open import Data.Binary.Segmented.Operations.Semantics      using (⟦_⇓⟧; ⟦_⇑⟧) public
open import Data.Binary.Segmented.Operations.Unary          using (inc; dec) public
