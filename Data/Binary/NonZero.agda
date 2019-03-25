{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero where

open import Data.Binary.NonZero.Definitions using (𝔹) public
open import Data.Binary.NonZero.Operations.Semantics using (⟦_⇑⟧; ⟦_⇓⟧) public
open import Data.Binary.NonZero.Operations.Addition using (_+_) public
open import Data.Binary.NonZero.Operations.Multiplication using (_*_) public
open import Data.Binary.NonZero.Operations.Unary using (inc; dec) public
