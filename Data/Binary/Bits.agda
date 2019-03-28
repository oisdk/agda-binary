{-# OPTIONS --without-K --safe #-}

module Data.Binary.Bits where

open import Data.Bool as Bool using (not; _∨_; _∧_; _xor_; T) renaming (Bool to Bit; true to I; false to O) public

_xnor_ : Bit → Bit → Bit
O xnor y = not y
I xnor y = y

sumᵇ : Bit → Bit → Bit → Bit
sumᵇ O = _xor_
sumᵇ I = _xnor_

carryᵇ : Bit → Bit → Bit → Bit
carryᵇ O = _∧_
carryᵇ I = _∨_
