module Data.Binary.Bits where

open import Data.List as List using (List; _∷_; [])

data Bit : Set where O I : Bit

Bits : Set
Bits = List Bit

infix 5 O∷_
O∷_ : Bits → Bits
O∷ [] = []
O∷ xs@(_ ∷ _) = O ∷ xs

inc : Bits → Bits
inc [] = I ∷ []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs
