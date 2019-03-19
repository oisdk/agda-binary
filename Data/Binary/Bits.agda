module Data.Binary.Bits where

open import Data.List as List using (List; _∷_; [])

data Bit : Set where O I : Bit

𝔹 : Set
𝔹 = List Bit

infix 5 O∷_
O∷_ : 𝔹 → 𝔹
O∷ [] = []
O∷ xs@(_ ∷ _) = O ∷ xs

inc : 𝔹 → 𝔹
inc [] = I ∷ []
inc (O ∷ xs) = I ∷ xs
inc (I ∷ xs) = O ∷ inc xs
