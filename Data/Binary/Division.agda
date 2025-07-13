module Data.Binary.Division where

open import Data.Binary.Definition
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ

-- integer division on natural numbers
-- dividing by zero yields zero

div : ℕ.Nat → ℕ.Nat → ℕ.Nat
div n ℕ.zero    = ℕ.zero
div n (ℕ.suc m) = ℕ.div-helper ℕ.zero m n m

infixl 7 _÷_
_÷_ : 𝔹 → 𝔹 → 𝔹
xs ÷ ys = ⟦ div ⟦ xs ⇓⟧ ⟦ ys ⇓⟧ ⇑⟧

