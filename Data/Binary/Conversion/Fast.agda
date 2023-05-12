module Data.Binary.Conversion.Fast where

-- This module provides a conversion function from
-- nats which uses built-in functions.
-- It is dramatically faster than the normal conversion
-- even at smaller numbers.

open import Data.Binary.Definition
open import Data.Binary.Helpers

⟦_⇑⟧⟨_⟩ : ℕ → ℕ → 𝔹
⟦ suc n ⇑⟧⟨ suc w ⟩ =
  if even n
    then 1ᵇ ⟦ div2 n ⇑⟧⟨ w ⟩
    else 2ᵇ ⟦ div2 n ⇑⟧⟨ w ⟩
⟦ zero  ⇑⟧⟨ _    ⟩ = 0ᵇ
⟦ suc _ ⇑⟧⟨ zero ⟩ = 0ᵇ -- will not happen

-- We build the output by repeatedly halving the input,
-- but we also pass in the number to reduce as we go so that
-- we satisfy the termination checker.
⟦_⇑⟧ : ℕ → 𝔹
⟦ n ⇑⟧ = ⟦ n ⇑⟧⟨ n ⟩
{-# INLINE ⟦_⇑⟧ #-}
