{-# OPTIONS --without-K --safe #-}

module Data.Binary.Conversion.Fast where

-- This module provides a conversion function from
-- nats which uses built-in functions.
-- It is dramatically faster than the normal conversion
-- even at smaller numbers.

open import Data.Binary.Definition
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

even : Nat → Bool
even n = mod-helper 0 1 n 1 == 0

div2 : Nat → Nat
div2 n = div-helper 0 1 n 1

infixr 2 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

⟦_⇑⟧⟨_⟩ : Nat → Nat → 𝔹
⟦ suc n ⇑⟧⟨ suc w ⟩ =
  if even n
    then 1ᵇ ⟦ div2 n ⇑⟧⟨ w ⟩
    else 2ᵇ ⟦ div2 n ⇑⟧⟨ w ⟩
⟦ zero  ⇑⟧⟨ _    ⟩ = 0ᵇ
⟦ suc _ ⇑⟧⟨ zero ⟩ = 0ᵇ -- will not happen

-- We build the output by repeatedly halving the input,
-- but we also pass in the number to reduce as we go so that
-- we satisfy the termination checker.
⟦_⇑⟧ : Nat → 𝔹
⟦ n ⇑⟧ = ⟦ n ⇑⟧⟨ n ⟩
{-# INLINE ⟦_⇑⟧ #-}

