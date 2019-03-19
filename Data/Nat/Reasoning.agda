{-# OPTIONS --without-K --safe #-}

module Data.Nat.Reasoning where

open import Data.Nat
import Data.Nat.Properties as ℕ-Prop
open import Relation.Binary.PropositionalEquality

infixr 3 _*≫_ _≪*_ _+≫_ _≪+_
_*≫_ : ∀ {x y} z → x ≡ y → z * x ≡ z * y
_*≫_ _ = cong _

_+≫_ : ∀ {x y} z → x ≡ y → z + x ≡ z + y
_+≫_ _ = cong _

_≪*_ : ∀ {x y} z → x ≡ y → x * z ≡ y * z
_≪*_ _ = cong _

_≪+_ : ∀ {x y} z → x ≡ y → x + z ≡ y + z
_≪+_ _ = cong _
