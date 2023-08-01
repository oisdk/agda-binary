module Data.Binary.Helpers where

import Agda.Builtin.Nat as ℕ
open import Agda.Builtin.Nat
  using (suc; zero)
  renaming (Nat to ℕ)
  public
open import Agda.Builtin.Bool

infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

id : {A : Set} → A → A
id x = x

even : ℕ → Bool
even n = ℕ.mod-helper 0 1 n 1 ℕ.== 0

div2 : ℕ → ℕ
div2 n = ℕ.div-helper 0 1 n 1

infixr 2 if_then_else_
if_then_else_ : {A : Set} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

