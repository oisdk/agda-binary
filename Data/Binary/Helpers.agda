module Data.Binary.Helpers where

import Agda.Builtin.Nat as ℕ
open import Agda.Builtin.Nat
  using (suc; zero)
  renaming (Nat to ℕ)
  public
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe public

even : ℕ → Bool
even n = ℕ.mod-helper 0 1 n 1 ℕ.== 0

div2 : ℕ → ℕ
div2 n = ℕ.div-helper 0 1 n 1

infixr 2 if_then_else_
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if true  then t else _ = t
if false then _ else f = f

map-maybe : {A : Set} → (A → A) → Maybe A → Maybe A
map-maybe f nothing  = nothing
map-maybe f (just x) = just (f x)

from-maybe : {A : Set} → A → Maybe A → A
from-maybe x nothing  = x
from-maybe _ (just x) = x
