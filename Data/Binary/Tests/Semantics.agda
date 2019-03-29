module Data.Binary.Tests.Semantics where

open import Data.Binary.Definitions
open import Data.Binary.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality

prop : ℕ → Set
prop n = let xs = List.upTo n in List.map (λ x → ⟦ ⟦ x ⇑⟧ ⇓⟧ ) xs ≡ xs

_ : prop 50
_ = refl

