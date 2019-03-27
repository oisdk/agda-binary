{-# OPTIONS --without-K --safe #-}

module Data.Binary.NonZero.Proofs.Semantics where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.NonZero.Operations.Unary
open import Data.Binary.NonZero.Proofs.Unary
open import Data.Binary.NonZero.Definitions
open import Data.Binary.NonZero.Operations.Semantics
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality.FasterReasoning
import Data.Nat.Properties as ℕ
open import Function

homo : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
homo zero = refl
homo (suc n) = inc-homo ⟦ n ⇑⟧ ⟨ trans ⟩ cong suc (homo n)


inj : ∀ {x y} → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
inj {x} {y} = go (inc-view x) (inc-view y)
  where
  go : ∀ {x y} → IncView x → IncView y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
  go {x} {y} x′ y′ ⟦x⇓⟧≡⟦y⇓⟧ with ⟦ x ⇓⟧ | ⟦ y ⇓⟧ | inspect ⟦_⇓⟧ x | inspect ⟦_⇓⟧ y
  go 𝔹zero 𝔹zero ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] = refl
  go (𝔹suc x′ xs′) 𝔹zero ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo x′) ⟨ trans ⟩ x≡ ⟨ trans ⟩ ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym y≡
  go {_} {.0ᵇ} (𝔹suc x′ xs′) 𝔹zero ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | ()
  go 𝔹zero (𝔹suc y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo y′) ⟨ trans ⟩ y≡ ⟨ trans ⟩ sym ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym x≡
  go {.0ᵇ} {.(0< _)} 𝔹zero (𝔹suc y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | ()
  go (𝔹suc x′ xs′) (𝔹suc y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo x′) ⟨ trans ⟩ x≡ ⟨ trans ⟩ ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym (sym (inc-homo y′) ⟨ trans ⟩ y≡)
  go (𝔹suc x′ xs′) (𝔹suc y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | x′≡y′ = cong inc (go xs′ ys′ (ℕ.suc-injective x′≡y′))

open import Function.Bijection

𝔹↔ℕ : 𝔹 ⤖ ℕ
𝔹↔ℕ = bijection ⟦_⇓⟧ ⟦_⇑⟧ inj homo
