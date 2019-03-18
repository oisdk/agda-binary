{-# OPTIONS --without-K --safe #-}

module Data.Binary.Segmented.Properties where

open import Relation.Binary.PropositionalEquality
open import Data.Binary.Segmented
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary
open import Function
import Data.Nat.Properties as ℕ-Prop

open import Data.Binary.Segmented.Properties.Homomorphism
open import Data.Binary.Segmented.Properties.IncDec
open import Data.Binary.Segmented.Properties.Views

homo : ∀ n → ⟦ ⟦ n ⇑⟧ ⇓⟧ ≡ n
homo zero = refl
homo (suc n) = inc-homo ⟦ n ⇑⟧ ⟨ trans ⟩ cong suc (homo n)

inj : ∀ {x y} → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
inj {x} {y} = go (suc-rec x) (suc-rec y)
  where
  go : ∀ {x y} → Suc-Rec x → Suc-Rec y → ⟦ x ⇓⟧ ≡ ⟦ y ⇓⟧ → x ≡ y
  go {x} {y} x′ y′ ⟦x⇓⟧≡⟦y⇓⟧ with ⟦ x ⇓⟧ | ⟦ y ⇓⟧ | inspect ⟦_⇓⟧ x | inspect ⟦_⇓⟧ y
  go zeroʳ zeroʳ ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] = refl
  go (sucʳ x′ xs′) zeroʳ ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo x′) ⟨ trans ⟩ x≡ ⟨ trans ⟩ ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym y≡
  go {.(0< inc⁺ x′)} {.0₂} (sucʳ x′ xs′) zeroʳ ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | ()
  go zeroʳ (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo y′) ⟨ trans ⟩ y≡ ⟨ trans ⟩ sym ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym x≡
  go {.0₂} {.(0< inc⁺ y′)} zeroʳ (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | ()
  go (sucʳ x′ xs′) (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] with sym (inc-homo x′) ⟨ trans ⟩ x≡ ⟨ trans ⟩ ⟦x⇓⟧≡⟦y⇓⟧ ⟨ trans ⟩ sym (sym (inc-homo y′) ⟨ trans ⟩ y≡)
  go (sucʳ x′ xs′) (sucʳ y′ ys′) ⟦x⇓⟧≡⟦y⇓⟧ | ⟦x⇓⟧ | ⟦y⇓⟧ | [ x≡ ] | [ y≡ ] | x′≡y′ = cong inc (go xs′ ys′ (ℕ-Prop.suc-injective x′≡y′))

open import Function.Bijection

𝔹↔ℕ : 𝔹 ⤖ ℕ
𝔹↔ℕ = bijection ⟦_⇓⟧ ⟦_⇑⟧ inj homo

inc-injective : ∀ x y → inc x ≡ inc y → x ≡ y
inc-injective x y x+1≡y+1 = inj (ℕ-Prop.suc-injective (sym (inc-homo x) ⟨ trans ⟩ cong ⟦_⇓⟧ x+1≡y+1 ⟨ trans ⟩ inc-homo y))

homo⁻¹ : ∀ x → ⟦ ⟦ x ⇓⟧ ⇑⟧ ≡ x
homo⁻¹ = Bijection.left-inverse-of 𝔹↔ℕ

