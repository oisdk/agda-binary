{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Subtraction where

open import Data.Binary.Definition
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ

open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Properties.Double
open import Data.Binary.Subtraction

data ℕ± : Set where
  negⁿ  : ℕ±
  -1ⁿ   : ℕ±
  +ⁿ[_] : ℕ → ℕ±

infixl 6 _⊖_
_⊖_ : ℕ → ℕ → ℕ±
n     ⊖ zero        = +ⁿ[ n ]
zero  ⊖ suc zero    = -1ⁿ
zero  ⊖ suc (suc _) = negⁿ
suc n ⊖ suc m       = n ⊖ m

⟦_⇓⟧± : 𝔹± → ℕ±
⟦ neg   ⇓⟧± = negⁿ
⟦ -1ᵇ   ⇓⟧± = -1ⁿ
⟦ +[ x ] ⇓⟧± = +ⁿ[ ⟦ x ⇓⟧ ]

absⁿ : ℕ± → ℕ
absⁿ negⁿ    = 0
absⁿ -1ⁿ     = 0
absⁿ +ⁿ[ n ] = n

infixr 8 1ᵇⁿ_ 2ᵇⁿ_

1ᵇⁿ_ : ℕ± → ℕ±
1ᵇⁿ negⁿ    = negⁿ
1ᵇⁿ -1ⁿ     = -1ⁿ
1ᵇⁿ +ⁿ[ n ] = +ⁿ[ suc (n ℕ.* 2) ]

2ᵇⁿ_ : ℕ± → ℕ±
2ᵇⁿ negⁿ    = negⁿ
2ᵇⁿ -1ⁿ     = +ⁿ[ 0 ]
2ᵇⁿ +ⁿ[ n ] = +ⁿ[ suc (suc (n ℕ.* 2)) ]

1ᵇ±-cong : ∀ x → ⟦ 1ᵇ± x ⇓⟧± ≡ 1ᵇⁿ ⟦ x ⇓⟧±
1ᵇ±-cong neg    = refl
1ᵇ±-cong -1ᵇ    = refl
1ᵇ±-cong +[ _ ] = refl

2ᵇ±-cong : ∀ x → ⟦ 2ᵇ± x ⇓⟧± ≡ 2ᵇⁿ ⟦ x ⇓⟧±
2ᵇ±-cong neg    = refl
2ᵇ±-cong -1ᵇ    = refl
2ᵇ±-cong +[ _ ] = refl

dec±-cong : ∀ xs → ⟦ dec± xs ⇓⟧± ≡ ⟦ xs ⇓⟧ ⊖ 1
dec±-cong 0ᵇ      = refl
dec±-cong (1ᵇ xs) = cong +ⁿ[_] (double-cong xs)
dec±-cong (2ᵇ xs) = refl

1ᵇ-⊖ : ∀ x z → 1ᵇⁿ (x ⊖ z) ≡ suc (x ℕ.* 2) ⊖ (z ℕ.* 2)
1ᵇ-⊖ x       zero          = refl
1ᵇ-⊖ zero    (suc zero)    = refl
1ᵇ-⊖ zero    (suc (suc z)) = refl
1ᵇ-⊖ (suc x) (suc z)       = 1ᵇ-⊖ x z

2ᵇ-⊖ : ∀ x z → 2ᵇⁿ (x ⊖ suc z) ≡ (x ℕ.* 2) ⊖ (z ℕ.* 2)
2ᵇ-⊖ zero    zero    = refl
2ᵇ-⊖ zero    (suc z) = refl
2ᵇ-⊖ (suc x) zero    = refl
2ᵇ-⊖ (suc x) (suc z) = 2ᵇ-⊖ x z

sub-cong  : ∀ xs ys → ⟦ sub  xs ys ⇓⟧± ≡ ⟦ xs ⇓⟧ ⊖ ⟦ ys ⇓⟧
sub₁-cong : ∀ xs ys → ⟦ sub₁ xs ys ⇓⟧± ≡ ⟦ xs ⇓⟧ ⊖ suc ⟦ ys ⇓⟧
sub₂-cong : ∀ xs ys → ⟦ sub₂ xs ys ⇓⟧± ≡ ⟦ xs ⇓⟧ ⊖ suc (suc ⟦ ys ⇓⟧)

sub-cong _       0ᵇ           = refl
sub-cong 0ᵇ      (1ᵇ 0ᵇ)      = refl
sub-cong 0ᵇ      (1ᵇ (1ᵇ _))  = refl
sub-cong 0ᵇ      (1ᵇ (2ᵇ _))  = refl
sub-cong 0ᵇ      (2ᵇ _)       = refl
sub-cong (1ᵇ xs) (1ᵇ ys) = 2ᵇ±-cong (sub₁ xs ys) ∙ cong 2ᵇⁿ_ (sub₁-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (2ᵇ xs) (2ᵇ ys) = 2ᵇ±-cong (sub₁ xs ys) ∙ cong 2ᵇⁿ_ (sub₁-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (2ᵇ xs) (1ᵇ ys) = 1ᵇ±-cong (sub  xs ys) ∙ cong 1ᵇⁿ_ (sub-cong  xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (1ᵇ xs) (2ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys) ∙ cong 1ᵇⁿ_ (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)

sub₁-cong xs      0ᵇ      = dec±-cong xs
sub₁-cong 0ᵇ      (1ᵇ _)  = refl
sub₁-cong 0ᵇ      (2ᵇ _)  = refl
sub₁-cong (1ᵇ xs) (1ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys) ∙ cong 1ᵇⁿ_ (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₁-cong (2ᵇ xs) (2ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys) ∙ cong 1ᵇⁿ_ (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₁-cong (2ᵇ xs) (1ᵇ ys) = 2ᵇ±-cong (sub₁ xs ys) ∙ cong 2ᵇⁿ_ (sub₁-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub₁-cong (1ᵇ xs) (2ᵇ ys) = 2ᵇ±-cong (sub₂ xs ys) ∙ cong 2ᵇⁿ_ (sub₂-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)

sub₂-cong 0ᵇ      _       = refl
sub₂-cong (1ᵇ xs) 0ᵇ      = 1ᵇ±-cong (dec± xs)   ∙ cong 1ᵇⁿ_ (dec±-cong xs)   ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ 1
sub₂-cong (2ᵇ xs) 0ᵇ      = 2ᵇ±-cong (dec± xs)   ∙ cong 2ᵇⁿ_ (dec±-cong xs)   ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ 0
sub₂-cong (1ᵇ xs) (1ᵇ ys) = 2ᵇ±-cong (sub₂ xs ys) ∙ cong 2ᵇⁿ_ (sub₂-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₂-cong (2ᵇ xs) (2ᵇ ys) = 2ᵇ±-cong (sub₂ xs ys) ∙ cong 2ᵇⁿ_ (sub₂-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₂-cong (2ᵇ xs) (1ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys) ∙ cong 1ᵇⁿ_ (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₂-cong (1ᵇ xs) (2ᵇ ys) = 1ᵇ±-cong (sub₂ xs ys) ∙ cong 1ᵇⁿ_ (sub₂-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc (suc ⟦ ys ⇓⟧))

abs-cong : ∀ x → ⟦ abs x ⇓⟧ ≡ absⁿ ⟦ x ⇓⟧±
abs-cong neg    = refl
abs-cong -1ᵇ    = refl
abs-cong +[ _ ] = refl

⊖-cong : ∀ n m → absⁿ (n ⊖ m) ≡ n ℕ.- m
⊖-cong n       zero          = refl
⊖-cong zero    (suc zero)    = refl
⊖-cong zero    (suc (suc m)) = refl
⊖-cong (suc n) (suc m)       = ⊖-cong n m

-‿cong : ∀ xs ys → ⟦ xs - ys ⇓⟧ ≡ ⟦ xs ⇓⟧ ℕ.- ⟦ ys ⇓⟧
-‿cong xs ys = abs-cong (sub xs ys) ∙ cong absⁿ (sub-cong xs ys) ∙ ⊖-cong ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
