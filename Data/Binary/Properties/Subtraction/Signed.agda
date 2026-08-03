{-# OPTIONS --cubical --guardedness #-}

module Data.Binary.Properties.Subtraction.Signed where

open import Data.Binary.Definition
open import Data.Binary.Conversion
import Agda.Builtin.Nat as ℕ

open import Data.Binary.Helpers
open import Data.Binary.Properties.Helpers
open import Data.Binary.Properties.Double
open import Data.Binary.Subtraction.Signed

data ℤⁿ : Set where
  +ⁿ[_]   : ℕ → ℤⁿ
  -1ⁿ     : ℤⁿ
  -2ⁿ     : ℤⁿ
  -ⁿ[3+_] : ℕ → ℤⁿ

infixl 6 _⊖_
_⊖_ : ℕ → ℕ → ℤⁿ
n     ⊖ zero              = +ⁿ[ n ]
zero  ⊖ suc zero          = -1ⁿ
zero  ⊖ suc (suc zero)    = -2ⁿ
zero  ⊖ suc (suc (suc m)) = -ⁿ[3+ m ]
suc n ⊖ suc m             = n ⊖ m

⟦_⇓⟧ᶻ : ℤᵇ → ℤⁿ
⟦ +[ x ]   ⇓⟧ᶻ = +ⁿ[ ⟦ x ⇓⟧ ]
⟦ -1ᵇ      ⇓⟧ᶻ = -1ⁿ
⟦ -2ᵇ      ⇓⟧ᶻ = -2ⁿ
⟦ -[3+ x ] ⇓⟧ᶻ = -ⁿ[3+ ⟦ x ⇓⟧ ]

posⁿ : ℤⁿ → ℕ
posⁿ +ⁿ[ n ]   = n
posⁿ -1ⁿ       = 0
posⁿ -2ⁿ       = 0
posⁿ -ⁿ[3+ _ ] = 0

magⁿ : ℤⁿ → ℕ
magⁿ +ⁿ[ _ ]   = 0
magⁿ -1ⁿ       = 1
magⁿ -2ⁿ       = 2
magⁿ -ⁿ[3+ n ] = suc (suc (suc n))

⊖-pos : ∀ n m → posⁿ (n ⊖ m) ≡ n ℕ.- m
⊖-pos n       zero                = refl
⊖-pos zero    (suc zero)          = refl
⊖-pos zero    (suc (suc zero))    = refl
⊖-pos zero    (suc (suc (suc m))) = refl
⊖-pos (suc n) (suc m)             = ⊖-pos n m

⊖-mag : ∀ n m → magⁿ (n ⊖ m) ≡ m ℕ.- n
⊖-mag zero    zero                = refl
⊖-mag (suc n) zero                = refl
⊖-mag zero    (suc zero)          = refl
⊖-mag zero    (suc (suc zero))    = refl
⊖-mag zero    (suc (suc (suc m))) = refl
⊖-mag (suc n) (suc m)             = ⊖-mag n m

infixr 8 1ᵇⁿ_ 2ᵇⁿ_ 1ᵇ∓ⁿ_ 2ᵇ∓ⁿ_

1ᵇⁿ_ : ℤⁿ → ℤⁿ
1ᵇⁿ +ⁿ[ n ]   = +ⁿ[ suc (n ℕ.* 2) ]
1ᵇⁿ -1ⁿ       = -1ⁿ
1ᵇⁿ -2ⁿ       = -ⁿ[3+ 0 ]
1ᵇⁿ -ⁿ[3+ n ] = -ⁿ[3+ suc (suc (n ℕ.* 2)) ]

2ᵇⁿ_ : ℤⁿ → ℤⁿ
2ᵇⁿ +ⁿ[ n ]   = +ⁿ[ suc (suc (n ℕ.* 2)) ]
2ᵇⁿ -1ⁿ       = +ⁿ[ 0 ]
2ᵇⁿ -2ⁿ       = -2ⁿ
2ᵇⁿ -ⁿ[3+ n ] = -ⁿ[3+ suc (n ℕ.* 2) ]

1ᵇ∓ⁿ_ : ℤⁿ → ℤⁿ
1ᵇ∓ⁿ +ⁿ[ n ]   = -ⁿ[3+ suc (suc (n ℕ.* 2)) ]
1ᵇ∓ⁿ -1ⁿ       = -ⁿ[3+ 0 ]
1ᵇ∓ⁿ -2ⁿ       = -1ⁿ
1ᵇ∓ⁿ -ⁿ[3+ n ] = +ⁿ[ suc (n ℕ.* 2) ]

2ᵇ∓ⁿ_ : ℤⁿ → ℤⁿ
2ᵇ∓ⁿ +ⁿ[ n ]   = -ⁿ[3+ suc (n ℕ.* 2) ]
2ᵇ∓ⁿ -1ⁿ       = -2ⁿ
2ᵇ∓ⁿ -2ⁿ       = +ⁿ[ 0 ]
2ᵇ∓ⁿ -ⁿ[3+ n ] = +ⁿ[ suc (suc (n ℕ.* 2)) ]

1ᵇ±-cong : ∀ x → ⟦ 1ᵇ± x ⇓⟧ᶻ ≡ 1ᵇⁿ ⟦ x ⇓⟧ᶻ
1ᵇ±-cong +[ _ ]   = refl
1ᵇ±-cong -1ᵇ      = refl
1ᵇ±-cong -2ᵇ      = refl
1ᵇ±-cong -[3+ _ ] = refl

2ᵇ±-cong : ∀ x → ⟦ 2ᵇ± x ⇓⟧ᶻ ≡ 2ᵇⁿ ⟦ x ⇓⟧ᶻ
2ᵇ±-cong +[ _ ]   = refl
2ᵇ±-cong -1ᵇ      = refl
2ᵇ±-cong -2ᵇ      = refl
2ᵇ±-cong -[3+ _ ] = refl

1ᵇ∓-cong : ∀ x → ⟦ 1ᵇ∓ x ⇓⟧ᶻ ≡ 1ᵇ∓ⁿ ⟦ x ⇓⟧ᶻ
1ᵇ∓-cong +[ _ ]   = refl
1ᵇ∓-cong -1ᵇ      = refl
1ᵇ∓-cong -2ᵇ      = refl
1ᵇ∓-cong -[3+ _ ] = refl

2ᵇ∓-cong : ∀ x → ⟦ 2ᵇ∓ x ⇓⟧ᶻ ≡ 2ᵇ∓ⁿ ⟦ x ⇓⟧ᶻ
2ᵇ∓-cong +[ _ ]   = refl
2ᵇ∓-cong -1ᵇ      = refl
2ᵇ∓-cong -2ᵇ      = refl
2ᵇ∓-cong -[3+ _ ] = refl

dec±-cong : ∀ xs → ⟦ dec± xs ⇓⟧ᶻ ≡ ⟦ xs ⇓⟧ ⊖ 1
dec±-cong 0ᵇ      = refl
dec±-cong (1ᵇ xs) = cong +ⁿ[_] (double-cong xs)
dec±-cong (2ᵇ xs) = refl

1ᵇ-⊖ : ∀ x z → 1ᵇⁿ (x ⊖ z) ≡ suc (x ℕ.* 2) ⊖ (z ℕ.* 2)
1ᵇ-⊖ x       zero                = refl
1ᵇ-⊖ zero    (suc zero)          = refl
1ᵇ-⊖ zero    (suc (suc zero))    = refl
1ᵇ-⊖ zero    (suc (suc (suc z))) = refl
1ᵇ-⊖ (suc x) (suc z)             = 1ᵇ-⊖ x z

2ᵇ-⊖ : ∀ x z → 2ᵇⁿ (x ⊖ suc z) ≡ (x ℕ.* 2) ⊖ (z ℕ.* 2)
2ᵇ-⊖ zero    zero          = refl
2ᵇ-⊖ zero    (suc zero)    = refl
2ᵇ-⊖ zero    (suc (suc z)) = refl
2ᵇ-⊖ (suc x) zero          = refl
2ᵇ-⊖ (suc x) (suc z)       = 2ᵇ-⊖ x z

1ᵇ∓-⊖ : ∀ x z → 1ᵇ∓ⁿ (z ⊖ x) ≡ (x ℕ.* 2) ⊖ suc (suc (suc (suc (suc (z ℕ.* 2)))))
1ᵇ∓-⊖ zero                z       = refl
1ᵇ∓-⊖ (suc zero)          zero    = refl
1ᵇ∓-⊖ (suc (suc zero))    zero    = refl
1ᵇ∓-⊖ (suc (suc (suc x))) zero    = refl
1ᵇ∓-⊖ (suc x)             (suc z) = 1ᵇ∓-⊖ x z

2ᵇ∓-⊖ : ∀ x z → 2ᵇ∓ⁿ (z ⊖ x) ≡ (x ℕ.* 2) ⊖ suc (suc (suc (suc (z ℕ.* 2))))
2ᵇ∓-⊖ zero                z       = refl
2ᵇ∓-⊖ (suc zero)          zero    = refl
2ᵇ∓-⊖ (suc (suc zero))    zero    = refl
2ᵇ∓-⊖ (suc (suc (suc x))) zero    = refl
2ᵇ∓-⊖ (suc x)             (suc z) = 2ᵇ∓-⊖ x z

sub₁-cong : ∀ xs ys → ⟦ sub₁ xs ys ⇓⟧ᶻ ≡ ⟦ xs ⇓⟧ ⊖ suc ⟦ ys ⇓⟧
sub₁-cong xs      0ᵇ      = dec±-cong xs
sub₁-cong 0ᵇ      (1ᵇ ys) = 2ᵇ∓-cong (dec± ys)    ∙ cong 2ᵇ∓ⁿ_ (dec±-cong ys)    ∙ 2ᵇ∓-⊖ 1 ⟦ ys ⇓⟧
sub₁-cong 0ᵇ      (2ᵇ ys) = 1ᵇ∓-cong (dec± ys)    ∙ cong 1ᵇ∓ⁿ_ (dec±-cong ys)    ∙ 1ᵇ∓-⊖ 1 ⟦ ys ⇓⟧
sub₁-cong (1ᵇ xs) (1ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys) ∙ cong 1ᵇⁿ_  (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₁-cong (2ᵇ xs) (2ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys) ∙ cong 1ᵇⁿ_  (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)
sub₁-cong (2ᵇ xs) (1ᵇ ys) = 2ᵇ±-cong (sub₁ xs ys) ∙ cong 2ᵇⁿ_  (sub₁-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub₁-cong (1ᵇ xs) (2ᵇ ys) = 2ᵇ∓-cong (sub₁ ys xs) ∙ cong 2ᵇ∓ⁿ_ (sub₁-cong ys xs) ∙ 2ᵇ∓-⊖ (suc ⟦ xs ⇓⟧) ⟦ ys ⇓⟧

sub-cong : ∀ xs ys → ⟦ sub xs ys ⇓⟧ᶻ ≡ ⟦ xs ⇓⟧ ⊖ ⟦ ys ⇓⟧
sub-cong _       0ᵇ      = refl
sub-cong 0ᵇ      (1ᵇ ys) = 1ᵇ±-cong (sub₁ 0ᵇ ys)  ∙ cong 1ᵇⁿ_  (sub₁-cong 0ᵇ ys) ∙ 1ᵇ-⊖ 0 (suc ⟦ ys ⇓⟧)
sub-cong 0ᵇ      (2ᵇ ys) = 2ᵇ∓-cong (dec± ys)     ∙ cong 2ᵇ∓ⁿ_ (dec±-cong ys)    ∙ 2ᵇ∓-⊖ 1 ⟦ ys ⇓⟧
sub-cong (1ᵇ xs) (1ᵇ ys) = 2ᵇ±-cong (sub₁ xs ys)  ∙ cong 2ᵇⁿ_  (sub₁-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (2ᵇ xs) (2ᵇ ys) = 2ᵇ±-cong (sub₁ xs ys)  ∙ cong 2ᵇⁿ_  (sub₁-cong xs ys) ∙ 2ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (2ᵇ xs) (1ᵇ ys) = 1ᵇ±-cong (sub  xs ys)  ∙ cong 1ᵇⁿ_  (sub-cong  xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
sub-cong (1ᵇ xs) (2ᵇ ys) = 1ᵇ±-cong (sub₁ xs ys)  ∙ cong 1ᵇⁿ_  (sub₁-cong xs ys) ∙ 1ᵇ-⊖ ⟦ xs ⇓⟧ (suc ⟦ ys ⇓⟧)

-‿pos : ∀ xs ys → posⁿ ⟦ xs - ys ⇓⟧ᶻ ≡ ⟦ xs ⇓⟧ ℕ.- ⟦ ys ⇓⟧
-‿pos xs ys = cong posⁿ (sub-cong xs ys) ∙ ⊖-pos ⟦ xs ⇓⟧ ⟦ ys ⇓⟧

-‿mag : ∀ xs ys → magⁿ ⟦ xs - ys ⇓⟧ᶻ ≡ ⟦ ys ⇓⟧ ℕ.- ⟦ xs ⇓⟧
-‿mag xs ys = cong magⁿ (sub-cong xs ys) ∙ ⊖-mag ⟦ xs ⇓⟧ ⟦ ys ⇓⟧
